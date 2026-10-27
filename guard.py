# -*- coding: utf-8 -*-
"""
guard.py - protection plan, Step 1 (base) + Step 2 (VIP key).

Step 1
  * client_ip()   real visitor IP, using what the ipcheck test proved for blitz.cloud:
                  X-Real-IP, CF-Connecting-IP and X-Forwarded-For (first entry) are set by
                  the proxy and cannot be faked.  True-Client-IP is NEVER read (a fake
                  one reaches the app untouched).  The socket peer (10.x.x.x) is only a
                  last resort.
  * Window        thread-safe counters with a time window (TTL), for the later rate rules.
  * mode()        PROTECT = off | log | on   (env var = starting value; the admin panel can
                  change it and the choice is kept in the DB).
                  off = guard does nothing.  log = dry-run: only writes what it WOULD block.
                  on  = really blocks.
  * violation()   the one place every later rule calls; it applies the mode.

Step 2
  * VIP keys      made in the admin panel, only a hash is stored.  A request with a valid key
                  (header X-VIP-Key, or ?vk=... for <video>) gets NO limit: is_vip() is True.

Step 3
  * Sessions      a link made for the website player is bound to ONE session: the visitor's IP,
                  a random session id and an expiry (max SESS_MAX, 60 min).  The player pings
                  /api/hb every 30 s (a heartbeat); silence for SESS_IDLE (90 s) = session over.
                  Another IP, an expired or a wrong-purpose link = violation (stream and
                  download links are different).  The player then quietly asks for a fresh link,
                  so a real user never sees an error.  Memory only and restart-safe: a valid
                  signed link whose record is gone (restart) simply starts a new record.
                  Stremio / VIP links stay unbound (no session) - rules for them come later.

Step 4
  * Download rule  a download link is a separate "d" link, made only for a signed-in user (ticket
                  /api/dltok).  At most DL_MAX (3) downloads at the same time per account
                  (anonymous in dry-run: per IP).  WN (movie) streams go through our own /wn
                  proxy once PROTECT=on (env WN_PROXY=0|1 overrides), so the same IP / session
                  rules apply to them.

Step 5
  * Guest rule    a visitor who is not signed in may START at most GUEST_MAX (5) different videos per
                  IP (and per device id) in GUEST_HOURS (24 h).  The 6th = sign-in is asked.
  * Concurrent    at most CONC_MAX (2) live streams from one IP.  The same device opening a new video
                  replaces its own old one (episode change / renew), so it counts once.
  * Detail first  a video link is only given if the anime's page (/meta) was opened before from this
                  IP or device (open_mark / was_opened).  The website quietly opens it and retries.
  * Rate limits   rate(): /api/shows per minute, /meta (burst + per minute), Stremio /stream and
                  /manifest.json per minute.
  * Device id     header X-Device (random id the browser keeps).  Soft check: easy to change.

Step 6
  * Honeypot      a few fake anime (decoys()) ride in the site's list marked z:1; the website hides
                  them.  Whoever asks for one (detail / video / skip / poster) is a bot: trap().
  * Bot score     track() counts what each IP / device does (video asked, skip, heartbeat, meta ...);
                  bot_score() turns it into 0-100 % with the reasons.
  * Bans          ban() / unban() (admin panel), kept in the DB (table bot_bans).  Auto bans (decoy
                  or score >= BAN_SCORE) only when PROTECT=on and they end after BAN_HOURS (24 h).
                  A banned visitor gets quiet empty answers (no error to learn from), see addon.py.

Step 7
  * Captcha asked  captcha_needed() is the one place that says "this visitor must play the game
                  captcha now" (PROTECT=on) or only logs it (dry-run).  score_of() gives the bot %
                  of an IP / device.  The game itself is in captcha.py.  Every ask counts as one small
                  limit-break in the bot score (+5, at most 25 - so a bot that ignores the captcha and
                  keeps asking ends in the ban, while a human who is asked once and passes loses nothing).

Nothing in here may ever break the site: every public function swallows its own errors.
"""
import collections
import hashlib
import ipaddress
import os
import secrets
import threading
import time

MODES = ("off", "log", "on")


def _clean_mode(v, default):
    v = str(v or "").strip().lower()
    return v if v in MODES else default


_ENV_MODE = _clean_mode(os.environ.get("PROTECT"), "log")
_mode_saved = None                         # set from the DB / admin panel, beats the env var
# Trust the proxy headers only when we really sit behind the platform proxy.
TRUST_PROXY = os.environ.get("GUARD_TRUST_PROXY", "1") != "0"
VIP_MAX = 50


def mode():
    return _mode_saved or _ENV_MODE


def _log(lvl, msg, key=None, ttl=60):
    try:
        import applog
        if key:
            applog.log_once(key, ttl, lvl, "guard", msg)
        else:
            applog.log(lvl, "guard", msg)
    except Exception:
        print("[guard] " + msg, flush=True)


# ------------------------------------------------------------------ IP ----
def _norm_ip(text):
    """'1.2.3.4' / '::ffff:1.2.3.4' / ' 2001:db8::1 ' -> clean string, or None."""
    try:
        a = ipaddress.ip_address(str(text or "").strip())
        if a.version == 6 and a.ipv4_mapped:
            a = a.ipv4_mapped
        return str(a)
    except Exception:
        return None


def client_ip(headers, peer=""):
    """Real visitor IP (see module doc for why this order)."""
    try:
        if TRUST_PROXY:
            for h in ("X-Real-IP", "CF-Connecting-IP"):
                v = _norm_ip(headers.get(h))
                if v:
                    return v
            v = _norm_ip((headers.get("X-Forwarded-For") or "").split(",")[0])
            if v:
                return v
        return _norm_ip(peer) or str(peer or "0.0.0.0")
    except Exception:
        return str(peer or "0.0.0.0")


def ip_key(ip):
    """What counters use as the 'person': IPv4 as is, IPv6 grouped by /64
    (one home gets a whole /64, so single addresses would be too easy to rotate)."""
    try:
        a = ipaddress.ip_address(ip)
        if a.version == 6:
            return "v6:" + str(ipaddress.ip_network(ip + "/64", strict=False).network_address)
    except Exception:
        pass
    return ip


# ------------------------------------------------------------- counters ----
class Window:
    """hit(key, window_s) -> how many hits this key has had in the last window_s seconds.
    Memory only (resets on restart; bans/limits that must survive go to the DB later)."""

    def __init__(self, maxkeys=30000):
        self._d = {}                       # key -> [window, deque(timestamps)]
        self._lock = threading.Lock()
        self._max = maxkeys
        self._clean_at = 0.0

    def _prune(self, now):
        if now - self._clean_at < 60 and len(self._d) < self._max:
            return
        self._clean_at = now
        for k in [k for k, (w, dq) in self._d.items() if not dq or dq[-1] < now - w]:
            del self._d[k]
        if len(self._d) >= self._max:      # still too many: drop the oldest half
            for k in sorted(self._d, key=lambda k: self._d[k][1][-1] if self._d[k][1] else 0)[: self._max // 2]:
                del self._d[k]

    def hit(self, key, window, now=None):
        now = now or time.time()
        with self._lock:
            self._prune(now)
            ent = self._d.get(key)
            if ent is None:
                ent = self._d[key] = [window, collections.deque()]
            ent[0] = max(ent[0], window)
            dq = ent[1]
            dq.append(now)
            lim = now - window
            while dq and dq[0] < lim:
                dq.popleft()
            return len(dq)

    def count(self, key, window, now=None):
        now = now or time.time()
        with self._lock:
            ent = self._d.get(key)
            if not ent:
                return 0
            lim = now - window
            return sum(1 for t in ent[1] if t >= lim)

    def keys(self, prefix="", window=60, now=None):
        now = now or time.time()
        with self._lock:
            return [k for k, (w, dq) in self._d.items()
                    if k.startswith(prefix) and dq and dq[-1] >= now - window]


REQ = Window()                              # every request, per IP (used by later rules)
_viol = collections.Counter()               # rule name -> how many times it fired
_viol_lock = threading.Lock()


def note(ip):
    """Count one request from this IP."""
    try:
        REQ.hit("ip:" + ip_key(ip), 60)
    except Exception:
        pass


def violation(rule, ip, detail="", dev=""):
    """Every later rule calls this when a limit is broken.
    Returns True only if the request must really be blocked (mode 'on')."""
    try:
        m = mode()
        if m == "off":
            return False
        with _viol_lock:
            _viol[rule] += 1
        _beh_add("viol", ip, dev)
        _log("warn", "%s ip=%s %s -> %s" % (rule, ip, detail, "BLOCK" if m == "on" else "log only (dry-run)"),
             key="viol:%s:%s" % (rule, ip_key(ip)), ttl=60)
        return m == "on"
    except Exception:
        return False


# ------------------------------------------------------------- VIP keys ----
_VIP_SCHEMA = "CREATE TABLE IF NOT EXISTS vip_keys(id TEXT PRIMARY KEY, name TEXT, hash TEXT, created REAL)"
_vip = {}                                   # sha256(key) -> {"id","name","created"}   (read-only dict, replaced as a whole)
_vip_used = {}                              # id -> last time a request used it (memory only)
_vip_lock = threading.Lock()
_loaded = threading.Event()


def _hash(key):
    return hashlib.sha256(key.encode("utf-8")).hexdigest()


def _accounts():
    import accounts
    return accounts


def vip_key_from(headers, qs=None):
    k = (headers.get("X-VIP-Key") or "").strip()
    if not k and qs:
        try:
            k = (qs.get("vk") or [""])[0].strip()
        except Exception:
            k = ""
    return k[:200]


def is_vip(headers, qs=None, ip=""):
    """-> key name if the request carries a valid VIP key, else None. Memory lookup only (fast)."""
    try:
        k = vip_key_from(headers, qs)
        if not k:
            return None
        rec = _vip.get(_hash(k))
        if rec:
            _vip_used[rec["id"]] = time.time()
            return rec["name"]
        _log("warn", "wrong VIP key from %s" % ip, key="vipbad:" + ip_key(ip or "?"), ttl=120)
    except Exception:
        pass
    return None


def _reload():
    """Read keys + saved mode from the DB. Raises while the DB is down."""
    global _vip, _mode_saved
    a = _accounts()
    a.q(_VIP_SCHEMA)                        # a 'Reload from Telegram' may bring back an old DB without it
    rows = a.q("SELECT id, name, hash, created FROM vip_keys")
    new = {}
    for r in rows:
        new[r[2]] = {"id": r[0], "name": r[1], "created": r[3]}
    with _vip_lock:
        _vip = new
    m = a.kv_get("guard_mode")
    if m in MODES:
        _mode_saved = m
    sd = a.kv_get("hp_seed")                 # seed of the fake anime: kept, so they do not change at every restart
    if not sd:
        sd = os.environ.get("HP_SEED") or secrets.token_hex(8)
        a.kv_set("hp_seed", sd)
    _set_seed(sd)
    a.q(_BAN_SCHEMA)
    now = time.time()
    newb = {}
    for r in a.q("SELECT key, why, created, until, auto FROM bot_bans"):
        if r[3] and r[3] <= now:
            continue                         # an old automatic ban that already ended
        newb[r[0]] = {"why": r[1] or "", "created": r[2] or 0, "until": r[3] or 0, "auto": bool(r[4])}
    global _bans
    with _ban_lock:
        _bans = newb
    _loaded.set()


def _loop():
    shown = False
    while True:
        try:
            _reload()
            shown = False
            time.sleep(300)
        except Exception as e:
            if not shown:
                print("[guard] DB not ready yet (%r), retrying" % (e,), flush=True)
                shown = True
            time.sleep(20)


def start():
    """Call once at boot: loads VIP keys + saved mode in the background."""
    print("[guard] PROTECT mode=%s (env=%s) trust_proxy=%s" % (mode(), _ENV_MODE, TRUST_PROXY), flush=True)
    threading.Thread(target=_loop, daemon=True, name="guard-load").start()


def vip_list():
    with _vip_lock:
        recs = list(_vip.values())
    recs.sort(key=lambda r: r.get("created") or 0)
    return [{"id": r["id"], "name": r["name"], "created": r["created"],
             "last_used": _vip_used.get(r["id"])} for r in recs]


def vip_new(name):
    """Make a key. The real key is returned ONCE; only its hash is stored."""
    global _vip
    name = " ".join(str(name or "").split())[:40]
    if not name:
        raise ValueError("Naam likho (jaise: TV app).")
    if len(_vip) >= VIP_MAX:
        raise ValueError("Bahut zyada keys (max %d). Purani delete karo." % VIP_MAX)
    key = "vk_" + secrets.token_urlsafe(24)
    kid = secrets.token_hex(4)
    now = time.time()
    a = _accounts()
    a.q(_VIP_SCHEMA)
    a.q("INSERT INTO vip_keys(id, name, hash, created) VALUES(?,?,?,?)", (kid, name, _hash(key), now))
    with _vip_lock:
        new = dict(_vip)
        new[_hash(key)] = {"id": kid, "name": name, "created": now}
        _vip = new
    _log("info", "VIP key created: %s (%s)" % (name, kid))
    return {"id": kid, "name": name, "key": key}


def vip_del(kid):
    global _vip
    kid = str(kid or "").strip()[:20]
    a = _accounts()
    a.q("DELETE FROM vip_keys WHERE id=?", (kid,))
    with _vip_lock:
        new = {h: r for h, r in _vip.items() if r["id"] != kid}
        gone = len(new) != len(_vip)
        _vip = new
    _vip_used.pop(kid, None)
    if gone:
        _log("info", "VIP key deleted: " + kid)
    return gone


# ------------------------------------------------------------- sessions ----
def _env_num(key, default):
    try:
        return max(1, int(float(os.environ.get(key, default))))
    except Exception:
        return default


SESS_MAX = _env_num("SESS_MAX_MIN", 60) * 60     # a link lives at most this long (seconds)
SESS_IDLE = _env_num("SESS_IDLE", 90)             # no heartbeat for this long = session over
SESS_RENEW_LEFT = 120                             # the player asks for a fresh link this early
DL_LIFE = 600                                     # a download link lives 10 min
_sess = {}                                        # sid -> {"ipk", "start", "last", "exp", "dev"}
_ip_sids = {}                                     # ipk -> set of sids (so "live streams of this IP" is quick)
_sess_lock = threading.Lock()
_sess_clean_at = 0.0


def _sess_prune(now):
    global _sess_clean_at
    if now - _sess_clean_at < 60 and len(_sess) < 20000:
        return
    _sess_clean_at = now
    for k in [k for k, r in _sess.items() if r["exp"] < now - 300 or r["last"] < now - 3600]:
        del _sess[k]
    if len(_sess) >= 20000:                       # still too many: drop the oldest half
        for k in sorted(_sess, key=lambda k: _sess[k]["last"])[:10000]:
            del _sess[k]
    idx = {}                                      # rebuild the per-IP index from what is left
    for k, r in _sess.items():
        idx.setdefault(r["ipk"], set()).add(k)
    _ip_sids.clear()
    _ip_sids.update(idx)


def sess_open(ip, now=None, dev=""):
    """New session for the website player.  Returns {"sid","ipk","exp"}, or None when the guard
    is off (then plain unbound links are used, exactly like before).  dev = the browser's device id."""
    try:
        if mode() == "off":
            return None
        now = now or time.time()
        sid = secrets.token_urlsafe(9)
        rec = {"ipk": ip_key(ip), "start": now, "last": now, "exp": now + SESS_MAX, "dev": dev or ""}
        with _sess_lock:
            _sess_prune(now)
            _sess[sid] = rec
            _ip_sids.setdefault(rec["ipk"], set()).add(sid)
        return {"sid": sid, "ipk": rec["ipk"], "exp": rec["exp"]}
    except Exception:
        return None


def sess_end(sid):
    """Step 9 ("one token = one stream, latest wins"): stop an older session.  Its links answer
    403 renew (why = ended) from now on; the heartbeat cannot revive it.  Never raises."""
    try:
        with _sess_lock:
            rec = _sess.get(str(sid or ""))
            if rec is not None:
                rec["ended"] = True
                return True
    except Exception:
        pass
    return False


def sess_check(p, ip, want, beat=False, now=None):
    """Is this request allowed under its session?  p = parsed link
    {"kind","sid","ipk","exp"}.  Returns "" if fine, else why not: kind / expired / ip / idle.
    beat=True is the heartbeat itself: it also marks the session alive (and revives an idle one).
    Never raises (a bug here must not stop video)."""
    try:
        now = now or time.time()
        kind = p.get("kind")
        if kind != want and not (beat and kind in ("s", "w")):   # heartbeat comes from a stream (s) or WN (w) link
            return "kind"
        if now > p["exp"]:
            return "expired"
        if ip_key(ip) != p["ipk"]:
            return "ip"
        if want == "d":                           # download link: checked by kind, expiry and IP only
            return ""
        sid = p["sid"]
        with _sess_lock:
            rec = _sess.get(sid)
            if rec is None:                       # restart (or pruned): signed link is valid, start over
                _sess[sid] = {"ipk": p["ipk"], "start": now, "last": now, "exp": p["exp"]}
                return ""
            if rec.get("ended"):                  # Step 9: a newer stream of the same TV pass took over (latest wins)
                return "ended"
            if want in ("s", "w") and not beat and now - rec["last"] > SESS_IDLE:
                return "idle"
            if beat:
                rec["last"] = now
        return ""
    except Exception:
        return ""


# ------------------------------------------------------------ downloads ----
DL_MAX = _env_num("DL_MAX", 3)                    # downloads at the same time, per account
_dl = {}                                          # key -> running downloads
_dl_lock = threading.Lock()


def dl_begin(key):
    """A download starts.  Returns how many are now running for this key (including this one)."""
    with _dl_lock:
        _dl[key] = _dl.get(key, 0) + 1
        return _dl[key]


def dl_end(key):
    with _dl_lock:
        n = _dl.get(key, 0) - 1
        if n > 0:
            _dl[key] = n
        else:
            _dl.pop(key, None)


def dl_total():
    with _dl_lock:
        return sum(_dl.values())


def sess_count(now=None):
    now = now or time.time()
    with _sess_lock:
        return sum(1 for r in _sess.values() if r["exp"] > now and now - r["last"] <= SESS_IDLE)



# ============================================================ Step 5 ====
# Guest limit, live-stream limit, "open the page first", request rate limits.
GUEST_MAX = _env_num("GUEST_MAX", 5)              # different videos a not-signed-in visitor may start ...
GUEST_HOURS = _env_num("GUEST_HOURS", 24)         # ... in this many hours (per IP and per device id)
CONC_MAX = _env_num("CONC_MAX", 2)                # live streams at the same time from one IP
OPEN_HOURS = _env_num("OPEN_HOURS", 6)            # an opened anime page is remembered this long
META_MAX = _env_num("META_MAX", 3)                # /meta: at most this many ...
META_WIN = _env_num("META_WIN", 3)                # ... in this many seconds (= about 1 per second)
META_MIN_MAX = _env_num("META_MIN_MAX", 40)       # /meta per minute, per IP
SHOWS_IP_MIN = _env_num("SHOWS_IP_MIN", 20)       # /api/shows per minute, per IP
SHOWS_DEV_MIN = _env_num("SHOWS_DEV_MIN", 10)     # /api/shows per minute, per device id
STREAM_MIN = _env_num("STREAM_MIN", 20)           # Stremio /stream per minute, per IP
MANIFEST_MIN = _env_num("MANIFEST_MIN", 10)       # Stremio /manifest.json per minute, per IP

_DEV_RE = None


def device_id(headers):
    """The browser's random id (header X-Device), or "" when missing / malformed."""
    global _DEV_RE
    try:
        if _DEV_RE is None:
            import re
            _DEV_RE = re.compile(r"^[A-Za-z0-9_-]{8,40}$")
        v = (headers.get("X-Device") or "").strip()
        return v if _DEV_RE.match(v) else ""
    except Exception:
        return ""


RATE = Window()


def rate(name, ip, dev, win, ip_max, dev_max=0, detail=""):
    """Count one request.  True = it must be refused (limit broken AND mode is 'on')."""
    try:
        if mode() == "off":
            return False
        bad = RATE.hit("%s:i:%s" % (name, ip_key(ip)), win) > ip_max
        if dev and dev_max:
            bad = (RATE.hit("%s:d:%s" % (name, dev), win) > dev_max) or bad
        if bad:
            return violation("rate_" + name, ip, "%s more than %d in %ds" % (detail or name, ip_max, win), dev=dev)
    except Exception:
        pass
    return False


# ---- "open the anime page first"
_opened = {}                                      # "i:<ipk>|slug" / "d:<dev>|slug" -> time
_open_lock = threading.Lock()


def open_mark(ip, dev, slug, now=None):
    """The anime's page (/meta) was opened by this IP / device."""
    try:
        now = now or time.time()
        with _open_lock:
            if len(_opened) > 60000:
                lim = now - OPEN_HOURS * 3600
                for k in [k for k, t in _opened.items() if t < lim]:
                    del _opened[k]
                if len(_opened) > 60000:
                    _opened.clear()
            _opened["i:%s|%s" % (ip_key(ip), slug)] = now
            if dev:
                _opened["d:%s|%s" % (dev, slug)] = now
    except Exception:
        pass


def was_opened(ip, dev, slug, now=None):
    try:
        now = now or time.time()
        lim = now - OPEN_HOURS * 3600
        with _open_lock:
            for k in ("i:%s|%s" % (ip_key(ip), slug), ("d:%s|%s" % (dev, slug)) if dev else None):
                if k and _opened.get(k, 0) >= lim:
                    return True
        return False
    except Exception:
        return True                                # a bug here must never stop a video


# ---- guest: max GUEST_MAX different videos
_guest = {}                                       # "i:<ipk>" / "d:<dev>" -> {video: first time}
_guest_lock = threading.Lock()


def guest_start(ip, dev, video, now=None):
    """A visitor who is NOT signed in starts `video`.  True = refuse (limit broken AND mode 'on').
    Watching the same video again (seek, retry, renew) never counts twice."""
    try:
        if mode() == "off":
            return False
        now = now or time.time()
        lim = now - GUEST_HOURS * 3600
        keys = ["i:" + ip_key(ip)] + (["d:" + dev] if dev else [])
        over = []
        with _guest_lock:
            if len(_guest) > 40000:
                for k in [k for k, d in _guest.items() if not d or max(d.values()) < lim]:
                    del _guest[k]
                if len(_guest) > 40000:
                    _guest.clear()
            for k in keys:
                d = _guest.setdefault(k, {})
                for v in [v for v, t in d.items() if t < lim]:
                    del d[v]
                if video not in d and len(d) >= GUEST_MAX:
                    over.append(k)
        if over and violation("guest_limit", ip, "%s already has %d videos (%s)" % (over[0], GUEST_MAX, video), dev=dev):
            return True                            # refused: the video is NOT counted
        with _guest_lock:
            for k in keys:
                _guest.setdefault(k, {}).setdefault(video, now)
        return False
    except Exception:
        return False


def guest_count(ip, dev="", now=None):
    now = now or time.time()
    lim = now - GUEST_HOURS * 3600
    with _guest_lock:
        out = 0
        for k in ["i:" + ip_key(ip)] + (["d:" + dev] if dev else []):
            out = max(out, sum(1 for t in _guest.get(k, {}).values() if t >= lim))
        return out


# ---- live streams from one IP
def live_streams(ip, now=None):
    """Set of 'who' that have a live stream on this IP.  One device = one entry however many
    links it opened (episode change, renew); a session without device id counts alone."""
    now = now or time.time()
    ipk = ip_key(ip)
    live = set()
    with _sess_lock:
        for sid in list(_ip_sids.get(ipk, ())):
            r = _sess.get(sid)
            if r and r["exp"] > now and now - r["last"] <= SESS_IDLE:
                live.add(r.get("dev") or sid)
    return live


def conc_check(ip, dev="", now=None):
    """The visitor wants one more stream.  True = refuse (CONC_MAX live already AND mode 'on')."""
    try:
        if mode() == "off":
            return False
        live = live_streams(ip, now)
        if (dev and dev in live) or len(live) < CONC_MAX:
            return False
        return violation("concurrent", ip, "%d live streams already (max %d)" % (len(live), CONC_MAX), dev=dev)
    except Exception:
        return False


# ============================================================ Step 6 ====
# Honeypot (fake anime), bot score, bans.
BAN_SCORE = _env_num("BAN_SCORE", 90)             # score at which an IP is banned automatically (mode 'on')
CAPTCHA_SCORE_USER = _env_num("CAPTCHA_SCORE_USER", 85)   # a SIGNED-IN user gets the game only from this bot score
FLAG_SCORE = _env_num("FLAG_SCORE", 60)           # score from which the admin list calls it "shak"
BAN_HOURS = _env_num("BAN_HOURS", 24)             # automatic bans end after this (manual bans: never, unless you set hours)
BEH_SECS = 3600                                   # the score looks at the last hour (counters restart after it)
DECOY_N = _env_num("DECOY_N", 6)

_BEH_KINDS = ("watch", "skip", "meta", "hb", "shows", "stream", "prog")
BEH = {}                                          # "ip:<ipk>" / "dev:<id>" -> counters
_beh_lock = threading.Lock()


def _beh_rec(key, now):
    r = BEH.get(key)
    if r is None or now - r["t0"] > BEH_SECS:
        r = BEH[key] = {"t0": now, "last": now, "n": dict.fromkeys(_BEH_KINDS, 0),
                        "viol": 0, "decoy": 0, "nodev": 0, "fast": 0, "vid": "", "vid_t": 0.0, "with": set()}
    return r


def _beh_keys(ip, dev):
    ks = ["ip:" + ip_key(ip)] if ip else []
    if dev:
        ks.append("dev:" + dev)
    return ks


def _beh_prune(now):
    if len(BEH) < 20000:
        return
    for k in [k for k, r in BEH.items() if now - r["last"] > BEH_SECS]:
        del BEH[k]
    if len(BEH) >= 20000:
        for k in sorted(BEH, key=lambda k: BEH[k]["last"])[:10000]:
            del BEH[k]


def _beh_add(what, ip, dev="", now=None):
    """what = 'viol' | 'decoy' (counters that are not a request kind)."""
    try:
        now = now or time.time()
        with _beh_lock:
            for k in _beh_keys(ip, dev):
                r = _beh_rec(k, now)
                r[what] += 1
                r["last"] = now
    except Exception:
        pass


def track(kind, ip, dev="", now=None):
    """Count one thing this visitor did (kind in _BEH_KINDS)."""
    try:
        if mode() == "off":
            return
        now = now or time.time()
        ik, dk = "ip:" + ip_key(ip), ("dev:" + dev) if dev else ""
        with _beh_lock:
            _beh_prune(now)
            for k in (ik, dk):
                if not k:
                    continue
                r = _beh_rec(k, now)
                r["n"][kind] = r["n"].get(kind, 0) + 1
                r["last"] = now
                if kind == "watch" and not dev and k == ik:
                    r["nodev"] += 1
                if k == ik and dev and len(r["with"]) < 5:
                    r["with"].add("dev:" + dev)
                if k == dk and len(r["with"]) < 5:
                    r["with"].add("ip:" + ik[3:])
    except Exception:
        pass


FAST_SECS = _env_num("FAST_SECS", 30)             # a different video asked for sooner than this after the last one = "fast switch"


def watch_switch(video, ip, dev="", now=None):
    """The visitor asked for `video`.  If it is a DIFFERENT video than his last one and he asked for it
    before FAST_SECS seconds went by (a human watches an episode longer; a bot hops episode to episode),
    one fast switch is counted.  The same video again (renew, seek, retry) is never counted."""
    try:
        if mode() == "off":
            return
        now = now or time.time()
        video = str(video)
        with _beh_lock:
            for k in _beh_keys(ip, dev):
                r = _beh_rec(k, now)
                if r["vid"] and r["vid"] != video and now - r["vid_t"] < FAST_SECS:
                    r["fast"] += 1
                if r["vid"] != video:
                    r["vid"], r["vid_t"] = video, now
                r["last"] = now
    except Exception:
        pass


def bot_score(rec):
    """-> (0..100, [reasons]).  A real visitor asks for a video AND for skip-intro, heartbeats,
    the anime's page ...; a bot asks only for the video, in bulk, and runs into the limits."""
    n, w, why, pts = rec["n"], rec["n"]["watch"], [], 0
    if rec["decoy"]:
        return 100, ["nakli anime maanga (jaal)"]
    if w >= 3:
        miss = 1 - min(1.0, n["skip"] / w)
        if miss > 0.3:
            p = round(30 * miss)
            pts += p; why.append("video maanga par skip-intro nahi (%d video, %d skip) +%d" % (w, n["skip"], p))
    if w >= 4:
        miss = 1 - min(1.0, n["hb"] / w)
        if miss > 0.5:
            p = round(15 * miss)
            pts += p; why.append("heartbeat bahut kam (%d video, %d ping) +%d" % (w, n["hb"], p))
    if w >= 3 and rec["nodev"] / w > 0.5:
        pts += 15; why.append("device id ke bina video maanga +15")
    if w > 15:
        p = min(20, (w - 15) * 2)
        pts += p; why.append("ek ghante me %d video +%d" % (w, p))
    if rec.get("fast", 0) >= 3:
        p = min(60, 15 * rec["fast"])
        pts += p; why.append("%d baar %d sec se pehle naya episode maanga +%d" % (rec["fast"], FAST_SECS, p))
    if rec["viol"]:
        p = min(25, 5 * rec["viol"])
        pts += p; why.append("%d baar limit todi +%d" % (rec["viol"], p))
    return min(100, pts), why


# ---- decoys (fake anime)
_hp_seed = ""
_decoy_slugs = set()                              # the current seed's slugs
_decoy_all = set()                                # every slug this process ever used (a list built before the DB seed arrived)
_decoy_cache = []
_decoy_lock = threading.Lock()
_ADJ = ["Kuroi", "Akai", "Shiroi", "Tsuki", "Hoshi", "Yami", "Kaze", "Ame", "Yume", "Sora", "Hikari", "Kage", "Mizu", "Kitsune", "Ryuu"]
_NOUN = ["Kishi", "Tatakai", "Monogatari", "Senshi", "Chikai", "Gakuen", "Densetsu", "Saga", "Requiem", "Tenshi", "Ookami", "Shinigami"]
_TAIL = ["", "", " Season 2", " (Hindi Dub)", " The Movie"]


def _set_seed(seed):
    """(Re)build the list of fake anime names from a seed."""
    global _hp_seed, _decoy_slugs, _decoy_cache
    import random
    import re
    seed = str(seed or "")
    if not seed or seed == _hp_seed:
        return
    rng = random.Random(seed)
    out, seen = [], set()
    while len(out) < max(1, DECOY_N) and len(seen) < 500:
        name = "%s %s no %s%s" % (rng.choice(_ADJ), rng.choice(_ADJ), rng.choice(_NOUN), rng.choice(_TAIL))
        slug = re.sub(r"[^a-z0-9]+", "_", name.lower()).strip("_")
        if slug in seen:
            continue
        seen.add(slug)
        out.append((slug, name))
    with _decoy_lock:
        _hp_seed = seed
        _decoy_cache = out
        _decoy_slugs = {s for s, _ in out}
        _decoy_all.update(_decoy_slugs)


def decoy_items(real_items):
    """Fake list entries shaped like the real ones (copied from random real entries), marked z:1.
    The website hides z:1; a script that reads the list blindly will not."""
    try:
        import random
        if not _decoy_cache:
            _set_seed(os.environ.get("HP_SEED") or secrets.token_hex(8))
        pool = [r for r in real_items if not r.get("movie")] or list(real_items)
        if not pool:
            return []
        rng = random.Random(_hp_seed)
        out = []
        for i, (slug, name) in enumerate(_decoy_cache):
            t = dict(rng.choice(pool))
            t.update(slug=slug, name=name, poster="/img/s/" + slug, movie=False, kind="anime",
                     ord=900000 + i, le=[1, 12], n=12, upd=0, add=0, z=1)
            t.pop("en", None)
            out.append(t)
        return out
    except Exception:
        return []


def is_decoy(slug):
    try:
        return slug in _decoy_all
    except Exception:
        return False


# ---- bans
_BAN_SCHEMA = "CREATE TABLE IF NOT EXISTS bot_bans(key TEXT PRIMARY KEY, why TEXT, created REAL, until REAL, auto INTEGER)"
_bans = {}                                        # "ip:<ipk>" / "dev:<id>" -> {"why","created","until","auto"}  (replaced as a whole)
_ban_lock = threading.Lock()


def ban_key(text):
    """'1.2.3.4' / 'ip:1.2.3.4' / 'dev:abcd...' / a bare device id -> canonical key, else ValueError."""
    t = str(text or "").strip()
    if t.startswith("dev:"):
        t = t[4:]
        if not _dev_ok(t):
            raise ValueError("Device id galat hai.")
        return "dev:" + t
    if t.startswith("ip:"):
        t = t[3:]
    n = _norm_ip(t)
    if n:
        return "ip:" + ip_key(n)
    if t.startswith("v6:"):
        return "ip:" + t
    if _dev_ok(t):
        return "dev:" + t
    raise ValueError("IP ya device id likho.")


def _dev_ok(t):
    import re
    return bool(re.match(r"^[A-Za-z0-9_-]{8,40}$", t or ""))


def is_banned(ip, dev="", now=None):
    """-> why (text) if this IP / device is banned, else ''.  Memory lookup only."""
    try:
        if not _bans:
            return ""
        now = now or time.time()
        for k in _beh_keys(ip, dev):
            b = _bans.get(k)
            if b and (not b["until"] or b["until"] > now):
                return b["why"] or "ban"
    except Exception:
        pass
    return ""


def _ban_save(key, rec):
    try:
        a = _accounts()
        a.q(_BAN_SCHEMA)
        a.q("INSERT OR REPLACE INTO bot_bans(key, why, created, until, auto) VALUES(?,?,?,?,?)",
            (key, rec["why"], rec["created"], rec["until"], 1 if rec["auto"] else 0))
    except Exception as e:
        _log("warn", "ban %s not saved to DB (%r) - it works until restart" % (key, e), key="bansave", ttl=300)


def ban(key, why="", hours=0, auto=False, wait_db=True):
    """Ban a key (see ban_key).  hours=0 -> until unbanned.  wait_db=False saves in the background."""
    global _bans
    key = ban_key(key)
    now = time.time()
    rec = {"why": str(why or "")[:120], "created": now, "until": (now + hours * 3600) if hours else 0, "auto": bool(auto)}
    with _ban_lock:
        new = dict(_bans)
        new[key] = rec
        _bans = new
    _log("warn" if auto else "info", "BAN %s (%s)%s" % (key, rec["why"], " auto" if auto else ""))
    if wait_db:
        a = _accounts()
        a.q(_BAN_SCHEMA)
        a.q("INSERT OR REPLACE INTO bot_bans(key, why, created, until, auto) VALUES(?,?,?,?,?)",
            (key, rec["why"], rec["created"], rec["until"], 1 if rec["auto"] else 0))
    else:
        threading.Thread(target=_ban_save, args=(key, rec), daemon=True, name="ban-save").start()
    return key


def unban(key):
    global _bans
    key = ban_key(key)
    a = _accounts()
    a.q(_BAN_SCHEMA)
    a.q("DELETE FROM bot_bans WHERE key=?", (key,))
    with _ban_lock:
        new = dict(_bans)
        gone = new.pop(key, None) is not None
        _bans = new
    if gone:
        _log("info", "UNBAN " + key)
    return gone


def ban_list():
    now = time.time()
    rows = [dict(key=k, why=b["why"], created=b["created"], until=b["until"], auto=b["auto"])
            for k, b in _bans.items() if not b["until"] or b["until"] > now]
    rows.sort(key=lambda r: -r["created"])
    return rows


def _auto_ban(ip, dev, why):
    for k in _beh_keys(ip, dev):
        try:
            ban(k, why, BAN_HOURS, auto=True, wait_db=False)
        except Exception:
            pass


def trap(ip, dev, slug, how):
    """Someone asked for a fake anime = a bot.  True = mode 'on' (the visitor is banned now)."""
    try:
        m = mode()
        if m == "off":
            return False
        with _viol_lock:
            _viol["honeypot"] += 1
        _beh_add("decoy", ip, dev)
        _log("warn", "HONEYPOT ip=%s dev=%s asked for fake anime %s (%s) -> %s"
             % (ip, dev or "-", slug, how, "BAN %dh" % BAN_HOURS if m == "on" else "log only (dry-run)"),
             key="trap:" + ip_key(ip), ttl=60)
        if m == "on":
            _auto_ban(ip, dev, "jaal: nakli anime %s" % slug)
            return True
    except Exception:
        pass
    return False


def check_score(ip, dev=""):
    """After a video request: has this IP reached BAN_SCORE?  True = banned now (mode 'on')."""
    try:
        m = mode()
        if m == "off":
            return False
        with _beh_lock:
            r = BEH.get("ip:" + ip_key(ip))
            sc, why = bot_score(r) if r else (0, [])
        if sc >= BAN_SCORE:
            _log("warn", "BOT %d%% ip=%s %s -> %s" % (sc, ip, "; ".join(why)[:200],
                                                     "BAN %dh" % BAN_HOURS if m == "on" else "log only (dry-run)"),
                 key="botscore:" + ip_key(ip), ttl=300)
            if m == "on":
                _auto_ban(ip, "", "bot score %d%%" % sc)
                return True
    except Exception:
        pass
    return False


def bot_list(limit=60):
    """The admin list: busiest / most suspicious visitors of the last hour."""
    now = time.time()
    out = []
    with _beh_lock:
        for k, r in BEH.items():
            if now - r["last"] > BEH_SECS or not (sum(r["n"].values()) or r["decoy"]):
                continue
            sc, why = bot_score(r)
            out.append({"key": k, "n": dict(r["n"]), "viol": r["viol"], "decoy": r["decoy"], "score": sc, "why": why,
                        "last": r["last"], "with": sorted(r["with"])})
    for o in out:
        b = _bans.get(o["key"])
        o["banned"] = bool(b and (not b["until"] or b["until"] > now))
    out.sort(key=lambda o: (-o["score"], -o["n"].get("watch", 0), -o["last"]))
    return out[:limit]


# ----------------------------------------------------------- admin view ----
def set_mode(m):
    global _mode_saved
    m = str(m or "").strip().lower()
    if m not in MODES:
        raise ValueError("mode off / log / on me se ek hona chahiye")
    _accounts().kv_set("guard_mode", m)
    _mode_saved = m
    _log("info", "PROTECT mode set to " + m)
    return m


def forgive(ip, dev=""):
    """The visitor just passed the game captcha: start his behaviour counters from zero."""
    try:
        with _beh_lock:
            for k in _beh_keys(ip, dev):
                BEH.pop(k, None)
    except Exception:
        pass


def score_of(ip, dev=""):
    """Bot % of this IP / device (the higher of the two) -> (0..100, [reasons])."""
    best = (0, [])
    try:
        with _beh_lock:
            recs = [BEH.get("ip:" + ip_key(ip))] + ([BEH.get("dev:" + dev)] if dev else [])
            for r in recs:
                if r:
                    s = bot_score(r)
                    if s[0] > best[0]:
                        best = s
    except Exception:
        pass
    return best


# ------------------------------------------------- sign-in watch + one stream per account (Step 10) ----
LOGIN_FAILS = _env_num("LOGIN_FAILS", 5)          # wrong passwords from one IP in 10 min -> captcha
LOGIN_TRIES = _env_num("LOGIN_TRIES", 20)         # sign-in tries from one IP in 10 min -> captcha
LOGIN_USER_FAILS = _env_num("LOGIN_USER_FAILS", 8)  # wrong passwords on ONE account (any IP) in 10 min -> captcha
LOGIN_WIN = 600
_acct = {}                                        # user id -> {"sid","video","dev","ipk","t"}
_acct_lock = threading.Lock()


def login_why(ip, username=""):
    """Is a sign-in captcha needed? -> text, or "" (normal).  Counts nothing."""
    try:
        ik, un = ip_key(ip), (username or "").lower()[:40]
        if RATE.count("lfail:i:" + ik, LOGIN_WIN) >= LOGIN_FAILS:
            return "%d galat password / %d min" % (LOGIN_FAILS, LOGIN_WIN // 60)
        if RATE.count("ltry:i:" + ik, LOGIN_WIN) >= LOGIN_TRIES:
            return "bahut sign-in koshish (%d / %d min)" % (LOGIN_TRIES, LOGIN_WIN // 60)
        if un and RATE.count("lfail:u:" + un, LOGIN_WIN) >= LOGIN_USER_FAILS:
            return "is account pe bahut galat password"
    except Exception:
        pass
    return ""


def login_hard(ip, username=""):
    """Even with a captcha pass there is a ceiling (3x).  True = refuse (only when PROTECT=on)."""
    try:
        ik, un = ip_key(ip), (username or "").lower()[:40]
        if (RATE.count("lfail:i:" + ik, LOGIN_WIN) >= LOGIN_FAILS * 3
                or (un and RATE.count("lfail:u:" + un, LOGIN_WIN) >= LOGIN_USER_FAILS * 3)):
            return violation("login_hard", ip, "sign-in galat password bahut baar (captcha ke baad bhi)")
    except Exception:
        pass
    return False


def login_note(ip, username, ok):
    """Count one sign-in try (and a failure)."""
    try:
        if mode() == "off":
            return
        ik, un = ip_key(ip), (username or "").lower()[:40]
        RATE.hit("ltry:i:" + ik, LOGIN_WIN)
        if not ok:
            RATE.hit("lfail:i:" + ik, LOGIN_WIN)
            if un:
                RATE.hit("lfail:u:" + un, LOGIN_WIN)
    except Exception:
        pass


def acct_stream(uid, sid, video="", dev="", ip=""):
    """One account = one stream, latest wins.  -> the OLDER session id to stop ("" = none).
    A renew / retry of the same video from the same browser never stops its own earlier link."""
    try:
        if not uid or not sid:
            return ""
        now, ik = time.time(), ip_key(ip)
        with _acct_lock:
            for k in [k for k, r in _acct.items() if now - r["t"] > SESS_MAX + 600]:
                del _acct[k]
            r = _acct.get(uid)
            old = ""
            if r and r["sid"] != sid and (r["video"] != str(video) or r["dev"] != (dev or "") or r["ipk"] != ik):
                old = r["sid"]
            _acct[uid] = {"sid": sid, "video": str(video), "dev": dev or "", "ipk": ik, "t": now}
            return old
    except Exception:
        return ""


# ---- strikes: a visitor who keeps looking like a bot gets the game 3 times, then his speed is cut for SLOW_MIN minutes
CAP_STRIKES = _env_num("CAP_STRIKES", 3)          # games asked for bot-like watching before the slow-down starts
SLOW_MIN = _env_num("SLOW_MIN", 30)               # the slow-down lasts this many minutes
SLOW_BPS = _env_num("SLOW_BPS", 12000)            # bytes/second while slowed (stream AND download)
STRIKE_WIN = 3600                                 # strikes older than this are forgotten
_strikes = {}                                     # "i:<ipk>" / "d:<dev>" -> [times]
_slow = {}                                        # same keys -> slowed until
_strike_lock = threading.Lock()


def _sk(ip, dev):
    return ["i:" + ip_key(ip)] + (["d:" + dev] if dev else [])


def is_slow(ip, dev="", now=None):
    """True = this visitor's streams and downloads must run at SLOW_BPS."""
    try:
        if not _slow or mode() != "on":
            return False
        now = now or time.time()
        with _strike_lock:
            return any(_slow.get(k, 0) > now for k in _sk(ip, dev))
    except Exception:
        return False


def bot_strike(ip, dev, why, ask=True, now=None):
    """Bot-like watching seen (many videos at once / bot score).  -> "ask" (play the game) | "slow" (3 games
    already used: speed cut for SLOW_MIN min, no more game) | "" (nothing: mode off/log or ask=False and still free)."""
    try:
        m = mode()
        if m == "off":
            return ""
        now = now or time.time()
        if m != "on":
            captcha_needed(ip, why, dev=dev)      # dry-run: only writes it down
            return ""
        keys = _sk(ip, dev)
        with _strike_lock:
            if any(_slow.get(k, 0) > now for k in keys):
                return "slow"
            n = 0
            for k in keys:
                lst = [t for t in _strikes.get(k, []) if t > now - STRIKE_WIN]
                _strikes[k] = lst
                n = max(n, len(lst))
            if n >= CAP_STRIKES:
                for k in keys:
                    _slow[k] = now + SLOW_MIN * 60
                    _strikes.pop(k, None)
                res = "slow"
            else:
                if ask:
                    for k in keys:
                        _strikes.setdefault(k, []).append(now)
                res = "ask" if ask else ""
            if len(_strikes) > 30000:
                _strikes.clear()
            if len(_slow) > 30000:
                for k in [k for k, t in _slow.items() if t < now]:
                    del _slow[k]
        if res == "slow":
            _log("warn", "SLOW ip=%s %s -> %d min slow-down" % (ip, why, SLOW_MIN), key="slow:" + ip_key(ip), ttl=60)
        elif res == "ask":
            captcha_needed(ip, why, dev=dev)
        return res
    except Exception:
        return ""


def captcha_needed(ip, why, dev=""):
    """Unusual activity seen (rate limit / bot score).  True = ask the game captcha now (mode 'on').
    Mode 'log' only writes it down (dry-run), mode 'off' does nothing."""
    try:
        m = mode()
        if m == "off":
            return False
        with _viol_lock:
            _viol["captcha_asked"] += 1
        # (no "viol" point here: asking a game must not raise the bot score, or the same visitor is asked again and again)
        _log("warn", "captcha ip=%s %s -> %s" % (ip, why, "ASK" if m == "on" else "log only (dry-run)"),
             key="capask:" + ip_key(ip), ttl=60)
        return m == "on"
    except Exception:
        return False


def info(headers, peer=""):
    """Everything the admin panel's Protection card shows."""
    ip = client_ip(headers, peer)
    seen = {h: headers.get(h) for h in ("X-Real-IP", "CF-Connecting-IP", "X-Forwarded-For", "True-Client-IP")}
    with _viol_lock:
        viol = dict(_viol)
    return {"mode": mode(), "env_mode": _ENV_MODE, "loaded": _loaded.is_set(),
            "your_ip": ip, "peer": peer, "headers": seen,
            "active_ips_1min": len(REQ.keys("ip:", 60)),
            "sessions": sess_count(), "downloads": dl_total(), "dl_max": DL_MAX, "sess_max_min": SESS_MAX // 60, "sess_idle": SESS_IDLE,
            "violations": viol, "vip": vip_list(), "vip_max": VIP_MAX,
            "bans": len(ban_list()), "decoys": len(_decoy_cache),
            "limits": {"guest_max": GUEST_MAX, "guest_hours": GUEST_HOURS, "conc_max": CONC_MAX,
                       "ban_score": BAN_SCORE, "flag_score": FLAG_SCORE, "ban_hours": BAN_HOURS}}
