# -*- coding: utf-8 -*-
"""
captcha.py - protection plan, Step 7: the game captcha (server side).

The game ("rang dekho, maaro"):  a cannon at the bottom, up to 4 balls that move along curves and
change colour all the time.  The cannon shows a target colour: shoot a ball of that colour.
HITS (2) correct hits are needed, so one lucky shot is not enough.  A shot goes a little crooked
(skew, shown to the player by the aim line).

How it is checked (nothing here trusts the browser):
  1. new()     makes a game from a random SEED: ball paths, colours, target colours, skew.  The
               game is kept on the server (60 s, one use) and the visitor gets its layout.
  2. verify()  gets only what the player DID: for every shot the time and the aim angle (plus a
               few aim samples).  The server RUNS THE GAME AGAIN from its own seed, shot by shot,
               and decides itself whether the shots hit.  "I passed" does not exist.
  3. Human check: not faster than MIN_SHOT_MS, aim samples must look like a hand (small shake, not
               machine-straight, not evenly timed, not perfectly still), the shot clock cannot run
               ahead of the real clock.
  4. Hidden proof-of-work: a small hash puzzle the page solves in the background (the visitor sees
               nothing); a bot pays CPU for every captcha.
  5. Pass token: after a pass the visitor gets a signed token bound to the IP (30 min).  It goes in
               header X-Captcha.  check_pass() is how every later rule asks "is this a proven human?".
  6. Game types rotate: TYPES paths, two of them active at a time, changing every ROTATE_DAYS (14).

Coordinates: the card is W x H (360 x 300) "game pixels"; the page scales it to the real size.
Times are milliseconds since the game was received.  Angles are radians, 0 = straight up,
positive = to the right.

Everything is memory-only (a captcha lives 60 s, a restart just means "ask again").  Pass tokens
are signed, so they survive a restart.  No function here may raise into the site: callers get
False / {"ok": False} instead.
"""
import base64
import collections
import hashlib
import hmac
import math
import os
import secrets
import threading
import time

# ----------------------------------------------------------------- numbers ----
W, H = 360, 300
CANNON = (180.0, 284.0)
BULLET_R = 5.0
STEP_MS = 8                         # the shot is re-played in steps of this many ms
TAU = 2 * math.pi
TYPES = ("zigzag", "orbit", "lissajous", "eight")
NCOL = 4                            # colours: 0 laal, 1 neela, 2 hara, 3 peela (the page picks the real colours)


def _num(key, default, lo, hi, cast=float):
    try:
        return max(lo, min(hi, cast(float(os.environ.get(key, default)))))
    except Exception:
        return default


TTL = _num("CAPTCHA_TTL", 120, 10, 600, int)               # a captcha lives this long (seconds), one use
PASS_TTL = _num("CAPTCHA_PASS_MIN", 180, 1, 1440, int) * 60  # pass token life (phone / web)
POW_BITS = _num("CAPTCHA_POW_BITS", 14, 0, 24, int)       # hidden puzzle: leading zero bits (14 = ~16k hashes)
BURST_MAX = _num("CAPTCHA_BURST", 5, 2, 50, int)          # this many DIFFERENT videos in BURST_WIN s = rate limit seen
BURST_WIN = 60
HUMAN_FAIL = 60                     # human score (0-100) from which the shots are called a bot's
MODE = os.environ.get("CAPTCHA_MODE", "text").strip().lower()   # "text" = type the distorted letters (sarkari style) | "tap" = tap the ball of the asked colour | "shoot" = old cannon game
if MODE not in ("text", "tap", "shoot"):
    MODE = "text"
try:
    import textcaptcha
    if MODE == "text" and not textcaptcha.OK:      # Pillow is not installed: keep the site working with the ball game
        MODE = "tap"
except Exception:
    textcaptcha = None
    if MODE == "text":
        MODE = "tap"
TEXT_LEN = _num("CAPTCHA_TEXT_LEN", 6, 4, 8, int)          # letters in the picture
TEXT_MATH_PCT = _num("CAPTCHA_MATH_PCT", 30, 0, 100, int)         # % of the pictures that are a small sum (7+4-2=?)
TEXT_SORT_PCT = _num("CAPTCHA_SORT_PCT", 30, 0, 100, int)         # % that are "put these 3-4 numbers in order" (the rest: letters)
TEXT_MIN_MS = _num("CAPTCHA_TEXT_MIN_MS", 1500, 300, 10000, int)   # typing the answer cannot be faster than this (a program is)
ROTATE_DAYS = _num("CAPTCHA_ROTATE_DAYS", 14, 1, 365, int)
CONC_HARD = _num("CAPTCHA_CONC_HARD", 4, 2, 50, int)      # even a proven human may not run more live streams than this
TV_HOURS = _num("CAPTCHA_TV_HOURS", 8, 1, 48, int)         # Step 9: TV pass lives this long (plan: 6-12 hours)
TV_VIDEOS = _num("CAPTCHA_TV_VIDEOS", 35, 5, 500, int)     # ... or this many DIFFERENT videos, whichever comes first (plan: 30-40)
TV_PAIR_TTL = 120                                          # a QR / code works for 2 minutes, once
TV_PAIR_OPEN = 6                                           # open QR codes per TV IP at a time (a hostel has many TVs)

_DEFAULT = {
    "speed": 0.55,       # how fast the balls move (x)  [a little faster than 0.35, still easy]
    "size": 26.0,        # ball radius (px)  [EASY: was 16]
    "balls": 3,          # how many balls (2-4)  [EASY: was 4]
    "color_ms": 2200,    # a ball changes its colour every this many ms
    "skew": 0.0,         # the shot goes this far crooked (radians, +-)  [EASY: was 0.10]
    "bullet": 800.0,     # bullet speed (px/s)  [EASY: was 520]
    "hits": 3,           # correct hits needed
    "max_shots": 5,      # taps allowed (5 tries, 3 right = pass)
    "min_shot_ms": 400,  # no shot sooner than this after the start / the previous shot
    "slack": 10.0,       # extra hit distance (px)  [EASY: was 3]
}
_LIMITS = {"speed": (0.3, 3.0), "size": (8.0, 30.0), "balls": (2, 4), "color_ms": (600, 8000), "skew": (0.0, 0.3),
           "bullet": (250.0, 1200.0), "hits": (1, 4), "max_shots": (1, 10), "min_shot_ms": (100, 1500), "slack": (0.0, 10.0)}
_cfg = dict(_DEFAULT)
_cfg_lock = threading.Lock()


def _clean(over):
    out = {}
    for k, v in (over or {}).items():
        if k in _DEFAULT:
            try:
                lo, hi = _LIMITS[k]
                v = float(v)
                if not math.isfinite(v):
                    continue
                v = max(lo, min(hi, v))
                out[k] = int(round(v)) if isinstance(_DEFAULT[k], int) else v
            except Exception:
                pass
    return out


def cfg():
    with _cfg_lock:
        return dict(_cfg)


_CFG_KEY = "captcha_cfg"             # row in the kv table: only the numbers that differ from the defaults


def set_cfg(over=None, reset=False, save=False):
    """The game lab / admin changes the numbers.  save=True also keeps them in the DB (restart-proof, Step 8)."""
    with _cfg_lock:
        if reset:
            _cfg.clear(); _cfg.update(_DEFAULT)
        _cfg.update(_clean(over))
        now = dict(_cfg)
    if save:
        save_cfg(now)
    return now


def save_cfg(c=None):
    """-> True when the DB took it.  Never raises (a down DB only means: works until restart)."""
    try:
        import json
        import accounts
        c = c or cfg()
        diff = {k: v for k, v in c.items() if _DEFAULT.get(k) != v}
        accounts.kv_set(_CFG_KEY, json.dumps(diff))
        return True
    except Exception as e:
        _log("warn", "game numbers not saved to DB (%r) - they work until restart" % (e,), key="cap_cfg_save", ttl=300)
        return False


def load_cfg():
    """Called once at start: the numbers saved from the lab come back.  -> dict of what was loaded."""
    try:
        import json
        import accounts
        raw = accounts.kv_get(_CFG_KEY)
        over = _clean(json.loads(raw)) if raw else {}
        if over:
            set_cfg(over)
        return over
    except Exception as e:
        _log("warn", "game numbers not loaded from DB (%r) - defaults are used" % (e,), key="cap_cfg_load", ttl=300)
        return {}


# ------------------------------------------------------------- randomness ----
class Rng:
    """mulberry32 - tiny, 32-bit only, so a JavaScript port gives the very same numbers."""

    def __init__(self, seed):
        self.s = int(seed) & 0xFFFFFFFF

    def next(self):
        M = 0xFFFFFFFF
        self.s = (self.s + 0x6D2B79F5) & M
        a = self.s
        t = ((a ^ (a >> 15)) * (1 | a)) & M
        t = (((t + (((t ^ (t >> 7)) * (61 | t)) & M)) & M) ^ t) & M
        return ((t ^ (t >> 14)) & M) / 4294967296.0

    def between(self, lo, hi):
        return lo + (hi - lo) * self.next()

    def below(self, n):
        return int(self.next() * n) % n


def active_types(now=None):
    """Two of the 4 game types are live at a time; the pair moves on every ROTATE_DAYS."""
    p = int((now or time.time()) // 86400 // ROTATE_DAYS)
    return [p % len(TYPES), (p + 1) % len(TYPES)]


# ------------------------------------------------------------------- game ----
def layout(seed, typ, c):
    """Everything about one game, from its seed (and nothing else)."""
    r = Rng(seed)
    n = int(c["balls"])
    perm = list(range(NCOL))
    for i in range(NCOL - 1, 0, -1):                      # shuffle the colours
        j = r.below(i + 1)
        perm[i], perm[j] = perm[j], perm[i]
    balls = []
    rows = list(range(n))                                 # zigzag rows in a random order
    for i in range(n - 1, 0, -1):
        j = r.below(i + 1)
        rows[i], rows[j] = rows[j], rows[i]
    for i in range(n):
        d = 1 if r.below(2) else -1                       # every ball picks its own direction
        ty = r.below(4)                                   # ... and its OWN kind of path (all 4 kinds mixed in one game)
        b = {"c": perm[i], "ty": ty, "ph": round(r.between(0, TAU), 4), "ph2": round(r.between(0, TAU), 4), "dir": d}
        if ty == 0:                                       # zigzag: sideways triangle wave, bobbing rows
            b.update(f=round(r.between(0.18, 0.48), 4), g=round(r.between(1.0, 2.6), 4), y=50 + 36 * rows[i])
        elif ty == 1:                                     # orbit: ellipses of different size, both directions
            b.update(f=round(r.between(0.7, 1.7), 4),
                     rx=round(52 + 24 * rows[i] + r.between(-8, 8), 3), ry=round(26 + 13 * rows[i] + r.between(-6, 6), 3))
        elif ty == 2:                                     # lissajous: wide wandering curves
            b.update(f=round(r.between(0.6, 1.5), 4), g=round(r.between(0.9, 2.2), 4))
        else:                                             # figure eight
            b.update(f=round(r.between(0.6, 1.4), 4), ry=round(r.between(30, 56), 3))
        b.update(wa=round(r.between(6, 16), 3), wb=round(r.between(5, 12), 3), wf=round(r.between(0.5, 1.5), 4),   # random wobble on top,
                 wg=round(r.between(0.6, 1.7), 4), wp=round(r.between(0, TAU), 4), wq=round(r.between(0, TAU), 4))  # so no path repeats
        balls.append(b)
    ms = int(c["max_shots"])
    return {
        "type": typ, "n": n, "balls": balls,
        "targets": [perm[r.below(n)] for _ in range(ms + 4)],   # only colours that are really on screen
        "skews": [round(r.between(-1, 1) * float(c["skew"]), 4) for _ in range(ms + 4)],
    }


def _tri(x):                                              # triangle wave, period 1, -1..1
    f = x - math.floor(x)
    return 4.0 * abs(f - 0.5) - 1.0


def ball_pos(L, i, t_ms, c):
    """Where ball i is at time t_ms.  The page uses the same formulas to draw it."""
    p, u = L["balls"][i], t_ms / 1000.0 * float(c["speed"])
    ty = p.get("ty", L["type"])
    if ty != 1:
        u *= p.get("dir", 1)
    if ty == 0:
        x, y = 180.0 + 118.0 * _tri(u * p["f"] + p["ph"] / TAU), p["y"] + 20.0 * math.sin(u * p["g"] + p["ph2"])
    elif ty == 1:
        a = u * p["f"] * p["dir"] + p["ph"]
        x, y = 180.0 + p["rx"] * math.cos(a), 110.0 + p["ry"] * math.sin(a)
    elif ty == 2:
        x, y = 180.0 + 125.0 * math.sin(u * p["f"] + p["ph"]), 105.0 + 55.0 * math.sin(u * p["g"] + p["ph2"])
    else:
        a = u * p["f"] + p["ph"]
        x, y = 180.0 + 122.0 * math.sin(a), 105.0 + p["ry"] * math.sin(2.0 * a + p["ph2"])
    if "wa" in p:
        x += p["wa"] * math.sin(u * p["wf"] + p["wp"])
        y += p["wb"] * math.sin(u * p["wg"] + p["wq"])
    return x, max(y, 32.0)


def ball_color(L, i, t_ms, c):
    return L["balls"][i]["c"] % NCOL      # every ball keeps ONE colour all game (only its movement is random)


def sim_shot(L, c, k, t_ms, a):
    """Play shot number k (fired at t_ms, finger angle a) -> {"hit": ball or -1, "t": hit time, "color": ...}."""
    ang = a + L["skews"][k]
    dx, dy = math.sin(ang), -math.cos(ang)
    vb, reach = float(c["bullet"]), float(c["size"]) + BULLET_R + float(c["slack"])
    ms, end = int(t_ms), int(t_ms) + int(1000 * 340 / vb)
    while ms <= end:
        d = vb * (ms - t_ms) / 1000.0
        bx, by = CANNON[0] + dx * d, CANNON[1] + dy * d
        if bx < -BULLET_R or bx > W + BULLET_R or by < -BULLET_R:
            break
        best, bd = -1, 1e18
        for i in range(L["n"]):
            x, y = ball_pos(L, i, ms, c)
            dd = (x - bx) ** 2 + (y - by) ** 2
            if dd <= reach * reach and dd < bd:
                best, bd = i, dd
        if best >= 0:
            return {"hit": best, "t": ms, "color": ball_color(L, best, ms, c)}
        ms += STEP_MS
    return {"hit": -1, "t": None, "color": None}


def replay(L, c, shots):
    """Play all the shots in order.  -> (hits, [per shot result]).  Only a ball of the target colour counts."""
    need, hits, out = int(c["hits"]), 0, []
    for k, s in enumerate(shots):
        if hits >= need:
            break
        r = sim_shot(L, c, k, s["t"], s["a"])
        want = L["targets"][hits]
        r["want"], r["ok"] = want, bool(r["hit"] >= 0 and r["color"] == want)
        hits += r["ok"]
        out.append(r)
    return hits, out


# ------------------------------------------------------------ open games ----
_open = {}                           # id -> record
_lock = threading.Lock()
_stat = collections.Counter()
_recent = collections.deque(maxlen=40)
_stat_lock = threading.Lock()


def _ipk(ip):
    try:
        import guard
        return guard.ip_key(ip)
    except Exception:
        return str(ip)


def _log(lvl, msg, key=None, ttl=60):
    try:
        import guard
        guard._log(lvl, "captcha " + msg, key=key, ttl=ttl)
    except Exception:
        pass


def _prune(now):
    for k in [k for k, r in _open.items() if r["exp"] < now]:
        del _open[k]
    if len(_open) > 20000:                                   # flood: forget the oldest half
        for k in sorted(_open, key=lambda k: _open[k]["t0"])[: len(_open) // 2]:
            del _open[k]


def _fails_recent(ipk, now):
    d = _fail_hist.get(ipk)
    if not d:
        return 0
    while d and d[0] < now - 600:
        d.popleft()
    return len(d)


_fail_hist = {}                      # ipk -> deque of fail times (last 10 min)


def new(ip, dev="", typ=None, over=None, now=None):
    """Start a captcha.  typ / over (game type, number overrides) are for the admin's game lab only."""
    try:
        now = now or time.time()
        lab_typ = typ is not None
        c = cfg()
        c.update(_clean(over))
        if typ is None or not (0 <= int(typ) < len(TYPES)):
            typ = active_types(now)[secrets.randbelow(2)]
        typ = int(typ)
        if MODE == "text" and not over and not lab_typ:        # the normal site: a picture of letters (the game lab still gets the game)
            return _new_text(ip, dev, now)
        seed = secrets.randbits(32)
        L = layout(seed, typ, c)
        ipk = _ipk(ip)
        bits = POW_BITS + (2 if _fails_recent(ipk, now) >= 3 else 0)     # a visitor that keeps failing pays more CPU
        cid = secrets.token_urlsafe(12)
        salt = secrets.token_hex(8)
        rec = {"id": cid, "ipk": ipk, "dev": dev or "", "t0": now, "exp": now + TTL, "seed": seed, "L": L, "c": c,
               "salt": salt, "bits": bits, "mode": "tap" if MODE == "text" else MODE}
        with _lock:
            _prune(now)
            _open[cid] = rec
        with _stat_lock:
            _stat["new"] += 1
        return {"id": cid, "ttl": TTL, "w": W, "h": H, "cannon": list(CANNON), "bullet_r": BULLET_R,
                "cfg": {k: c[k] for k in ("speed", "size", "balls", "color_ms", "bullet", "hits", "max_shots", "min_shot_ms", "slack")},
                "game": {"mode": "tap" if MODE == "text" else MODE, "type": typ, "name": TYPES[typ], "balls": L["balls"], "targets": L["targets"][: int(c["max_shots"])],
                         "skews": L["skews"][: int(c["max_shots"])]},
                "pow": {"salt": salt, "bits": bits, "how": "sha256(id:salt:nonce) with `bits` leading zero bits"}}
    except Exception as e:
        _log("error", "new() failed: %r" % (e,), key="cap_new_err", ttl=300)
        return None


def _new_text(ip, dev, now):
    """A picture-of-letters captcha.  The answer stays here; the visitor only gets the picture."""
    ipk = _ipk(ip)
    r = secrets.randbelow(100)                                   # the visitor (and a program) never knows which kind comes
    kind = "sort" if r < TEXT_SORT_PCT else "math" if r < TEXT_SORT_PCT + TEXT_MATH_PCT else "letters"
    ans, img = (textcaptcha.make_sort() if kind == "sort" else textcaptcha.make_math() if kind == "math" else textcaptcha.make(TEXT_LEN))
    bits = POW_BITS + (2 if _fails_recent(ipk, now) >= 3 else 0)
    cid = secrets.token_urlsafe(12)
    salt = secrets.token_hex(8)
    rec = {"id": cid, "ipk": ipk, "dev": dev or "", "t0": now, "exp": now + TTL, "salt": salt, "bits": bits,
           "mode": "text", "kind": kind, "ans": ans if kind == "sort" else textcaptcha.norm(ans)}
    with _lock:
        _prune(now)
        _open[cid] = rec
    with _stat_lock:
        _stat["new"] += 1
    return {"id": cid, "ttl": TTL, "cfg": {}, "game": {"mode": "text", "img": img},
            "pow": {"salt": salt, "bits": bits, "how": "sha256(id:salt:nonce) with `bits` leading zero bits"}}


def _take(cid, ip, now):
    """Fetch the game AND use it up (one try per captcha).  -> (record, "")  or  (None, why)."""
    with _lock:
        _prune(now - 5)                                       # (an expired game is told apart below)
        rec = _open.pop(str(cid or ""), None)
    if not rec:
        return None, "gone"
    if rec["exp"] < now:
        return None, "expired"
    if rec["ipk"] != _ipk(ip):
        return None, "ip"
    return rec, ""


# ------------------------------------------------------------------- pow ----
def pow_ok(cid, salt, bits, nonce):
    try:
        nonce = str(nonce)
        if not nonce or len(nonce) > 24:
            return False
        if bits <= 0:
            return True
        h = hashlib.sha256(("%s:%s:%s" % (cid, salt, nonce)).encode()).digest()
        return int.from_bytes(h, "big") >> (256 - bits) == 0
    except Exception:
        return False


def solve_pow(cid, salt, bits, limit=5_000_000):
    """What the page does in the background (here for the tests and as a reference)."""
    for n in range(limit):
        if pow_ok(cid, salt, bits, n):
            return str(n)
    return None


# ----------------------------------------------------------- human check ----
def _std(v):
    m = sum(v) / len(v)
    return math.sqrt(sum((x - m) ** 2 for x in v) / len(v))


def human_score(shots):
    """0-100: how much the aim looks like a machine's.  Per shot, the worst shot counts.  -> (score, reasons)"""
    worst, why = 0, []
    for k, s in enumerate(shots):
        pts, r = 0, []
        sm = s.get("s") or []
        n = len(sm)
        if n == 0:
            pts += 70; r.append("aim ka koi nishaan nahi")
        elif n < 3:
            pts += 30; r.append("aim ke 3 se kam nishaan")
        else:
            ts, an = [p[0] for p in sm], [p[1] for p in sm]
            if any(b < a for a, b in zip(ts, ts[1:])) or ts[0] < s["t"] - 2500 or ts[-1] > s["t"] + 60:
                pts += 40; r.append("aim ka waqt ulta / shot se mel nahi")
            if abs(an[-1] - s["a"]) > 0.05:
                pts += 40; r.append("chhodte waqt ka angle shot se alag")
            if ts[-1] - ts[0] < 120:
                pts += 20; r.append("aim 0.12 sec se chhota")
            if _std(an) < 1e-9:
                pts += 35; r.append("haath bilkul nahi hila")
            if n >= 5 and ts[-1] > ts[0]:                  # machine-straight line from first to last sample?
                slope = (an[-1] - an[0]) / (ts[-1] - ts[0])
                if max(abs(an[0] + slope * (t - ts[0]) - a) for t, a in zip(ts, an)) < 1e-6 and abs(an[-1] - an[0]) > 1e-6:
                    pts += 40; r.append("aim ek dum seedhi lakeer")
            if n >= 6:
                d = [b - a for a, b in zip(ts, ts[1:])]
                if _std(d) < 0.5:
                    pts += 30; r.append("samples ek dum barabar gap pe")
        if pts > worst:
            worst, why = pts, ["shot %d: %s" % (k + 1, x) for x in r]
    if shots and all(abs(s["a"]) < 1e-9 for s in shots):
        worst += 45; why.append("har shot bilkul seedha (0 angle)")
    return min(100, worst), why


def _read_shots(body, c):
    """Clean the shots the browser sent.  -> list or None (garbage)."""
    try:
        raw = body.get("shots")
        if not isinstance(raw, list) or not 1 <= len(raw) <= int(c["max_shots"]):
            return None
        out = []
        for s in raw:
            t, a = float(s["t"]), float(s["a"])
            if not (math.isfinite(t) and math.isfinite(a)) or t < 0 or t > 120000 or abs(a) > 1.4:
                return None
            sm = []
            for p in (s.get("s") or [])[:60]:
                pt, pa = float(p[0]), float(p[1])
                if not (math.isfinite(pt) and math.isfinite(pa)):
                    return None
                sm.append((pt, pa))
            out.append({"t": int(round(t)), "a": a, "s": sm})
        return out
    except Exception:
        return None


# ------------------------------------------------------------- tap mode ----
def _read_taps(body, c):
    """Clean the taps the browser sent: [{t, x, y}].  -> list or None (garbage)."""
    try:
        raw = body.get("shots")
        if not isinstance(raw, list) or not 1 <= len(raw) <= int(c["max_shots"]):
            return None
        out = []
        for s in raw:
            t, x, y = float(s["t"]), float(s["x"]), float(s["y"])
            if not all(math.isfinite(v) for v in (t, x, y)) or t < 0 or t > 120000 or not (-60 <= x <= W + 60) or not (-60 <= y <= H + 60):
                return None
            out.append({"t": int(round(t)), "x": x, "y": y})
        return out
    except Exception:
        return None


def replay_tap(L, c, taps):
    """The server decides itself: at the tap time, is the tap on a ball of the asked colour?  -> (hits, [per tap])"""
    need, hits, out = int(c["hits"]), 0, []
    reach = float(c["size"]) + float(c["slack"])
    for s in taps:
        if hits >= need:
            break
        want = L["targets"][hits]
        best, bd = -1, 1e18
        for i in range(L["n"]):
            x, y = ball_pos(L, i, s["t"], c)
            dd = (x - s["x"]) ** 2 + (y - s["y"]) ** 2
            if dd <= reach * reach and dd < bd:
                best, bd = i, dd
        col = ball_color(L, best, s["t"], c) if best >= 0 else None
        ok = bool(best >= 0 and col == want)
        hits += ok
        out.append({"hit": best, "t": s["t"], "color": col, "want": want, "ok": ok, "dist": round(math.sqrt(bd), 2) if best >= 0 else None})
    return hits, out


def tap_score(taps, res):
    """0-100: how machine-like are the taps?  (dead-centre every time / evenly timed)"""
    score, why = 0, []
    hit_d = [r["dist"] for r in res if r["dist"] is not None]
    if len(hit_d) >= 2 and max(hit_d) < 0.6:
        score += 70; why.append("har tap gend ke bilkul beech me")
    if len(taps) >= 3:
        d = [b["t"] - a["t"] for a, b in zip(taps, taps[1:])]
        if _std(d) < 0.5:
            score += 30; why.append("taps ek dum barabar gap pe")
    return score, why


# ----------------------------------------------------------------- verify ----
def _record(ip, ok, why, score=0, ms=0):
    now = time.time()
    ipk = _ipk(ip)
    with _stat_lock:
        _stat["pass" if ok else "fail"] += 1
        if not ok:
            _stat["why_" + why] += 1
        _recent.append({"t": round(now), "ip": ipk, "ok": ok, "why": why, "score": score, "ms": ms})
    if not ok:
        d = _fail_hist.setdefault(ipk, collections.deque())
        d.append(now)
        if len(_fail_hist) > 20000:
            _fail_hist.clear()


def verify(cid, ip, body, now=None, lab=False):
    """The visitor says what he did.  -> {"ok": True, "token", "ttl"}  or  {"ok": False, "why", "retry": True}.
    lab=True (admin game lab) adds the full detail: hits, per-shot results, human score."""
    now = now or time.time()
    try:
        body = body if isinstance(body, dict) else {}
        rec, why = _take(cid, ip, now)
        if not rec:
            _record(ip, False, why)
            return {"ok": False, "why": why, "retry": True}
        c, L = rec.get("c"), rec.get("L")
        detail = {}

        def fail(w, score=0):
            _record(ip, False, w, score, int((now - rec["t0"]) * 1000))
            out = {"ok": False, "why": "bot" if w in ("speed", "clock", "human", "pow", "shots") else w, "retry": True}
            if lab:
                out.update(real_why=w, **detail)
            return out

        if rec.get("mode") == "text":
            return _verify_text(rec, body, ip, now, fail)
        tap = rec.get("mode") == "tap"
        shots = (_read_taps if tap else _read_shots)(body, c)
        if shots is None:
            return fail("shots")

        # 1. the hidden proof-of-work
        if not pow_ok(rec["id"], rec["salt"], rec["bits"], body.get("pow")):
            return fail("pow")
        # 2. clocks: no shot sooner than min_shot_ms, and the game clock cannot run ahead of the real one
        prev = 0
        for s in shots:
            if s["t"] - prev < int(c["min_shot_ms"]):
                return fail("speed")
            prev = s["t"]
        if shots[-1]["t"] > (now - rec["t0"]) * 1000 + 1500:
            return fail("clock")
        # 3. does the aim look like a hand?  4. play the game again on the server
        if tap:
            hits, res = replay_tap(L, c, shots)
            score, hw = tap_score(shots, res)
        else:
            score, hw = human_score(shots)
        detail.update(human=score, human_why=hw)
        if score >= HUMAN_FAIL:
            return fail("human", score)
        if not tap:
            hits, res = replay(L, c, shots)
        detail.update(hits=hits, shots=res, need=int(c["hits"]))
        if hits < int(c["hits"]):
            return fail("miss", score)
        _record(ip, True, "", score, int((now - rec["t0"]) * 1000))
        out = {"ok": True, "token": make_pass(ip, now=now), "ttl": PASS_TTL}
        if lab:
            out.update(detail)
        return out
    except Exception as e:
        _log("error", "verify() failed: %r" % (e,), key="cap_ver_err", ttl=300)
        return {"ok": False, "why": "error", "retry": True}


def _verify_text(rec, body, ip, now, fail):
    """Picture captcha: hidden proof-of-work, not typed faster than a person can, then the letters themselves."""
    if not pow_ok(rec["id"], rec["salt"], rec["bits"], body.get("pow")):
        return fail("pow")
    if (now - rec["t0"]) * 1000 < TEXT_MIN_MS:
        return fail("speed")
    if rec.get("kind") == "sort":                       # numbers in the right order; any separator is fine
        typed = ",".join(str(x) for x in textcaptcha.parse_nums(body.get("text")))
    else:
        typed = textcaptcha.norm(body.get("text"))
    if not typed or not hmac.compare_digest(typed.encode(), rec["ans"].encode()):
        return fail("miss")
    _record(ip, True, "", 0, int((now - rec["t0"]) * 1000))
    return {"ok": True, "token": make_pass(ip, now=now), "ttl": PASS_TTL}


# ------------------------------------------------------------ pass token ----
_key = hashlib.sha256((os.environ.get("TOKEN_SECRET") or os.environ.get("SQL_URL")
                       or os.environ.get("ADMIN_KEY") or secrets.token_hex(32)).encode()).digest()


def configure(key):
    """addon.py gives its own secret, so the captcha token lives and dies with the other links."""
    global _key
    if key:
        _key = hashlib.sha256(b"captcha" + bytes(key)).digest()


def make_pass(ip, kind="w", ttl=None, now=None):
    """Signed pass for this IP:  kind w = phone / web (30 min).  TV passes (kind t) are made by make_tv_pass()."""
    exp = int((now or time.time()) + (ttl or PASS_TTL))
    payload = ("%s|%s|%d" % (kind, _ipk(ip), exp)).encode()
    sig = hmac.new(_key, payload, hashlib.sha256).digest()[:16]
    return base64.urlsafe_b64encode(payload).decode().rstrip("=") + "." + base64.urlsafe_b64encode(sig).decode().rstrip("=")


def check_pass(token, ip, kind="w", now=None):
    """True = the visitor passed a captcha lately from this IP.  Never raises."""
    try:
        a, b = str(token or "").split(".")
        payload = base64.urlsafe_b64decode(a + "=" * (-len(a) % 4))
        sig = base64.urlsafe_b64decode(b + "=" * (-len(b) % 4))
        if not hmac.compare_digest(sig, hmac.new(_key, payload, hashlib.sha256).digest()[:16]):
            return False
        k, ipk, exp = payload.decode().split("|")
        return k == kind and ipk == _ipk(ip) and int(exp) >= (now or time.time())
    except Exception:
        return False


# ------------------------------------------------------ signup pass (Step 10) ----
_su_used = {}                        # pass signature -> time it paid for a signup
_su_lock = threading.Lock()


def signup_spent(token, now=None):
    """Step 10: did this pass already pay for an account?  (one game = one signup)"""
    try:
        sig = str(token or "").split(".")[-1]
        with _su_lock:
            return _su_used.get(sig, 0) > (now or time.time())
    except Exception:
        return False


def signup_spend(token, now=None):
    """Step 10: the pass paid for one account - it cannot pay for another (it still works for video)."""
    try:
        now = now or time.time()
        sig = str(token or "").split(".")[-1]
        with _su_lock:
            for k in [k for k, t in _su_used.items() if t < now]:
                del _su_used[k]
            _su_used[sig] = now + 24 * 3600 + 60
    except Exception:
        pass


# ------------------------------------------------------------ TV pass (Step 9) ----
# The TV cannot play the game (no touch), so a phone plays it for the TV:
#   1. TV    tv_new(tv_ip)          -> {pid (secret, only the TV knows it), code (6 letters, goes in the QR), ttl}
#   2. phone opens  /tv?c=CODE, plays the normal game (/api/captcha/new + verify) and gets a normal pass token
#   3. phone tv_finish(code, pass)  -> the pass is USED UP (one game = one TV) and a TV pass is made for the TV's IP
#   4. TV    tv_poll(pid, tv_ip)    -> {state: wait | ok (+ token) | gone}, asked every 2 s
# The TV pass is signed, bound to the TV's IP, lives TV_HOURS or TV_VIDEOS different videos, and allows ONE stream
# (latest wins).  The phone may be on another IP (mobile data): only the TV's IP counts.
_CODE_CHARS = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"        # no 0/O, 1/I: easy to read off a TV
_pairs = {}                          # pid -> {code, ipk, exp, tok}
_codes = {}                          # code -> pid
_used = {}                           # signature of a phone pass already used for a TV -> its expiry
_tv_use = {}                         # token id -> {"v": {video: t}, "exp", "sid"}
_tv_lock = threading.Lock()


def _tv_prune(now):
    for p in [p for p, r in _pairs.items() if r["exp"] < now]:
        _codes.pop(_pairs[p]["code"], None)
        del _pairs[p]
    for k in [k for k, e in _used.items() if e < now]:
        del _used[k]
    for k in [k for k, r in _tv_use.items() if r["exp"] < now]:
        del _tv_use[k]
    if len(_pairs) > 20000:
        _pairs.clear()
        _codes.clear()
    if len(_tv_use) > 50000:
        _tv_use.clear()


def tv_new(ip, now=None):
    """A TV asks for a QR.  -> {"pid", "code", "ttl"}  (pid stays on the TV, only code goes in the QR)."""
    try:
        now = now or time.time()
        ipk = _ipk(ip)
        with _tv_lock:
            _tv_prune(now)
            mine = sorted((r["exp"], p) for p, r in _pairs.items() if r["ipk"] == ipk)
            while len(mine) >= TV_PAIR_OPEN:                 # more than a few open QRs: the oldest goes
                _, p = mine.pop(0)
                _codes.pop(_pairs[p]["code"], None)
                del _pairs[p]
            for _ in range(20):
                code = "".join(_CODE_CHARS[secrets.randbelow(len(_CODE_CHARS))] for _ in range(6))
                if code not in _codes:
                    break
            pid = secrets.token_urlsafe(16)
            _pairs[pid] = {"code": code, "ipk": ipk, "exp": now + TV_PAIR_TTL, "tok": ""}
            _codes[code] = pid
        with _stat_lock:
            _stat["tv_new"] += 1
        return {"pid": pid, "code": code, "ttl": TV_PAIR_TTL}
    except Exception as e:
        _log("error", "tv_new() failed: %r" % (e,), key="tv_new_err", ttl=300)
        return None


def _code_of(code):
    return "".join(ch for ch in str(code or "").upper() if ch in _CODE_CHARS)[:6]


def tv_peek(code, now=None):
    """Is this code an open, not yet used QR?  (The phone page asks before it shows the game.)"""
    try:
        now = now or time.time()
        with _tv_lock:
            pid = _codes.get(_code_of(code))
            r = _pairs.get(pid) if pid else None
            return bool(r and r["exp"] >= now and not r["tok"])
    except Exception:
        return False


def tv_finish(code, phone_ip, phone_pass, now=None):
    """The phone passed the game and hands its pass in.  -> (True, "") or (False, why).
    The phone pass is used up here: one game gives ONE TV a pass, not many."""
    try:
        now = now or time.time()
        if not check_pass(phone_pass, phone_ip, now=now):
            return False, "nopass"
        sig = str(phone_pass).split(".")[-1]
        with _tv_lock:
            _tv_prune(now)
            if sig in _used:
                return False, "used"
            pid = _codes.get(_code_of(code))
            r = _pairs.get(pid) if pid else None
            if not r or r["exp"] < now:
                return False, "gone"
            if r["tok"]:
                return False, "used"
            _used[sig] = now + PASS_TTL + 60
            r["tok"] = make_tv_pass(r["ipk"], now=now)
        with _stat_lock:
            _stat["tv_done"] += 1
        return True, ""
    except Exception as e:
        _log("error", "tv_finish() failed: %r" % (e,), key="tv_fin_err", ttl=300)
        return False, "error"


def tv_poll(pid, ip, now=None):
    """The TV asks (every 2 s).  -> {"state": "wait"} | {"state": "ok", "token", "ttl", "videos"} | {"state": "gone"}.
    Only the IP that asked for the QR may poll.  The answer can be read again until the QR expires (a lost reply)."""
    try:
        now = now or time.time()
        with _tv_lock:
            r = _pairs.get(str(pid or ""))
            if not r or r["exp"] < now or r["ipk"] != _ipk(ip):
                return {"state": "gone"}
            if not r["tok"]:
                return {"state": "wait"}
            return {"state": "ok", "token": r["tok"], "ttl": TV_HOURS * 3600, "videos": TV_VIDEOS}
    except Exception:
        return {"state": "gone"}


def make_tv_pass(ip_or_key, ttl=None, videos=None, now=None):
    """Signed TV pass: kind t, bound to the TV's IP, with its own random id (that is what counts videos / the stream)."""
    now = now or time.time()
    exp = int(now + (ttl or TV_HOURS * 3600))
    ipk = _ipk(ip_or_key)                      # (an IP key that is already a key stays as it is)
    payload = ("t|%s|%d|%s" % (ipk, exp, secrets.token_hex(6))).encode()
    sig = hmac.new(_key, payload, hashlib.sha256).digest()[:16]
    return base64.urlsafe_b64encode(payload).decode().rstrip("=") + "." + base64.urlsafe_b64encode(sig).decode().rstrip("=")


def check_tv_pass(token, ip, now=None):
    """-> the pass id when this is a valid TV pass for this IP, else "".  Never raises."""
    try:
        a, b = str(token or "").split(".")
        payload = base64.urlsafe_b64decode(a + "=" * (-len(a) % 4))
        sig = base64.urlsafe_b64decode(b + "=" * (-len(b) % 4))
        if not hmac.compare_digest(sig, hmac.new(_key, payload, hashlib.sha256).digest()[:16]):
            return ""
        k, ipk, exp, nid = payload.decode().split("|")
        if k == "t" and ipk == _ipk(ip) and int(exp) >= (now or time.time()):
            return nid
    except Exception:
        pass
    return ""


def tv_video(nid, video, now=None):
    """The TV pass `nid` asks for `video`.  -> (still_valid, videos_used).  The same video again (seek, retry,
    renew) is not counted twice.  After TV_VIDEOS different videos the pass is finished (a new QR is needed)."""
    try:
        now = now or time.time()
        with _tv_lock:
            _tv_prune(now)
            r = _tv_use.get(nid)
            if r is None:
                r = _tv_use[nid] = {"v": {}, "exp": now + TV_HOURS * 3600 + 600, "sid": ""}
            if str(video) not in r["v"]:
                if len(r["v"]) >= TV_VIDEOS:
                    return False, len(r["v"])
                r["v"][str(video)] = now
            return True, len(r["v"])
    except Exception:
        return True, 0


def tv_stream(nid, sid, video="", now=None):
    """The TV pass opened stream session `sid` for `video`.  -> the OLDER session to stop ("" = none).  Latest wins,
    but the same video again (renew / retry) never stops its own earlier link."""
    try:
        now = now or time.time()
        with _tv_lock:
            r = _tv_use.get(nid)
            if r is None:
                r = _tv_use[nid] = {"v": {}, "exp": now + TV_HOURS * 3600 + 600, "sid": ""}
            old = r["sid"] if (r.get("video") != str(video) and r["sid"] != str(sid or "")) else ""
            r["sid"], r["video"] = str(sid or ""), str(video)
            return old
    except Exception:
        return ""


def tv_left(nid):
    try:
        with _tv_lock:
            r = _tv_use.get(nid)
            return TV_VIDEOS - (len(r["v"]) if r else 0)
    except Exception:
        return TV_VIDEOS


# ------------------------------------------------------- rate-limit seen ----
_burst = {}                          # ipk -> {video: time}
_burst_lock = threading.Lock()


def burst(ip, video, now=None):
    """The visitor asked for `video`.  -> how many DIFFERENT videos he asked for in the last BURST_WIN s
    (the same video again - seek, retry, renew - is not counted twice)."""
    try:
        now = now or time.time()
        k = _ipk(ip)
        with _burst_lock:
            if len(_burst) > 30000:
                _burst.clear()
            d = _burst.setdefault(k, {})
            for v in [v for v, t in d.items() if t < now - BURST_WIN]:
                del d[v]
            d.setdefault(str(video), now)
            return len(d)
    except Exception:
        return 0


# ------------------------------------------------------------------ admin ----
def stats():
    with _stat_lock:
        s = dict(_stat)
        rc = list(_recent)[-20:]
    with _lock:
        n_open = len(_open)
    return {"open": n_open, "counts": s, "recent": rc, "types": [TYPES[i] for i in active_types()],
            "cfg": cfg(), "pow_bits": POW_BITS, "ttl": TTL, "pass_min": PASS_TTL // 60,
            "burst_max": BURST_MAX, "human_fail": HUMAN_FAIL,
            "tv": {"open_qr": len(_pairs), "hours": TV_HOURS, "videos": TV_VIDEOS, "passes_in_use": len(_tv_use)}}
