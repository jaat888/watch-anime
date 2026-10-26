#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RareToons 3.0 — Stremio addon.  Streams-only, Phoenix-style cards.

CARD FORMAT (one card per language that actually plays in-app)

    name   ◫ MQ ◫
    title  ⧉ <title> ⌗ <Language>[ · sub]
           ⬡ Movie | ⬡ S01E05 · <episode title>
           ⊞ mollad_jaat ◧ MQ 1080·720·360[ · note]

    Languages: Hindi, Tamil, Telugu, Bengali, Malayalam, Urdu, English,
    Japanese, Anime Times ... (whatever the show's hub carries).
    PLAYABLE-ONLY: a language we cannot resolve to our HLS gets no card.

RESOLUTION PIPELINE

    1. episodes_index.jsonl (crawler snapshot) gives first-guess zippers.
    2. The site ROTATES movie zippers ~hourly and adds dubs/episodes, so
       EVERY stream/meta request merges the live hub page first
       (_live_rows -> _absorb_live, TTL 15 min, negative 4 min).
    3. codedew zipper links (all non-Hindi languages + movies) sit behind
       a 3-step "Security Scan" wall: _zipper_walk follows the data-href
       chain with a cookie session.  Walks are throttled by a global
       semaphore(3) - codedew rate-limits parallel walks.
    4. The post-wall page embeds https://argon.razorshell.space/embed/<id>
       carrying _juicycodes("<blob>"): a symbol-map cipher (ported below)
       decoding to the JWPlayer config whose sources.file is the
       1080p/720p/360p HLS master (groovy.monster, JUICYCODES).
    5. /mq/... proxies rewrite the whole HLS tree same-origin.  The site's
       MQ variant playlists are #EXT-X-BYTERANGE slices of ONE resource -
       exploded to ?rt=start-end so no player ever downloads the whole
       file (the old "full download" bug).  Content is single-video +
       single-audio TS by site encoding.

IDS
    raretoons2:<slug>[:s:e]   legacy ids from our own metas
    tt<...>:s:e               foreign ids, title-matched via Cinemeta

Run:  python3 addon.py [port]     (binds 0.0.0.0)
"""
import base64
import gzip
import hashlib
import hmac
import secrets
import json
import os
import re
import sys
import tempfile
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import urllib.error
import urllib.request
from urllib.parse import urlparse, parse_qs, unquote, urljoin

import accounts
import genres as G
import requests
from curl_cffi import requests as creq

# --------------------------------------------------------------- config ---
def _env_int(key, default):
    try:
        return int(os.environ.get(key) or default)
    except Exception:
        return default

PORT            = _env_int("PORT", 7700)
HOST_SUFFIX     = os.environ.get("HOST_SUFFIX", ".baby-beamup.club")
RESOLVE_TIMEOUT = _env_int("RESOLVE_TIMEOUT", 8)   # per upstream fetch, s
WALK_HOPS       = _env_int("WALK_HOPS", 5)         # wall hops incl. final
WALK_BUDGET     = _env_int("WALK_BUDGET", 10)      # per zipper, s
LIST_BUDGET     = _env_int("LIST_BUDGET", 15)      # per /stream resolve, s
HLS_TTL         = _env_int("HLS_TTL", 1800)        # zipper -> master URL
NEG_TTL         = _env_int("NEG_TTL", 60)          # failed resolve cache
LIVE_TTL        = _env_int("LIVE_TTL", 900)        # hub parse validity
LIVE_NEG        = _env_int("LIVE_NEG", 60)         # empty hub parse cache
WN_TTL          = _env_int("WN_TTL", 6 * 3600)     # WN signed link (~8h life)
WN_STALE        = _env_int("WN_STALE", 6 * 3600)   # max stale-serve age, WN
CINE_TTL        = _env_int("CINE_TTL", 6 * 3600)   # Cinemeta title cache
TMDB_TTL        = _env_int("TMDB_TTL", 7 * 24 * 3600)  # genre lookup cache
LIST_WAIT       = float(os.environ.get("LIST_WAIT") or 1.5)   # card listing waits at most this long (s)
OPTIMISTIC      = os.environ.get("OPTIMISTIC_CARDS", "1") != "0"  # show cards before resolve finishes
_LW             = LIST_WAIT if OPTIMISTIC else LIST_BUDGET
SHOWS_TTL       = _env_int("SHOWS_TTL", 45)        # /api/shows payload cache
PL_TTL          = _env_int("PL_TTL", 300)          # HLS playlist cache (VOD)

VERSION  = "3.4.5"
ADDON_ID = "community.raretoons2"
ADDON_NAME = "mollad_jaat"
BASE_DIR  = os.path.dirname(os.path.abspath(__file__))
SITE = "https://www.rareanimes.mov/"
ARGON = "https://argon.razorshell.space/"
# Public default key (same one Cinemeta-style community addons embed);
# override with your own via env var TMDB_API_KEY.
TMDB_API_KEY = os.environ.get("TMDB_API_KEY", "1af06616dcbb28ff03088d87d63211f5")
TMDB_CACHE_FILE = os.path.join(BASE_DIR, "tmdb_cache.json")
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")

CONTENT_TYPES = {
    ".m3u8": "application/vnd.apple.mpegurl",
    ".ts":   "video/mp2t",
    ".mp4":  "video/mp4",
    ".vtt":  "text/vtt",
    ".key":  "application/octet-stream",
    ".png":  "image/png",
    ".bin":  "application/octet-stream",
}

# Language badge order for cards (top of list first).
LANG_ORDER = {"Hindi": 0, "Tamil": 1, "Telugu": 2, "Bengali": 3,
              "Malayalam": 4, "Urdu": 5, "English": 6, "Japanese": 7,
              "Hindi Sub": 8, "Anime Times": 9}

# ----------------------------------------------------------------- data ---
def _slug(text):
    return re.sub(r"[^a-z0-9]+", "_", (text or "").lower())[:80].strip("_") or "x"


def _load_jsonl(path):
    rows = []
    try:
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if line:
                    rows.append(json.loads(line))
    except FileNotFoundError:
        pass
    return rows


ROWS = _load_jsonl(os.path.join(BASE_DIR, "episodes_index.jsonl"))

POSTERS = {}
try:
    with open(os.path.join(BASE_DIR, "posters.json"), encoding="utf-8") as fh:
        POSTERS = json.load(fh)
except Exception:
    pass


def _display(show):
    """Human hub name; Subbed/Dubbed variants must stay distinct."""
    s = re.split(r"\s+(?:[-–]\s+)?(?:Hindi|Tamil|Telugu|WatchMulti|Multi)\b",
                 show or "", maxsplit=1)[0].strip(" -–")
    s = re.sub(r"\s*(?:[-–]\s*)?Episodes?\.?\s*$", "", s, flags=re.I).strip(" -–")
    if re.search(r"subbed", show or "", re.I):
        s += " (Hindi Sub)"
    elif re.search(r"dubbed", show or "", re.I):
        s += " (Hindi Dub)"
    return s or show


SHOWS = {}

# slug -> {"v":3, "g": [genres], "d": overview, "r": rating 0-10, "rs": "mal"|"tmdb",
#           "rt": tmdb rating, "rm": mal rating, "t": epoch, "nf": not-found,
#           "jf": jikan failed (retry sooner)}
# Stored in SQL (accounts.tmdb) so it survives restarts/redeploys; loaded
# before _build_shows() so the first /api/shows already has genres.
_tmdb_lock = threading.Lock()
_TMDB_CACHE = {}
_TMDB_FAIL = {}          # slug -> time of last failed lookup (memory only)
TMDB_RETRY = 600         # retry a failed lookup after ~10 min
TMDB_NF_TTL = 24 * 3600  # "TMDB has no such title" is rechecked daily
JIKAN_RETRY_TTL = 3600   # entry saved without Jikan data -> retry after 1 h


def _tmdb_load_cache():
    global _TMDB_CACHE
    try:
        _TMDB_CACHE = accounts.tmdb_all()
    except Exception as e:
        print(f"[rt2] tmdb cache load failed: {repr(e)}", flush=True)
        _TMDB_CACHE = {}


def _tmdb_store(slug, info):
    """Save one successful lookup (memory + SQL).  Never called on failure."""
    info = dict(info, g=G.finalize(info.get("g"), info.get("d"), info.get("rs")), gf=1)
    with _tmdb_lock:
        _TMDB_CACHE[slug] = info
    try:
        accounts.tmdb_set(slug, info)
    except Exception as e:
        print(f"[rt2] tmdb save failed for {slug}: {repr(e)}", flush=True)


# NOTE: the cache is now loaded in the background by _tmdb_boot() (started in main())
# so the port opens at once and a cold SQL service cannot delay wake-up.


def _migrate_genres():
    """One-time, in the background: clean + top up (6-8) the genres of every
    already-saved show and store them back, so it is never recomputed."""
    n = 0
    for slug, info in list(_TMDB_CACHE.items()):
        if not isinstance(info, dict) or info.get("gf"):
            continue
        try:
            new = dict(info, g=G.finalize(info.get("g"), info.get("d"), info.get("rs")), gf=1)
            with _tmdb_lock:
                _TMDB_CACHE[slug] = new
            accounts.tmdb_set(slug, new)
            n += 1
        except Exception as e:
            print(f"[rt2] genre migrate failed for {slug}: {repr(e)}", flush=True)
        time.sleep(0.005)
    if n:
        print(f"[rt2] genres saved for {n} shows", flush=True)


def _tmdb_boot():
    """Background boot: load the whole tmdb table, fill genres/desc/rating into
    the already-built SHOWS, then run the one-time genre migration."""
    global _TMDB_CACHE
    try:
        loaded = accounts.tmdb_all()
    except Exception as e:
        print(f"[rt2] tmdb cache load failed: {repr(e)}", flush=True)
        loaded = {}
    with _tmdb_lock:
        loaded.update(_TMDB_CACHE)       # anything saved meanwhile wins
        _TMDB_CACHE = loaded
    with STORE_LOCK:
        for rec in SHOWS.values():
            c = _TMDB_CACHE.get(rec["slug"]) or {}
            rec["genres"] = c.get("g", [])
            rec["desc"] = c.get("d", "")
            rec["rating"] = c.get("r")
    _migrate_genres()


def _build_shows():
    for r in ROWS:
        show = r.get("show") or ""
        slug = _slug(show)
        rec = SHOWS.get(slug)
        if rec is None:
            rec = {"slug": slug, "name": _display(show), "site_name": show,
                   "hub": r.get("hub_url") or "",
                   "poster": POSTERS.get(show, ""), "movie": None, "eps": {}}
            SHOWS[slug] = rec
        try:
            s, e = int(r.get("season") or 0), int(r.get("episode") or 0)
        except (TypeError, ValueError):
            continue
        lst = rec["eps"].setdefault((s, e), [])
        if r not in lst:                 # rebuild-safe: no duplicate rows
            lst.append(r)
    for rec in SHOWS.values():
        rec["movie"] = all((k[0] or 0) == 0 for k in rec["eps"]) if rec["eps"] else False
        rec["poster"] = rec["poster"] or POSTERS.get(rec["site_name"], "")
        rec["genres"] = _TMDB_CACHE.get(rec["slug"], {}).get("g", [])
        rec["desc"] = _TMDB_CACHE.get(rec["slug"], {}).get("d", "")
        rec["rating"] = _TMDB_CACHE.get(rec["slug"], {}).get("r")


_build_shows()
SERIES = [r for r in SHOWS.values() if not r["movie"]]
MOVIES = [r for r in SHOWS.values() if r["movie"]]

# shared store lock: guards SHOWS[x]["eps"] mutation AND iteration
STORE_LOCK = threading.RLock()

# ------------------------------------------------------------------ http ---
def upstream_get(url, referer=None, timeout=RESOLVE_TIMEOUT):
    """Cloudflare-fronted hosts need the impersonating client."""
    headers = {"User-Agent": UA, "Accept": "*/*",
               "Accept-Language": "en-US,en;q=0.9"}
    if referer:
        headers["Referer"] = referer
    return creq.get(url, headers=headers, timeout=timeout,
                    allow_redirects=True, impersonate="chrome")


def upstream_stream(url, referer=None, rng=None, timeout=30):
    """Streaming variant for /mq child proxying."""
    headers = {"User-Agent": UA, "Accept": "*/*"}
    if referer:
        headers["Referer"] = referer
    if rng:
        headers["Range"] = rng
    return creq.get(url, headers=headers, timeout=timeout, stream=True,
                    allow_redirects=True, impersonate="chrome")


# ------------------------------------------------------- MQ-HLS resolver ---
_JUICY_SYMBOLS = ["`", "%", "-", "+", "*", "$", "!", "_", "^", "="]


def _juicy_decode(blob):
    """Port of the site's _juicycodes(): base64 -> symbol-map digits ->
    4-digit groups -> chr(group % 1000 - salt); salt = last 3 chars
    (each ord()-100).  Returns the JWPlayer config JS/JSON."""
    salt = int("".join(str(ord(c) - 100) for c in blob[-3:]))
    body = blob[:-3]
    # site JS: replace(/_/g,"+").replace(/-/g,"/") then a base64 loop on
    # the STANDARD alphabet that simply skips characters outside it.
    t = re.sub(r"[^A-Za-z0-9+/=]", "",
               body.replace("-", "+").replace("_", "/"))
    s = base64.b64decode(t + "=" * (-len(t) % 4)).decode("latin-1")
    digits = "".join(
        str(_JUICY_SYMBOLS.index(c)) if c in _JUICY_SYMBOLS else "0"
        for c in s)
    return "".join(chr(int(digits[i:i + 4]) % 1000 - salt)
                   for i in range(0, len(digits) // 4 * 4, 4))


_EMB_RE    = re.compile(r'<iframe[^>]+src="([^"]*argon\.razorshell\.space[^"]*)"')
_BLOB_RE   = re.compile(r'_juicycodes\(\s*((?:"[A-Za-z0-9+/=_-]{1,}"\s*\+\s*)+'
                        r'"[A-Za-z0-9+/=_-]{1,}")\s*\)')
_MASTER_RE = re.compile(r'"file":"(https:[^"]+\.m3u8)"')
_WALL_RE   = re.compile(r'data-href="([^"]+)"')

_WALK_SEM   = threading.Semaphore(3)   # codedew rate-limits parallel walks
_hls_cache  = {}                       # zipper -> (expires, master, embed)
_hls_lock   = threading.Lock()
_mqres_cache = {}                      # master URL -> (expires, "1080p")
_RES_RE = re.compile(r"(?i)(?<![0-9x])(2160|1080|720|480|360)\s*p(?![0-9])")
_MASTER_RES_RE = re.compile(r"RESOLUTION=\d+x(\d+)", re.I)


def _res_label(text):
    """'...1080p...' / '4k (Untouched) 17 GB' -> '1080p' / '2160p'."""
    t = text or ""
    m = _RES_RE.search(t)
    if m:
        return f"{m.group(1)}p"
    if re.search(r"(?i)(?<![a-z0-9])4k(?![a-z0-9])", t):
        return "2160p"
    return ""


def _master_quality(master):
    """Highest variant height of an MQ master playlist, cached 6 h.
    Only called inside an already-paid time window (card resolve /
    play rewrite) so cards never wait an extra second for it."""
    now = time.time()
    with _hls_lock:
        hit = _mqres_cache.get(master)
    if hit and hit[0] > now:
        return hit[1]
    q = ""
    try:
        r = upstream_get(master, referer=ARGON, timeout=5)
        if r.status_code == 200:
            hs = [int(h) for h in _MASTER_RES_RE.findall(r.text or "")]
            if hs:
                q = f"{max(hs)}p"
    except Exception:
        q = ""
    with _hls_lock:
        _mqres_cache[master] = (now + (6 * 3600 if q else 1800), q)
    return q

# ---- stale-while-revalidate infra -----------------------------------------
# Cards must ALWAYS show: a transient upstream failure may never remove a
# previously-playable card.  So caches keep their last-good value forever;
# reads past the fresh window serve the stale value instantly and refresh
# in the background (deduped).  Play time (/mq/...) still re-resolves in
# the fresh window, so the player never gets an expired signed master.
_bg_lock     = threading.Lock()
_bg_inflight = set()


def _bg_once(key, fn):
    """Run fn() in a daemon thread, deduped per key while running."""
    with _bg_lock:
        if key in _bg_inflight:
            return
        _bg_inflight.add(key)

    def _wrap():
        try:
            fn()
        except Exception:
            pass
        finally:
            with _bg_lock:
                _bg_inflight.discard(key)

    threading.Thread(target=_wrap, daemon=True).start()


def _zipper_walk(zipper, deadline):
    """Follow codedew's 3-step 'Security Scan' wall.  Each wall page has
    a goBtn data-href; the NEXT hop only resolves when the cookies set on
    the first response are resent - hence one cookie Session.  Returns
    (final_text, argon_embed_or_None)."""
    sess = creq.Session(impersonate="chrome")
    prev, url, text = SITE, zipper, ""
    for _ in range(WALK_HOPS):
        if deadline and time.monotonic() > deadline:
            return text, None
        with _WALK_SEM:                     # global throttle: ONE fetch per hop
            r = sess.get(url, headers={"User-Agent": UA, "Accept": "*/*",
                                       "Accept-Language": "en-US,en;q=0.9",
                                       "Referer": prev},
                         timeout=RESOLVE_TIMEOUT, allow_redirects=True)
        text = r.text or ""
        m = _EMB_RE.search(text)
        if m:
            return text, m.group(1)
        hop = _WALL_RE.search(text)
        if not hop:
            return text, None               # e.g. hubcloud download drive
        prev, url = url, hop.group(1).replace("&amp;", "&")
        if url.startswith("/"):
            url = "https://codedew.com" + url
    return text, None


_walk_locks = {}
_walk_locks_g = threading.Lock()


def _walk_lock_for(z):
    with _walk_locks_g:
        l = _walk_locks.get(z)
        if l is None:
            l = _walk_locks[z] = threading.Lock()
        return l


def _optimistic_zipper(zippers):
    """First candidate that is not known-dead: lets a card show instantly;
    the real resolve happens at play time (and is already warming)."""
    now = time.time()
    for z in zippers[:3]:
        if not z.startswith("https://codedew.com/"):
            continue
        with _hls_lock:
            h = _hls_cache.get(z)
        if h and not h[1] and h[0] > now:
            continue                       # inside negative window: dead
        return z
    return None


def _mq_resolve(zipper, stale_ok=False):
    """zipper -> (master_m3u8_url, embed_url).  Wall -> argon iframe ->
    embed page -> juicy blob -> JWPlayer config.

    stale_ok=False (PLAY time): fresh window only (HLS_TTL, 30 min) - a
    signed master past its window is re-walked so the player never gets
    an expired URL.  stale_ok=True (CARD LISTING): any last-good master
    is served instantly and refreshed in the background; a fresh-walk
    failure keeps the stale value instead of negative-caching it, so an
    existing card can never disappear because of a transient error."""
    now = time.time()
    with _hls_lock:
        hit = _hls_cache.get(zipper)
    if hit:
        exp, master, embed = hit
        if master and (exp > now or stale_ok):
            if exp <= now:                       # stale serve -> refresh
                _bg_once(("mq", zipper),
                         lambda: _mq_resolve(zipper))
            return master, embed
        if not master and exp > now:
            return None, None                    # inside negative window
    # ONE walk per zipper at a time: the card resolver and the player used
    # to walk the same zipper in parallel (double work, semaphore starved)
    with _walk_lock_for(zipper):
        with _hls_lock:
            hit2 = _hls_cache.get(zipper)
        if hit2 and hit2 is not hit and hit2[0] > time.time():
            return hit2[1], hit2[2]            # another thread just finished
        return _mq_walk(zipper, hit)


def _mq_walk(zipper, hit):
    now = time.time()
    embed = master = None
    deadline = time.monotonic() + WALK_BUDGET
    try:
        _, embed = _zipper_walk(zipper, deadline)
        if embed and time.monotonic() < deadline:
            ep = upstream_get(embed, referer=zipper).text or ""
            b = _BLOB_RE.search(ep)
            if b:
                blob = "".join(re.findall(r'"([A-Za-z0-9+/=_-]*)"', b.group(1)))
                mm = _MASTER_RE.search(_juicy_decode(blob))
                if mm:
                    master = mm.group(1).replace("\\/", "/")
    except Exception:
        pass
    if master:
        with _hls_lock:
            _hls_cache[zipper] = (now + HLS_TTL, master, embed)
        return master, embed
    if hit and hit[1]:                           # keep the card alive
        _bg_once(("mq", zipper), lambda: _mq_resolve(zipper))
        return hit[1], hit[2]
    with _hls_lock:
        _hls_cache[zipper] = (now + NEG_TTL, None, None)
    return None, None


# Opaque tokens: every upstream URL that appears in a link we hand out is
# encrypted + authenticated with a server-side key, so nobody can decode a
# /mq/... link back to the source site or CDN.  Key = TOKEN_SECRET env var,
# else derived from SQL_URL / ADMIN_KEY (stable across restarts), else random.
_TK = hashlib.sha256((os.environ.get("TOKEN_SECRET") or os.environ.get("SQL_URL")
                      or os.environ.get("ADMIN_KEY") or secrets.token_hex(32)).encode()).digest()


def _seal(text):
    plain = text.encode()
    tag = hmac.new(_TK, b"t" + plain, hashlib.sha256).digest()[:12]
    ks = b"".join(hmac.new(_TK, tag + i.to_bytes(4, "big"), hashlib.sha256).digest()
                  for i in range(len(plain) // 32 + 1))
    ct = bytes(a ^ b for a, b in zip(plain, ks))
    return base64.urlsafe_b64encode(tag + ct).decode().rstrip("=")


def _unseal(token):
    try:
        raw = base64.urlsafe_b64decode(token + "=" * (-len(token) % 4))
        tag, ct = raw[:12], raw[12:]
        ks = b"".join(hmac.new(_TK, tag + i.to_bytes(4, "big"), hashlib.sha256).digest()
                      for i in range(len(ct) // 32 + 1))
        plain = bytes(a ^ b for a, b in zip(ct, ks))
        good = hmac.new(_TK, b"t" + plain, hashlib.sha256).digest()[:12]
        return plain.decode() if hmac.compare_digest(tag, good) else ""
    except Exception:
        return ""


_mq_token, _mq_decode_token = _seal, _unseal


# ------------------------------------------------- WatchNow direct source --
# A codedew "WatchNow" button opens the site's own VidStack player page.
# The page embeds  playerSources = [{url: <worker-wrapped signed file>,
# name: V1|V2, type: fsl|10gbps}, ...]  - DIRECT download URLs (R2-S3
# signed ~8h, googleusercontent) that answer Range with 206.  That is
# how other addons play WatchNow server-side.  One WatchNow zipper per
# language lives on the movie hub.
_PSRCS_RE = re.compile(r"(?:var|const|let)\s+playerSources\s*=\s*"
                       r"(\[.*?\]);\s*(?:\n|var|const|let|function)", re.S)
_wn_cache = {}                            # zipper -> (expires, direct_url)


def _wn_inner(u):
    """worker-lingering.../<b64> wraps {"url": <signed storage URL>} -
    unwrap so the player gets the storage URL itself.  The /wn proxy
    pipe starves on Untouched bitrates (12-40 Mbps -> MB burn, no
    playback, frozen seeks); the storage endpoint serves byte-ranges at
    full speed with no special headers (UA alone suffices, proven), so
    the client downloads and seeks DIRECTLY - that is how other addons
    play WatchNow."""
    try:
        if "workers.dev/" in u:
            b64 = u.split("workers.dev/", 1)[1].split("?")[0].strip("/")
            j = json.loads(base64.urlsafe_b64decode(
                b64 + "=" * (-len(b64) % 4)))
            inner = j.get("url") or ""
            if inner.startswith("https://"):
                return inner
    except Exception:
        pass
    return u


def _wn_resolve(zipper, stale_ok=False):
    """WatchNow page -> (direct_url, kind) or (None, None).  kind:
    "fsl" = R2 signed storage (honours byte-ranges -> hand DIRECT to
    the player); "10g" = googleusercontent (IGNORES Range - serves the
    whole 0.8-17GB file with 200 -> must go through our /wn proxy so
    the client still gets 206 slices).  Same stale-while-revalidate
    contract as _mq_resolve; stale capped at WN_STALE (signed links
    expire ~8h)."""
    now = time.time()
    with _hls_lock:
        hit = _wn_cache.get(zipper)
    if hit:
        exp, url, kind = hit
        if url and (exp > now or (stale_ok and now - exp < WN_STALE)):
            if exp <= now:                       # stale serve -> refresh
                _bg_once(("wn", zipper),
                         lambda: _wn_resolve(zipper))
            return url, kind
        if not url and exp > now:
            return None, None                    # inside negative window
    url = kind = None
    try:
        text, _ = _zipper_walk(zipper,
                               deadline=time.monotonic() + WALK_BUDGET)
        mm = _PSRCS_RE.search(text or "")
        if mm:
            srcs = json.loads(mm.group(1).replace("\\/", "/"))
            for want, k2 in (("fsl", "fsl"), ("10gbps", "10g")):
                for s in srcs:
                    if (s.get("type") == want
                            and s.get("url", "").startswith("http")):
                        url, kind = _wn_inner(s["url"]), k2
                        break
                if url:
                    break
            if not url and srcs and srcs[0].get("url", "").startswith("http"):
                url = _wn_inner(srcs[0]["url"])
                kind = "fsl" if "cloudflarestorage" in url else "10g"
    except Exception:
        url = kind = None
    if url:
        # googleusercontent (10g) links carry no signature/expiry params
        # and die unpredictably -> short fresh window so PLAY time
        # (always fresh-resolved through /wn) never gets a dead one
        with _hls_lock:
            _wn_cache[zipper] = (now + (WN_TTL if kind == "fsl" else 300),
                                 url, kind)
        return url, kind
    if hit and hit[1] and now - hit[0] < WN_STALE:   # keep the card alive
        _bg_once(("wn", zipper), lambda: _wn_resolve(zipper))
        return hit[1], hit[2]
    with _hls_lock:
        _wn_cache[zipper] = (now + NEG_TTL, None, None)
    return None, None


def _resolve_wn(cands, budget=LIST_BUDGET, wait=None):
    """{lang: [(watchnow-zipper, qn)]} -> {lang: (direct_url, kind, zipper, qn)}.
    R2 (fsl) pages win; google (10g) is the fallback."""
    out = {}
    if not cands:
        return out
    deadline = time.monotonic() + budget
    jd = time.monotonic() + (budget if wait is None else wait)
    lock = threading.Lock()

    def _run(lang, zippers):
        fb = None
        for z, qn in zippers[:3]:
            if time.monotonic() > deadline:
                return
            u, kind = _wn_resolve(z, stale_ok=True)
            if not u:
                continue
            if kind == "fsl":
                with lock:
                    out[lang] = (u, kind, z, qn)
                return
            if fb is None:
                fb = (u, kind, z, qn)
        if fb:
            with lock:
                out[lang] = fb

    threads = [threading.Thread(target=_run, args=(l, zs), daemon=True)
               for l, zs in cands.items()]
    for t in threads:
        t.start()
    for t in threads:
        t.join(max(0.02, jd - time.monotonic()))
    with lock:
        return dict(out)

# --------------------------------------------------------- live freshness --
_EP_POS_RE = re.compile(r"Episode\s*0*(\d{1,3})", re.I)
_LANG_ZIP_RE = re.compile(
    r"color:\s*#[0-9a-fA-F]+;?[^>]*>\s*([A-Za-z][A-Za-z ]{1,18})"
    r"\s*</span>[^<]{0,60}?<a[^>]+href=\"([^\"]*codedew\.com/zipper[^\"]*)\"",
    re.S)
_HUB_ZIP_RE = re.compile(r'href="(https://codedew\.com/zipper/\?url=[^"]+)"')
_LIVE_LANGS = ("Hindi", "Tamil", "Telugu", "English", "Japanese",
               "Bengali", "Malayalam", "Urdu")
# movie-hub source buttons (user request): ONLY WatchMultiQuality and
# WatchNow are wanted; Download-labelled links stay as last-resort
# because some real players (e.g. Shinchan Bengali) carry that label;
# HubCloud/DLBeta/Mega/MediaFire/4k/GB rows are download-only: dropped.
_BTN_W = {"watchmultiquality": 0, "watchnow": 1, "download": 2}
_ALL_BTN_RE = re.compile(
    r'href="(https://codedew\.com/zipper/\?url=[^"]+)"[^>]*>'
    r"\s*([A-Za-z0-9 ]+?)\s*<", re.S)

_ICONS = {"icon-192.png": "iVBORw0KGgoAAAANSUhEUgAAAMAAAADACAIAAADdvvtQAAAE4UlEQVR4nO3dwY0USRCF4ZwVtzlwXgxAWhvWgLUZA7ABCQMWN/ZQUqm2B4buflUZ70X+3xmhypi/I4sZBC+vrx8H8Kw/qh8A2QgIEgKChIAgISBICAgSAoKEgCAhIEgICBICgoSAICEgSAgIEgKChIAgISBICAgSAoKEgCAhIEgICBICgoSAICEgSAgIEgKChIAgISBICAgSAoKEgCAhIEgICBICgoSAICEgSD5UP4CL73//+dCv//z1x0VPkuVl2X/m99Fi3rdsT2sFdG40v7JUTEsENKebt1YoqXlAVekc9c6oZ0AO3bzVsqRuAXmmc9Qso1bfB/KvZ4Q85P2abKDEr0qPVRQfUGI6R+kZZV9h6fWM/CMEB5Q++l30QSKvsOiJvyPxOsvbQF3rGZlHCwsoccQPiTtgUkBxw31O1jFjAsoaqyjosBkBBQ30LClHDggoZZSnizi4e0ARQ7yO//GtA/If3wTmQ/ANyHxwMzmPwjQg55GVsB2IaUBI4RiQ7aetludY7AK6ekyfvny79Pe/lGFDXgHNGdCnL99yM3JryCugmXIbsmIU0PzPVugqslpCRgFVCc3IhEtA5Z+qrIbKx7WzCMhkHFmryGRoFgFZCWrIQX1AJp+ko5RV5DC6+oBspWRUi4B+g4beVxyQwxL+LedVVD5ANtC9nDMqVBlQ+afnCYYN1Y6RDfQwVtERAT2JjDZlASXeX2+ZNFQ4TDaQavFVREDnWLYhAjrNmquoJqAeL0A/VZVR1UjZQJdYZxUR0FUWudEI6FrtMyKgGRo3VBBQ4zfod0xYRSWDZQNN1e9GI6ACnRoioBptVhEBVWrQEAEVS19FBGQhNyMCMpLYEAF5iVtFH6ofAP/z7z9/VT/CY9hARuLqGWwgE4npbAioWG46G66wSun1DDZQlQbpbAhotjbpbAoC+vz1x5p/JejqdEr+02fegSZptnh2XGGX65rOhoAu1DudDVfYVVaoZ1RtoN7v0SXplLxBD66wcy2ydY64wk6zYD2DDXSKNdPZlAXU4zXIJJ2qF6DBFaYwqacWV9gzSGdXGVDiLWaYTuH9NbjCHmJYT7niKyxlCdmmU7t+RnlA/mzTMUFAv0Q696h/Bypfwj8VUY/D6NhAtyLS8WERkMmrdFY6DutnOFxhm/JxUM9zLDZQrax03BgFNP8iC03HZ/0MnytsvtB63BhtoDFrCUWnY7V+xhgvr68fq5/hlsOfyDy51TM8rzDDMTnwHItjQAhiGpDnp62Q7UBMAxrGI5vPeRS+AQ3vwU1jPgTrgIb9+K7mf3z3gEbCEC8ScfCAgEbIKM+VcuSMgEbOQE8RdNiYgEbUWBVZx0wKaKQN9wlxBwwLaASO+H6JR3P8YeqdOv3MNTGdTd4G2uUO/Ub0QYIDGuGj36QfIfgKO0q8ztLT2TQJaJOSUY90NtlX2I2IL0zEQ96v1Qbaea6iZulsega0cyipZTe75gFtqjLqnc5miYB2c0paoZvdWgEdnRvTUtEcrRvQjUd7WraYGwQESavvA2E+AoKEgCAhIEgICBICgoSAICEgSAgIEgKChIAgISBICAgSAoKEgCAhIEgICBICgoSAICEgSAgIEgKChIAgISBICAgSAoKEgCAhIEgICBICgoSAICEgSAgIEgKChIAgISBICAiS/wAopWLEgEoGGwAAAABJRU5ErkJggg==",
          "icon-512.png": "iVBORw0KGgoAAAANSUhEUgAAAgAAAAIACAIAAAB7GkOtAAAN5UlEQVR4nO3dwW0dxxKGUUrwjgut7QAMvBgUwIvZATgGAwrATuMtJDxT0iV570xPd1f95wRgEFB3fVNNCf7w/PzpCYA8H1f/AACsIQAAoQQAIJQAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQv6z+AeAqXz7/OuS/8/uf/wz578BuPjw/f1r9M8Bxo6b8MdpAaQJAGWtn/f1UgSoEgH1Vmfhv0wO2JQDspcfQf40YsBUBYL3eQ/81YsByAsAymXP/Z0rAKgLAbOb+a5SAyQSAScz9+ykBcwgA1zL3z1ACLiUAXMLcH0sJuIIAMJjRfx0ZYCwBYAxzfyYlYAgB4CyjfxUZ4CQB4DijfwcywGECwBFG/25kgAMEgMcY/TuTAR4iANzL6K9CBriTAPA+o78iGeBdAsBbjP7qZIA3CAC3Gf2dyAA3fVz9A7Aj078Zf6DcZAPgOyZFb1YBXhIAvjH6c8gAX3kC4unJ9A/jj5uvbADpzIJkVoFwNoBopn84ByCcDSCUm89LVoFMNoBEpj8/cCQyCUAcV52bHIxAnoCCuOHcw3NQDhtACtOfOzkqOQQggivNQxyYEJ6AmnOTOcNzUG82gM5Mf05yhHoTgLZcXYZwkBoTgJ5cWgZynLryO4Bu3FWu41cCzdgAWjH9uZQD1owA9OFyMoFj1okANOFaMo3D1oYAdOBCMpkj14MAlOcqsoSD14AA1OYSspDjV50AFOb6sZxDWJoAVOXisQlHsS4BKMmVYysOZFECUI/LxoYcy4oEoBjXjG05nOUIQCUuGJtzRGsRgDJcLUpwUAsRgBpcKgpxXKsQgAJcJ8pxaEsQgN25SBTl6O5PAABCCcDWfENRmgO8OQHYl8tDA47xzgRgU64NbTjM2xKAHbkwNONI70kAAEIJwHZ8K9GSg70hAdiLS0JjjvduBGAjrgftOeRbEQCAUAKwC19GhHDU9yEAW3AliOLAb0IA1nMZfvvjr9U/ArM59jsQALbw2x9/yQBMJgCL+Q56SQOiOPzLCcBKLsDPrAJRXIG1BIAdaQBMIADL+PZ5m1UghIuwkACs4dDfSQYSuA6rCAAFaABcQQAW8L1zgFWgN5diCQGgEhmAgQRgNl8652lAS67GfAIwlSM+ilWgJRdkMgGgMA2AMwRgHl83V7AKNOOazCQAdCADcIAATOK7ZgIN6MFlmUYAaMUqAPcTgBl80UwmA9W5MnMIAG1pALxNAC7nW2Yhq0BdLs4EAkB/GgA3CcC1fMVswipQketzNQEgiAzASwJwId8ve9KAQlyiSwkAiawC8CQA1/Hlsj8ZKMFVuo4AkE4DiCUAl/DNUotVYHMu1EUEAL7RANIIAPzLKkAUARjPulqdDGzItbqCAMBtGkB7AjCY75ROrAJbcbmGEwB4hwzQlQDAXTSAfgRgJCtqb1aB5VyxsQQAHqMBtCEA8DCrAD0IwDCW0zQysISLNpAAwCkaQF0CAGdZBShKAMawliID07huowgAjKQBFCIAMJhVgCoEYAALKT/TgEu5dEMIAFzFKsDmBACuJQNsSwDOsopyDw0YztU7TwBgEqsAuxEAmEoG2IcAwAIawA4E4BSvkBxmFTjPBTxJAGAlDWAhAYDFrAKsIgCwBRlgPgE4zvsjw2nAo1zDMwQA9mIVYBoBgB3JABMIAOxLA7iUAMDWrAJcRwAO8qsnZtKAN7iMhwkA1GAVYDgBgEpkgIEEAOrRAIYQACjJKsB5AgCFyQBnCACUpwEcIwBH+Gtn7CZ8FXAljxEA6CO5ARwgANBK+CrAQwQAGpIB7iEA0JYG8DYBgM6sArxBAKA/GeAmAYAUGsAPBACCWAV4SQAe5p+cUF3LBriYBwgAJLIK8CQAkEwGwgkApNOAWAIAWAVCCQDwjQykEQDgOxqQQwCAH1kFQggAcJsGtCcAwKusAr0JAPAOGehKAIC7aEA/AgDcyyrQzC+rfwCgjL//+5/VPwIj2QCAu5j+/dgAgHcY/V0JAPAqo783T0DAbaZ/ezYA4EdGfwgBAP5l9EfxBAR8Y/qnsQEARn8oGwCkM/1j2QAgl9EfTgAe9vuf/3z5/OvqnwJO6Tf6f//zn9U/Qj2egCBOv+nPMTYACGL085IAQASjn595AoL+TH9usgFAZ0Y/bxAA6Mno512egKAh05972ACgFaOf+wnAEf4tGBtKHv3+FdgxnoCgg+Tpz2E2AKjN6OcwGwAUZvpzhg0ASjL6OU8AoBijn1E8AUElpj8D2QAO8jdBmczof42/A3qYAMDujH4u4gkItmb6cx0bAGzK6OdqAgDbMfqZwxPQcX71xBVM/4e4hmfYAGAXRj+TCQCsZ/SzhCcgWMz0ZxUbwCn+ORhnGP0n+QXASTYAWMP0ZzkbAMxm9LMJAYB5jH624gnoLK+Q3Mn0H8vVO88GAJcz+tmTAMCFjH525gloAKsoN5n+13HphrABwHhGPyUIAIxk9FOIJ6AxLKQ8mf6zuG6j2ABgAKOfigQATjH6qcsT0DDW0kCm/3wu2kA2ADjC6KcBGwA8zPSnBxvASP73AO0Z/Wt5/xlLAOAuRj/9eAKC95n+tGQDGMwrUDNG/z68/wwnAHCb0U97noDG853SgOm/G9fqCjYA+I7RTw4BgG+MftJ4ArqEdbUc039nLtRFbACkM/qJJQBX8fdB92f0l+Dz/zqegAhl+oMN4EKWgD0Z/YX4/L+UDYAspj/8nw3gWpaAfRj95fj8v5oA0J/RDzd5Arqcr5i1TP+iXJwJbAC0ZfTD2wRgBr8JmMzor87n/xyegOjG9Ic72QAmsQRMYPT34PN/GgGgA6MfDvAENI/vmouY/p24JjPZACjM6IczBGAqvwkYxehvyef/ZJ6AZnPEzzP9W3I15rMBUInRDwPZABbwpXOM6d+YS7GEDYACjH64ggCs4bfBdzL6E/j8X8UT0DIO/btM/wQuwkI2AHZk9MMEArCSh6CfGf1RfP6v5QloMRfgJdM/isO/nA2ALRj9MN+H5+dPq38GnjwEkcbn/w48AW3BZSCKA78JAdiFK0EIR30fAgAQSgA24suI9hzyrQjAXlwPGnO8dyMA23FJaMnB3pAAAIQSgB35VqIZR3pPArApF4Y2HOZtCcC+XBsacIx3JgBbc3kozQHenAAAhBKA3fmGoihHd38CUICLRDkObQkCUIPrRCGOaxUCUIZLRQkOaiECUImrxeYc0VoEoBgXjG05nOUIQD2uGRtyLCsSgJJcNrbiQBYlAFW5cmzCUaxLAApz8VjOISxNAGpz/VjI8atOAMpzCVnCwWtAADpwFZnMketBAJpwIZnGYWtDAPpwLZnAMetEAFpxObmUA9bMh+fnT6t/Bsb78vnX1T8CrRj9LdkAenJdGchx6koA2nJpGcJBakwAOnN1OckR6s3vACL4lQCPMvoT2AAiuMw8xIEJIQApXGnu5Kjk8AQUx3MQrzH609gA4rjk3ORgBBKARK46P3AkMnkCiuY5CKM/mQ0gmssfzgEIZwPg6ckqkMfo58kGwFfGQRR/3HxlA+A7VoHejH5eEgBukIF+jH5+5gmIGwyLZvyBcpMNgLdYBaoz+nmDAPA+GajI6OddAsC9ZKAKo587CQCPkYGdGf08RAA4QgZ2Y/RzgABwnAzswOjnMAHgLBlYxejnJAFgDBmYyehnCAFgMCW4jrnPWALAJWRgLKOfKwgA11KCM8x9LiUATKIE9zP3mUMAmE0JXmPuM5kAsIwSfGXus4oAsF5mCcx9lhMA9tI7BoY+WxEA9tUjBoY+2xIAyqjSAxOfKgSA2tZWwaynNAGgrVFtMOXpSgAAQn1c/QMAsIYAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQAgAQSgAAQgkAQCgBAAglAAChBAAglAAAhBIAgFACABBKAABCCQBAKAEACCUAAKEEACCUAACEEgCAUAIAEEoAAEIJAEAoAQAIJQAAoQQAIJQAAIQSAIBQAgAQSgAAQv0P6nyfXtcI938AAAAASUVORK5CYII="}

_live_cache = {}                          # hub -> (expires, rows)
_live_lock = threading.Lock()


def _live_rows(rec):
    """Re-parse the show's hub page on the site - the freshness path:
    brand-new episodes AND rotated movie zippers appear without a
    redeploy.  Episode hubs expose <color span>Language</span><a zipper>;
    movie hubs expose 'Hindi - Download' / 'Tamil - [ WatchMultiQuality ]'
    button blocks (HubCloud/DLBeta/4k/GB rows are download-only: skip)."""
    hub = rec.get("hub")
    if not hub:
        return []
    now = time.time()
    with _live_lock:
        hit = _live_cache.get(hub)
        if hit and hit[0] > now:
            return hit[1]
    rows = []
    try:
        page = upstream_get(hub, referer=SITE).text or ""
        if rec.get("movie"):
            # every zipper with its button label, in document order;
            # language = the nearest preceding <h4> heading ("Hindi -
            # Download" style sections).  A fixed look-back window fails:
            # WatchNow sits 3+ buttons deep and markup pushes the
            # heading out of reach.  QUALITY headings ("(Untouched)
            # 4.63 GB", "4k (Untouched) 17 GB") are the SAME movie's
            # size variants -> they INHERIT the running language; any
            # other non-language h4 ("Watch Also", "Recommended", ...)
            # RESETS it so foreign buttons are never mis-assigned.
            _quality_head = re.compile(
                r"(?i)\b(?:4k|\d+(?:\.\d+)?\s*(?:gb|mb)|untouched|"
                r"1080p?|720p?|480p?|blu[- ]?ray|web[- ]?dl|hd)\b")
            heads = []
            cur = None
            cur_q = ""
            for hm in re.finditer(r"<h4[^>]*>(.*?)</h4>", page, re.S):
                htxt = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", hm.group(1)))
                lang = next((L for L in _LIVE_LANGS
                             if re.search(rf"\b{L}\b", htxt, re.I)), None)
                if _quality_head.search(htxt):
                    cur_q = htxt          # "(Untouched) 4.63 GB" annotates
                if lang:                  #   the buttons that follow it
                    cur = lang
                    cur_q = ""            # new language section resets
                elif not _quality_head.search(htxt):
                    cur = None
                    cur_q = ""
                heads.append((hm.start(), cur, cur_q))
            heads.sort()

            def _lang_at(pos):
                lang = q = None
                for hpos, hlang, hq in heads:
                    if hpos <= pos:
                        lang, q = hlang, hq
                    else:
                        break
                return lang, (q or "")

            cands = []
            for mm in _ALL_BTN_RE.finditer(page):
                label = mm.group(2).strip().lower()
                if label not in _BTN_W:
                    continue          # HubCloud/DLBeta/Mega/MediaFire/...
                lang, qn = _lang_at(mm.start())
                if lang:
                    cands.append((_BTN_W[label], lang, mm.group(1), label,
                                  qn))
            # dedupe per language, priority order, max 3 candidates
            best = {}
            for w, lang, url, label, qn in sorted(cands):
                lst = best.setdefault(lang, [])
                if all(u != url for u, _l, _q in lst) and len(lst) < 3:
                    lst.append((url, label, qn))
            for lang, pairs in best.items():
                for u, label, qn in pairs:
                    rows.append({"show": rec["site_name"], "season": 0,
                                 "episode": 1, "ep_title": "", "lang": lang,
                                 "hub_url": hub, "mq": u, "sb": "",
                                 "btn": label, "qn": qn})
        else:
            eps = [(mm.start(), int(mm.group(1)))
                   for mm in _EP_POS_RE.finditer(page)]
            for lm in _LANG_ZIP_RE.finditer(page):
                ep = 0
                for pos, n in eps:
                    if pos < lm.start():
                        ep = n
                    else:
                        break
                if ep:
                    rows.append({"show": rec["site_name"], "season": None,
                                 "episode": ep, "ep_title": "",
                                 "lang": lm.group(1).strip(), "hub_url": hub,
                                 "mq": lm.group(2), "sb": ""})
            # series WatchNow buttons (one per episode x language):
            # episode = nearest preceding "Episode N" anchor, language =
            # nearest preceding language span, else the hub slug language
            _dl = next((w.title() for w in ("hindi", "tamil", "telugu",
                                            "bengali", "english")
                        if w in (rec.get("site_name") or "").lower()), "Hindi")
            for mm in _ALL_BTN_RE.finditer(page):
                if mm.group(2).strip().lower() != "watchnow":
                    continue
                ep = 0
                for pos, n in eps:
                    if pos < mm.start():
                        ep = n
                    else:
                        break
                if not ep:
                    continue
                lang = None
                for lpos, l in [(x.start(), x.group(1).strip())
                                for x in _LANG_ZIP_RE.finditer(page)]:
                    if lpos < mm.start():
                        lang = l
                    else:
                        break
                rows.append({"show": rec["site_name"], "season": None,
                             "episode": ep, "ep_title": "",
                             "lang": lang or _dl, "hub_url": hub,
                             "mq": mm.group(1), "sb": "",
                             "btn": "watchnow"})
            # SECOND PARSER (same one the crawler used for the index): the
            # regexes above only know the <span color>Lang</span><a> layout,
            # so episodes written in other layouts (one-line "Episode 09 -
            # Title  Hindi - [ WatchMultiQuality ]", headings, S01E09 ...)
            # were silently dropped -> list stopped at ep 8 while ep 9+
            # existed.  Union both, dedupe by (episode, lang, link).
            try:
                import parse_hubs as _PH
                seen_k = {(r.get("episode"), r.get("lang"), r.get("mq"))
                          for r in rows}
                for r in _PH.parse_html(page, hub, rec["site_name"], None):
                    if not r.get("episode") or not (r.get("mq") or r.get("sb")):
                        continue
                    k = (r["episode"], r.get("lang"), r.get("mq"))
                    if k in seen_k:
                        continue
                    seen_k.add(k)
                    rows.append({"show": rec["site_name"], "season": None,
                                 "episode": r["episode"],
                                 "ep_title": r.get("ep_title") or "",
                                 "lang": r.get("lang") or _dl,
                                 "hub_url": hub, "mq": r.get("mq") or "",
                                 "sb": r.get("sb") or ""})
            except Exception as e:
                print("[live] bs4 parse failed:", e, flush=True)
    except Exception:
        rows = []
    with _live_lock:
        _live_cache[hub] = (now + (LIVE_TTL if rows else LIVE_NEG), rows)
    return rows


def _absorb_live(rec, live_rows, season=None):
    """Merge live hub rows into rec['eps'] live-first: rotated zippers get
    replaced by fresh ones and unseen episodes become visible."""
    if not live_rows:
        return
    buckets = {}
    for r in live_rows:
        if rec["movie"]:
            key = (0, 1)
        else:
            s0 = season or r.get("season")
            if not s0:
                seasons = [k[0] for k in rec["eps"] if k[0]]
                s0 = min(seasons) if seasons else 1
            key = (s0, r.get("episode") or 1)
        r["season"] = key[0]
        buckets.setdefault(key, []).append(r)
    with STORE_LOCK:
        for key, rs in buckets.items():
            langs = {r.get("lang") for r in rs}
            old = rec["eps"].get(key, [])
            # fresh candidates first (document order = resolve tries them
            # in sequence), then untouched leftovers
            rec["eps"][key] = rs + [o for o in old
                                    if o.get("lang") not in langs]


def _resolve_picks(picks, done=None, budget=LIST_BUDGET, wait=None):
    """{lang: [zippers]} -> {lang: (master, zipper, quality)}.  One thread
    per language, up to 3 zippers each.  `wait` = how long THIS call blocks
    (threads keep running and fill the caches afterwards)."""
    out = {}
    if not picks:
        return out
    deadline = time.monotonic() + budget
    jd = time.monotonic() + (budget if wait is None else wait)
    lock = threading.Lock()

    def _run(lang, zippers):
        if done and lang in done:
            with lock:
                out[lang] = done[lang]
            return
        for z in zippers[:3]:
            if time.monotonic() > deadline:
                return
            master, _ = _mq_resolve(z, stale_ok=True)
            if master:
                q = (_master_quality(master)
                     if time.monotonic() < deadline - 1 else "")
                with lock:
                    out[lang] = (master, z, q)
                return

    threads = [threading.Thread(target=_run, args=(l, zs), daemon=True)
               for l, zs in picks.items()]
    for t in threads:
        t.start()
    for t in threads:
        t.join(max(0.02, jd - time.monotonic()))
    with lock:
        return dict(out)

# ------------------------------------------------------------------ meta ---
_CINEMETA = "https://v3-cinemeta.strem.io/meta/{t}/{id}.json"
_cine_cache = {}
_cine_lock = threading.Lock()


def _cinemeta_name_once(mtype, ext_id):
    now = time.time()
    key = (mtype, ext_id)
    with _cine_lock:
        hit = _cine_cache.get(key)
        if hit and hit[0] > now:
            return hit[1]
    name = None
    try:
        r = requests.get(_CINEMETA.format(t=mtype, id=ext_id), timeout=6,
                         headers={"User-Agent": UA,
                                  "Accept": "application/json"})
        if r.status_code == 200:
            name = (r.json().get("meta") or {}).get("name")
    except Exception:
        name = None
    with _cine_lock:
        _cine_cache[key] = (now + (CINE_TTL if name else 90), name)
    return name


def _cinemeta_name(mtype, ext_id):
    """Cinemeta occasionally returns an empty/stub body (transient) -
    one immediate retry before giving up, so a search-tap never loses
    its cards to a hiccup."""
    name = _cinemeta_name_once(mtype, ext_id)
    if not name:
        time.sleep(0.4)
        name = _cinemeta_name_once(mtype, ext_id)
    return name


_search_cache = {}                         # (title, want_movie) -> slug


_SEO_SLUG = {"hindi", "dubbed", "dub", "episodes", "episode", "download",
             "hd", "season", "movie", "480p", "720p", "1080p", "2160p",
             "4k", "web", "dl", "hin", "tam", "tel", "ben", "eng", "sub"}


def _slug_is_movie(slug):
    s = (slug or "").lower()
    return "movie" in s and "episodes" not in s


def _ensure_show(slug, hub_url, site_title, cinemeta_name):
    """Create a live show record for a hub that exists on the site but is
    missing from the crawler snapshot (brand-new shows).  Episodes come
    from the usual live-hub parse, so nothing else needs to know."""
    with STORE_LOCK:
        rec = SHOWS.get(slug)
        if rec:
            return rec
        rec = {"slug": slug,
               "site_name": site_title or slug.replace("_", " ").title(),
               "name": cinemeta_name or site_title
                       or slug.replace("_", " ").title(),
               "movie": _slug_is_movie(slug),
               "poster": "", "hub": hub_url, "eps": {},
               "genres": _TMDB_CACHE.get(slug, {}).get("g", [])}
        SHOWS[slug] = rec
    _bg_once(("poster", slug),
             lambda: _fetch_poster(rec))
    _show_genres(rec)
    return rec


def _fetch_poster(rec):
    """Lazy og:image grab so dynamically-discovered shows get a poster."""
    try:
        if rec.get("poster") or not rec.get("hub"):
            return
        t = upstream_get(rec["hub"], referer=SITE, timeout=10).text or ""
        q = chr(39)
        dd = chr(34)
        og = (re.search(r'property=["' + q + r']og:image["' + q + r']'
                        r'[^>]*content=["' + q + r']([^"' + q + r']+)', t)
              or re.search(r'content=["' + q + r']([^"' + q + r']+)["' + q
                           + r'][^>]*property=["' + q + r']og:image', t))
        if og:
            rec["poster"] = og.group(1).replace(dd + dd, dd)
    except Exception:
        pass


# ------------------------------------------------------------- TMDB ---
# Genres + description.  The crawled index has neither, so we ask TMDB by
# (cleaned) title.  Successful lookups are cached in SQL; failures are NOT
# cached (retried after ~10 min).
_TMDB_GENRE_MAP = {}      # {"tv": {id: name}, "movie": {id: name}}


def _tmdb_get(path, **params):
    params["api_key"] = TMDB_API_KEY
    r = requests.get("https://api.themoviedb.org/3" + path,
                      params=params, timeout=10)
    r.raise_for_status()
    return r.json()


def _tmdb_genre_map(kind):
    """{id: name}.  Only a NON-empty map is remembered; on failure this
    raises so nothing wrong gets cached."""
    m = _TMDB_GENRE_MAP.get(kind)
    if m:
        return m
    j = _tmdb_get(f"/genre/{kind}/list")
    m = {g["id"]: g["name"] for g in j.get("genres", [])}
    if not m:
        raise RuntimeError("empty genre map")
    _TMDB_GENRE_MAP[kind] = m
    return m


def _tmdb_clean(name):
    """'High School DxD Season 1 (Hindi Dub)' -> 'High School DxD'."""
    s = re.sub(r"[\[(][^\])]*[\])]", " ", name or "")
    s = re.sub(r"\b\d+(?:st|nd|rd|th)\s+season\b.*$", " ", s, flags=re.I)
    s = re.sub(r"\b(?:season|part|cour)\s*\d+\b.*$", " ", s, flags=re.I)
    s = re.sub(r"\b(?:final\s+season|hindi|tamil|telugu|bengali|dubbed|dub|subbed|dual\s+audio|multi\s+audio)\b", " ", s, flags=re.I)
    s = re.sub(r"\s+", " ", s).strip(" -:\u2013\u2014|,.")
    return s or (name or "")


def _tmdb_lookup(name, is_movie, anime=True):
    """-> {"v":3,"g":[...],"d":"...","r":8.1,"rs":"mal","t":ts[, "nf":1]}.
    TMDB failures RAISE (caller skips caching).  Jikan failures do not:
    the TMDB data is kept and flagged "jf" so Jikan is retried in 1 h.

    Genres are always normalised through genres.py.  For anime, Jikan
    (MyAnimeList) wins for genres + rating, TMDB fills whatever is
    missing; cartoons use TMDB only."""
    kind = "movie" if is_movie else "tv"
    results = []
    for query in dict.fromkeys([_tmdb_clean(name), name]):
        if not query:
            continue
        results = _tmdb_get(f"/search/{kind}", query=query).get("results") or []
        if results:
            break
    tm = {"g": [], "d": "", "r": None}
    if results:
        top = results[:10]
        anim = [r for r in top if 16 in (r.get("genre_ids") or [])]   # 16 = Animation
        pool = anim or top
        best = next((r for r in pool if r.get("overview")), pool[0])
        ids = best.get("genre_ids") or []
        gm = _tmdb_genre_map(kind) if ids else {}
        tm["g"] = [gm[i] for i in ids if i in gm]
        tm["d"] = (best.get("overview") or "").strip()
        va, vc = best.get("vote_average") or 0, best.get("vote_count") or 0
        if va > 0 and vc >= 5:              # ignore 1-2 vote noise
            tm["r"] = round(float(va), 1)
    mal, jf = None, 0
    if anime:
        try:
            mal = G.jikan_lookup(_tmdb_clean(name), is_movie)
        except Exception as e:
            jf = 1
            print(f"[rt2] jikan lookup FAILED for '{name}': {repr(e)}", flush=True)
    if not results and not mal:
        info = {"v": 3, "g": [], "d": "", "r": None, "t": time.time(), "nf": 1}
        if jf:
            info["jf"] = 1
        return info
    mal_r = round(float(mal["score"]), 1) if mal and mal.get("score") else None
    rating, src = (mal_r, "mal") if mal_r else ((tm["r"], "tmdb") if tm["r"] else (None, ""))
    info = {"v": 3,
            "g": (G.normalize(mal["genres"]) if len(G.normalize(mal["genres"])) >= 3
                  else G.normalize(mal["genres"], tm["g"])) if mal
                 else G.normalize(tm["g"]),
            "d": tm["d"] or (mal or {}).get("synopsis", ""),
            "r": rating, "rs": src, "rt": tm["r"], "rm": mal_r,
            "t": time.time()}
    if jf:
        info["jf"] = 1
    return info


def _tmdb_fresh(hit):
    if not hit or hit.get("v") != 3:      # old/empty entries -> refetch
        return False
    ttl = TMDB_NF_TTL if hit.get("nf") else TMDB_TTL
    if hit.get("jf"):                     # Jikan was down: try again soon
        ttl = min(ttl, JIKAN_RETRY_TTL)
    return time.time() - hit.get("t", 0) < ttl


def _tmdb_refresh(rec):
    """Do one lookup now; on success store it, on failure remember the
    time only in memory (retry in ~10 min).  Returns True on success."""
    slug = rec["slug"]
    try:
        nm = rec.get("name") or rec.get("site_name") or slug
        info = _tmdb_lookup(nm, bool(rec.get("movie")),
                            anime=_kind(nm) == "anime")
    except Exception as e:
        _TMDB_FAIL[slug] = time.time()
        print(f"[rt2] tmdb lookup FAILED for '{slug}': {repr(e)}", flush=True)
        return False
    _TMDB_FAIL.pop(slug, None)
    _tmdb_store(slug, info)
    rec["genres"], rec["desc"], rec["rating"] = info["g"], info["d"], info.get("r")
    return True


_FIN_MEMO = {}


def _show_info(rec, wait=0):
    """_show_info_raw + genres cleaned/topped-up to 6-8 (genres.finalize)."""
    info = _show_info_raw(rec, wait)
    if not info:
        return info
    k = (rec["slug"], info.get("t"))
    g = _FIN_MEMO.get(k)
    if g is None:
        g = _FIN_MEMO[k] = G.finalize(info.get("g"), info.get("d"), info.get("rs"))
    out = dict(info)
    out["g"] = g
    return out


def _show_info_raw(rec, wait=0):
    """Cached {"g","d","r","rs"} for a show.  On a miss starts a background TMDB
    lookup (optionally waits up to `wait` seconds for it)."""
    slug = rec["slug"]
    hit = _TMDB_CACHE.get(slug)
    if _tmdb_fresh(hit):
        return hit
    if time.time() - _TMDB_FAIL.get(slug, 0) < TMDB_RETRY:
        return hit or {}
    done = threading.Event()

    def _run(rec=rec):
        try:
            _tmdb_refresh(rec)
        finally:
            done.set()
    _bg_once(("tmdb", slug), _run)
    if wait:
        done.wait(wait)
    return _TMDB_CACHE.get(slug) or {}


def _show_genres(rec):
    return _show_info(rec).get("g", [])


def _tmdb_backfill():
    """Keeps every show (including newly crawled ones) filled in: checks
    every 10 min for shows with no/stale/old-format cache, paced ~3 req/s."""
    if not TMDB_API_KEY:
        return
    time.sleep(30)
    while True:
        try:
            now = time.time()
            with STORE_LOCK:
                todo = [r for r in SHOWS.values()
                        if not _tmdb_fresh(_TMDB_CACHE.get(r["slug"]))
                        and now - _TMDB_FAIL.get(r["slug"], 0) >= TMDB_RETRY]
            n = 0
            for rec in todo:
                if _tmdb_refresh(rec):
                    n += 1
                time.sleep(0.3)
            if todo:
                print(f"[rt2] tmdb backfill: {n}/{len(todo)} shows updated", flush=True)
        except Exception as e:
            print(f"[rt2] tmdb backfill error: {repr(e)}", flush=True)
        time.sleep(600)


def _site_search_slug(title, want_movie):
    """The site's own WordPress search - the ground truth for its naming
    ("Crayon Shin-chan ..." finds "Shin Chan Movie ..." instantly even
    when Cinemeta's branding defeats the substring matcher).  Returns a
    SHOWS slug or None.  Results are token-scored, best first."""
    now = time.time()
    key = (title, want_movie)
    with _hls_lock:
        hit = _search_cache.get(key)
    if hit and hit[0] > now:
        return hit[1]
    slug = None
    try:
        from urllib.parse import quote_plus
        # query variants: the site's engine returns a "no results" page
        # for long branded phrasings - the post-colon distinctive part
        # usually hits directly.
        variants = [title]
        if ":" in title:
            variants.append(title.rsplit(":", 1)[-1].strip())
        variants = list(dict.fromkeys(v for v in variants if len(v) >= 6))[:3]
        wt = _toks(title)
        best, bs = None, 0.0
        best_href = best_label = ""
        for qv in variants:
            items = []
            for _att in (1, 2):              # CF blips: one retry
                r = upstream_get(f"{SITE}/?s={quote_plus(qv)}",
                                 referer=SITE, timeout=12)
                items = re.findall(
                    r'<h[23][^>]*class="[^"]*entry-title[^"]*"[^>]*>\s*'
                    r'<a[^>]+href="([^"]+)"[^>]*>(.*?)</a>',
                    r.text or "", re.S)
                if items:
                    break
                time.sleep(0.8)
            for href, label in items:
                if "/hindi/" not in href:
                    continue
                cand = href.rstrip("/").rsplit("/", 1)[-1].replace("-", "_")
                rec = SHOWS.get(cand)
                if rec:
                    if bool(rec["movie"]) != want_movie:
                        continue
                    ref = _toks(_base_title(rec))
                else:
                    # brand-new show (not in the crawler snapshot yet):
                    # score against the slug itself, SEO words stripped
                    if _slug_is_movie(cand) != want_movie:
                        continue
                    ref = _toks(cand) - _SEO_SLUG
                shared = wt & ref
                if len(shared) < 3:
                    continue
                s = len(shared) / max(1, min(len(wt), len(ref)))
                if s > bs:
                    best, bs = cand, s
                    best_href, best_label = href, (label or "").strip()
            if best and bs >= 0.5:
                break
        if best and bs >= 0.5:
            slug = best
            if best not in SHOWS and best_href:
                _ensure_show(best, best_href, best_label, title)
    except Exception:
        slug = None
    with _hls_lock:
        _search_cache[key] = (now + (6 * 3600 if slug else 600), slug)
    return slug


_calt_cache = {}


_IMDB_SUG = "https://v2.sg.media-imdb.com/suggestion/{k}/{q}.json"


def _imdb_names(mtype, ext_id):
    """Display titles for ext_id from IMDb's suggestion CDN (no auth,
    reliable) - the ENGLISH name when Cinemeta's meta only carries the
    romaji/original ("Super no ura de yani su futari").  Replaces the
    old cinemeta-search-by-id call, which never matched anything."""
    now = time.time()
    key = (mtype, ext_id)
    with _cine_lock:
        hit = _calt_cache.get(key)
    if hit and hit[0] > now:
        return hit[1]
    alts = []
    try:
        r = requests.get(_IMDB_SUG.format(k=(ext_id[2:3] or "x").lower(),
                                          q=ext_id),
                         timeout=6, headers={"User-Agent": UA,
                                             "Accept": "application/json"})
        if r.status_code == 200:
            alts = [x.get("l") for x in (r.json().get("d") or [])
                    if x.get("id") == ext_id and x.get("l")]
    except Exception:
        alts = []
    with _cine_lock:
        _calt_cache[key] = (now + (6 * 3600 if alts else 1200), alts)
    return alts


def _norm_title(text):
    return re.sub(r"[^a-z0-9]+", "", (text or "").lower())


def _base_title(rec):
    """Franchise key: no season, no (...)/language/dub tails - works on
    every hub-title shape ("Season 2 Hindi Episodes ...", "Season 1
    Hindi Dubbed ...", "Season 4 (Hashira Training Arc) ...")."""
    n = rec["name"]
    n = re.sub(r"\([^)]*\)", " ", n)
    n = re.sub(r"\s*[-–]?\s*(hindi|tamil|telugu|malayalam|bengali|multi|"
               r"dubbed|subbed|dub|sub|uncut|crunchyroll|jio\s*cinema)\b.*$",
               "", n, flags=re.I)
    n = re.sub(r"\bseason\s*\d+\b", " ", n, flags=re.I)
    n = re.sub(r"\bepisodes\b", " ", n, flags=re.I)
    return re.sub(r"\s+", " ", n).strip(" -–")


_SIM_STOP = {"the", "a", "an", "of", "to", "in", "vs", "no", "part",
             "movie", "season", "episode", "episodes", "hindi", "dubbed",
             "subbed", "download", "watch", "online", "full", "hd", "tv"}


def _toks(text):
    return {w for w in re.findall(r"[a-z0-9]+", (text or "").lower())
            if w not in _SIM_STOP and len(w) > 1}


def _sim_match(title, season, mtype):
    """Word-token similarity fallback for the strict substring matcher:
    catches branded Cinemeta names ("Crayon Shin-chan: Action Kamen vs
    Higure Rakshas" vs the site's "Shin Chan Movie Action Kamen vs
    Higure Rakshas").  Requires >=3 shared distinctive words covering
    >=60% of the smaller side; type and season filters still apply."""
    wa = _toks(title)
    if len(wa) < 3:
        return None
    want_movie = mtype == "movie"
    best, bs = None, 0.0
    for rec in SHOWS.values():
        if bool(rec["movie"]) != want_movie:
            continue
        wb = _toks(_base_title(rec))
        shared = wa & wb
        if len(shared) < 3:
            continue
        s = len(shared) / max(1, min(len(wa), len(wb)))
        if s > bs:
            best, bs = rec, s
    if not best or bs < 0.6:
        return None
    if season is not None:
        with STORE_LOCK:
            if not any(k[0] == season for k in best["eps"]):
                return None
    return best


def _match_show(title, season, mtype="series"):
    """Franchise match: hubs whose base title matches the Cinemeta title;
    pick the hub carrying the REQUESTED season.  No such hub -> None
    (no cards beats wrong-season episodes).  Exact-base hubs beat
    substring hubs ("Naruto" must not swallow "Naruto Shippuden");
    Subbed/Dubbed duplicates prefer Dubbed.  mtype is authoritative for
    franchise splits: a MOVIE id ("...Infinity Castle") must resolve to
    the movie hub, never to the series hub (and vice versa)."""
    tn = _norm_title(title)
    if len(tn) < 4:
        return None
    cands, exact_base = [], []
    for rec in SHOWS.values():
        bn = _norm_title(_base_title(rec))
        if not bn or not (bn == tn or bn in tn or tn in bn):
            continue
        cands.append(rec)
        if bn == tn:
            exact_base.append(rec)
    if not cands:
        return None
    if exact_base:
        cands = exact_base
    want_movie = mtype == "movie"
    by_type = [r for r in cands if bool(r["movie"]) == want_movie]
    if by_type:
        cands = by_type                 # keep type-honest candidates only
    elif any(bool(r["movie"]) != want_movie for r in cands):
        return None                     # only wrong-type hubs -> no match
    if season is not None:
        with STORE_LOCK:
            exact = [r for r in cands if any(k[0] == season for k in r["eps"])]
        if exact:
            dubbed = [r for r in exact
                      if "subbed" not in (r.get("site_name") or "").lower()]
            return (dubbed or exact)[0]
        return None

    def _first_season(r):
        with STORE_LOCK:
            ss = sorted(k[0] for k in r["eps"] if k[0])
        return ss[0] if ss else 99

    cands.sort(key=lambda r: (r["movie"], _first_season(r)))
    dubbed = [r for r in cands
              if "subbed" not in (r.get("site_name") or "").lower()]
    return (dubbed or cands)[0]


def _rows_for(rec, season, episode):
    with STORE_LOCK:
        eps = rec["eps"]
        if rec["movie"]:
            return eps.get((0, 1)) or next(iter(eps.values()), [])
        if season is None:
            for key in sorted(eps):
                return eps[key]
            return []
        rows = (eps.get((season, episode)) or eps.get((0, episode))
                or eps.get((1, episode)) or [])
        if not rows:
            for (s0, e0), v in sorted(eps.items()):
                if e0 == episode:
                    rows = v
                    break
        return rows

# ----------------------------------------------------------------- cards ---
def _clip(text, limit):
    """Whitespace-normalised, word-boundary-clipped text."""
    text = re.sub(r"\s+", " ", text or "").strip()
    if len(text) <= limit:
        return text
    cut = text[:limit]
    sp = cut.rfind(" ")
    return cut[:sp] if sp > limit // 2 else cut


def _phx_card(rec, lang, prefix, ep_title, note, zipper, base, src="MQ",
              kind="fsl", qres=""):
    """Phoenix-style stream card (MQ = in-app HLS, WN = direct MKV)."""
    sub = " · sub" if lang.lower().endswith("sub") else ""
    lang0 = re.sub(r"\s*sub\s*$", "", lang, flags=re.I).strip() or lang
    # hub names carry "(Hindi Dubbed) ..." tails; the badge already says it
    clean = re.sub(r"\s*\([^)]*(?:Hindi|Download|HD)[^)]*\)\s*$", "",
                   rec["name"], flags=re.I).strip()
    line1 = f"⧉ {_clip(clean or rec['name'], 56)} ⌗ {lang0}{sub}"
    if rec["movie"]:
        line2 = "⬡ Movie"
    else:
        et = ep_title if ep_title and ep_title != rec["name"] else ""
        line2 = f"⬡ {prefix}" + (f" · {_clip(et, 34)}" if et else "")
    if src == "WN":
        # ALWAYS the direct origin link: the beamup edge strips client
        # Range headers (proven via the /hdrs echo), so a same-origin
        # proxy can never seek - while the player hitting R2/google
        # DIRECTLY gets real byte-range seeking (how the IC cards work).
        name, binge, fname = "◫ WN ◫", f"rt2|wn|{lang.lower()}", f"{prefix}.mkv"
        url = zipper
        wq = f" · {qres}" if qres else ""
        line3 = ("⊞ mollad_jaat ◧ WN" + wq + " · Untouched MKV"
                 if kind == "fsl"
                 else "⊞ mollad_jaat ◧ WN" + wq + " · Untouched (progressive)")
    else:
        line3 = "⊞ mollad_jaat ◧ MQ" + (f" · {qres}" if qres else "")
        name, binge, fname = "◫ MQ ◫", f"rt2|mq|{lang.lower()}", f"{prefix}.m3u8"
        url = f"{base}/mq/{_mq_token(zipper)}.m3u8"
    if note:
        line3 += f" · {note}"
    return {
        "name": name,
        "title": f"{line1}\n{line2}\n{line3}",
        "url": url,
        "behaviorHints": {
            "notWebReady": False,
            "bingeGroup": binge,
            "filename": fname,
        },
    }


def _lang_label(raw):
    """Row language -> card badge.  Default/WMQ rows are the primary
    (Hindi) player; 'Hindi Dub' folds into plain Hindi; 'Hindi Sub'
    keeps its own badge."""
    lang = re.sub(r"\s*(?:uncut|censored)\s*$", "", raw or "",
                  flags=re.I).strip()
    if not lang or lang.lower() in ("default", "watchmultiquality"):
        return "Hindi"
    if lang.lower() == "animetimes":
        return "Anime Times"
    return re.sub(r"\s+dub$", "", lang, flags=re.I)

# ------------------------------------------------------------- handlers ----
_public_base_holder = {}


def handle_manifest(base):
    return {
        "id": ADDON_ID,
        "version": VERSION,
        "name": ADDON_NAME,
        "description": ("Anime & toons in Hindi, Tamil, Telugu, Bengali "
                        "and more - every language the site carries, "
                        "played in-app as multi-quality HLS.  Works with "
                        "any catalog's tt-ids."),
        "logo": (base + "/logo.png") if base
                else "https://5a16d5684c14-raretoons.baby-beamup.club/logo.png",
        "background": None,
        "types": ["movie", "series"],
        # streams-only (user request): no catalogs of our own; streams
        # resolve for foreign tt... ids via Cinemeta and for legacy
        # raretoons2: ids.
        "resources": ["stream", "meta"],
        "idPrefixes": ["raretoons2", "tt"],
        "catalogs": [],
        "behaviorHints": {"configurable": False},
    }


def handle_meta(mtype, mid):
    slug = mid.split(":", 1)[1] if ":" in mid else mid
    rec = SHOWS.get(slug)
    if not rec:
        return None
    try:
        _absorb_live(rec, _live_rows(rec))
    except Exception:
        pass
    if not rec.get("poster"):
        _fetch_poster(rec)
    if rec.get("movie"):
        # SPEED: the detail page opens ~1-3 s before the play tap ->
        # walk this movie's zippers in the background NOW so the
        # /stream request finds warm caches and shows cards instantly.
        def _prewarm(rec=rec):
            try:
                picks, wc = {}, {}
                for r in _rows_for(rec, None, None):
                    z, lang = r.get("mq"), _lang_label(r.get("lang"))
                    if not z:
                        continue
                    if r.get("btn") == "watchnow":
                        lst = wc.setdefault(lang, [])
                        if all(z != z0 for z0, _q in lst):
                            lst.append((z, r.get("qn") or ""))
                    else:
                        lst = picks.setdefault(lang, [])
                        if z not in lst:
                            lst.append(z)
                if picks:
                    _resolve_picks(picks)
                if wc:
                    _resolve_wn(wc)
            except Exception:
                pass
        _bg_once(("prewarm-movie", slug), _prewarm)
    info = _show_info(rec, wait=3)
    meta = {
        "id": mid,
        "type": mtype,
        "name": rec["name"],
        "poster": rec["poster"] or None,
        "background": rec["poster"] or None,
        "description": info.get("d") or (f"{rec['name']} - every language the site "
                        "carries, streamed in-app as multi-quality HLS."),
        "overview": info.get("d") or "",
        "genres": info.get("g") or ["Animation"],
        "rating": info.get("r"),
        "ratingSource": {"mal": "MyAnimeList", "tmdb": "TMDB"}.get(info.get("rs"), ""),
        "videos": [],
    }
    if not rec["movie"]:
        vids = []
        with STORE_LOCK:
            seen_se = set()
            for (s, e), rows in sorted(rec["eps"].items(),
                                       key=lambda kv: (kv[0][0] or 99, kv[0][1])):
                s = s or 1           # season-less rows are still playable
                if (s, e) in seen_se or not e:
                    continue
                seen_se.add((s, e))
                r0 = rows[0]
                title = r0.get("ep_title") or f"Episode {e}"
                vids.append({"id": f"raretoons2:{slug}:{s}:{e}",
                             "season": s, "episode": e,
                             "title": title, "name": title})
        meta["videos"] = vids
    return meta


def handle_stream(mtype, mid):
    """One MQ card per resolvable language.  Foreign tt-ids title-match
    through Cinemeta.  Every request merges the live hub first (TTL
    cached): the site rotates movie zippers and adds dubs/episodes
    continuously, so the crawler snapshot goes stale within hours."""
    season = episode = None
    rec = None
    if mid.startswith("raretoons2:"):
        parts = mid[len("raretoons2:"):].split(":")
        rec = SHOWS.get(parts[0])
        if len(parts) >= 3:
            try:
                season, episode = int(parts[-2]), int(parts[-1])
            except ValueError:
                pass
    elif re.match(r"^tt\d+$", mid.split(":")[0] or ""):
        parts = mid.split(":")
        try:
            if len(parts) >= 3:
                season, episode = int(parts[-2]), int(parts[-1])
        except ValueError:
            pass
        title = _cinemeta_name(mtype, parts[0])
        rec = _match_show(title, season, mtype) if title else None
        if not rec and title:
            rec = _sim_match(title, season, mtype)
        if not rec and title:
            # ALTERNATIVE-NAME PARALLEL FETCH: the site's own search and
            # Cinemeta's alt titles race; either may rescue the match.
            box = {}
            ths = [
                threading.Thread(target=lambda b=box: b.update(
                    s=_site_search_slug(title, mtype == "movie")),
                    daemon=True),
                threading.Thread(target=lambda b=box: b.update(
                    a=_imdb_names(mtype, parts[0])), daemon=True)]
            for t0_ in ths:
                t0_.start()
            dl = time.monotonic() + 12
            for t0_ in ths:
                t0_.join(max(0.5, dl - time.monotonic()))
            rec = SHOWS.get(box.get("s") or "")
            if not rec:
                for alt in (box.get("a") or []):
                    rec = (_match_show(alt, season, mtype)
                           or _sim_match(alt, season, mtype)
                           or SHOWS.get(_site_search_slug(
                               alt, mtype == "movie") or ""))
                    if rec:
                        break
    else:
        return {"streams": []}
    if not rec:
        return {"streams": []}

    try:
        _absorb_live(rec, _live_rows(rec), season)
    except Exception:
        pass
    rows = _rows_for(rec, season, episode)
    if not rows:
        return {"streams": []}

    base = _public_base_holder.get("base") or ""
    prefix = (f"S{season:02d}E{episode:02d}" if season is not None
              else f"E{(rows[0].get('episode') or 1):02d}")
    ep_title = rows[0].get("ep_title") or rec["name"]

    def _picks(rs):
        p = {}
        for r in rs:
            lang = _lang_label(r.get("lang"))
            z = r.get("mq") or r.get("sb")
            if z:
                lst = p.setdefault(lang, [])
                if z not in lst:
                    lst.append(z)
        return {k: p[k] for k in sorted(p, key=lambda k: LANG_ORDER.get(k, 50))}

    picks = _picks(rows)
    if not picks:
        return {"streams": []}

    # movies: collect the WatchNow pool up front so the MQ and WN walks
    # run CONCURRENTLY - walking them back-to-back doubled the wait and
    # was the "cards take forever" complaint.
    def _wn_pool(rows_):
        wc = {}
        for r in rows_:
            if r.get("btn") != "watchnow":
                continue
            lang = _lang_label(r.get("lang"))
            z = r.get("mq")
            if z:
                lst = wc.setdefault(lang, [])
                if all(z != z0 for z0, _q in lst):
                    lst.append((z, r.get("qn") or ""))
        return wc

    def _pools(rows_, picks_, wc_):
        dl = time.monotonic() + _LW + 0.5
        box = {"wn": {}}
        ts = [threading.Thread(
            target=lambda b=box: b.update(mq=_resolve_picks(picks_, wait=_LW)),
            daemon=True)]
        if wc_:
            ts.append(threading.Thread(
                target=lambda b=box: b.update(wn=_resolve_wn(wc_, wait=_LW)),
                daemon=True))
        for t in ts:
            t.start()
        for t in ts:
            t.join(max(0.5, dl - time.monotonic()))
        return box.get("mq") or {}, box.get("wn") or {}

    wn_cands = _wn_pool(rows)
    resolved, wn_resolved = _pools(rows, picks, wn_cands)

    # requested episode absent from the merged view -> ONE synchronous
    # live refresh + retry (a brand-new episode must show on first tap).
    has_req = any((season is None or (r.get("season") or 1) == season)
                  and (episode is None or (r.get("episode") or 1) == episode)
                  for r in rows)
    if not has_req:
        with _live_lock:
            _live_cache.pop(rec.get("hub"), None)
        try:
            live = _live_rows(rec)
        except Exception:
            live = []
        if live:
            _absorb_live(rec, live, season)
            rows = _rows_for(rec, season, episode)
            picks = _picks(rows)
            wn_cands = _wn_pool(rows)
            resolved, wn_resolved = _pools(rows, picks, wn_cands)
    elif not OPTIMISTIC and (not resolved or (wn_cands and not wn_resolved)):
        # resolution came up EMPTY (a rotated zipper): the user must
        # never see zero cards on the first tap -> ONE synchronous live
        # refresh + retry before serving whatever we have.
        with _live_lock:
            _live_cache.pop(rec.get("hub"), None)
        try:
            live = _live_rows(rec)
        except Exception:
            live = []
        if live:
            _absorb_live(rec, live, season)
            rows = _rows_for(rec, season, episode)
            picks = _picks(rows)
            wn_cands = _wn_pool(rows)
            resolved, wn_resolved = _pools(rows, picks, wn_cands)
    if len(resolved) < len(picks) or (wn_cands and not wn_resolved):
        # served what we have NOW; finish the rest in the background
        def _fin(rec=rec, season=season, episode=episode):
            fr = _rows_for(rec, season, episode)
            fp = _picks(fr)
            got = _resolve_picks(fp) if fp else {}     # joins walks in flight
            if len(got) < len(fp):                     # zipper may have rotated
                with _live_lock:
                    _live_cache.pop(rec.get("hub"), None)
                live = _live_rows(rec)
                if live:
                    _absorb_live(rec, live, season)
                    fr = _rows_for(rec, season, episode)
                    fp = _picks(fr)
                    if fp:
                        _resolve_picks(fp)
            wc = _wn_pool(fr)
            if wc:
                _resolve_wn(wc)
        _bg_once(("fin", rec.get("hub"), season, episode), _fin)

    # series: pre-resolve the NEXT episode in the background - pressing
    # "next" then shows cards instantly.
    if not rec["movie"] and season is not None and episode:
        nxt = _rows_for(rec, season, episode + 1)
        zp = {}
        for r in nxt:
            z = r.get("mq") or r.get("sb")
            if z:
                zl = _lang_label(r.get("lang"))
                lst = zp.setdefault(zl, [])
                if z not in lst:
                    lst.append(z)
        if zp:
            _bg_once(("pre", rec.get("hub"), season, episode),
                     lambda: _resolve_picks(zp))

    dub_show = "dubbed" in (rec.get("site_name") or "").lower()
    has_dub = any(_lang_label(lang).lower() == "hindi" for lang in resolved)
    streams = []
    for lang in picks:                     # LANG_ORDER iteration order
        hit = resolved.get(lang)
        if not hit:
            z0 = _optimistic_zipper(picks[lang]) if OPTIMISTIC else None
            if not z0:
                continue                   # known-dead / nothing to try
            hit = (None, z0, "")           # resolves at play time
        master, z, mq_q = hit
        note = ""
        if dub_show and lang.lower() == "hindi sub" and not has_dub:
            note = "site has no dub for this episode yet"
        streams.append(_phx_card(rec, lang, prefix, ep_title, note, z, base,
                                 qres=mq_q))

    # WatchNow direct sources (movies): signed per-language file URLs.
    # fsl -> direct; 10g -> same-origin /wn slice-proxy.
    for lang in picks:                     # keep card order stable
        hit = wn_resolved.get(lang)
        if hit:
            u, kind, z, qn = hit
            wq = _res_label(unquote(u.split("?")[0])) or _res_label(qn)
            streams.append(_phx_card(rec, lang, prefix, ep_title, "", u,
                                     base, src="WN", kind=kind, qres=wq))
    return {"streams": streams}

# ------------------------------------------------------ website API --------
_LANG_KEYS = ["Hindi", "Tamil", "Telugu", "Bengali", "Malayalam", "Kannada", "Urdu", "English", "Japanese"]


def _show_langs(rec):
    found = set()
    for rows in rec["eps"].values():
        for r in rows:
            for k in _LANG_KEYS:
                if k.lower() in (r.get("lang") or "").lower():
                    found.add(k)
    return sorted(found)


# Western / non-anime cartoons.  The index has no genre field, so titles are
# matched by name.  To add more without editing code, set CARTOON_EXTRA to a
# comma-separated list of words (e.g. "gumball,oggy").
_CARTOON_WORDS = (
    "scooby", "tom and jerry", "ben 10", "ben gen 10", "tale dark", "grimm variations",
    "101 dalmatian", "happy family usa", "7 bears", "alvinnn", "aladdin", "batman",
    "batwheels", "bat-fam", "bionic max", "beywarriors", "beywheelz", "boonie bears",
    "boboiboy", "centaurworld", "castlevania", "dr. seuss", "duck dodgers",
    "ed, edd n eddy", "ejen ali", "exploding kittens", "hazbin", "helluva",
    "hot wheels", "invincible season", "jentry chau", "jurassic world", "justice league",
    "ninjago", "monsterwheelies", "miraculous", "moka", "murder drones", "nate is late",
    "popeye", "powerpuff", "regular show", "richie rich", "rocket monkeys",
    "sausage party", "spidey", "spirit rangers", "star wars", "swat kats", "tangled",
    "teen titans", "thundercats", "teenage mutant", "tmnt", "tomb raider: the legend",
    "transformers", "ultra b", "vampirina", "wolf king", "young justice",
    "sabrina", "dragon tales", "denver, the last", "dennis the menace", "daffy",
    "dragon prince", "ridley jones", "ronja", "mighty nein", "keymon",
    "digital circus", "molly mcgee", "the bad guys", "diabolical", "agent elvis",
    "are you afraid", "splinter cell", "twilight of the gods", "the mask", "cory carson",
    "slugterra", "barbie", "hawa hawai", "avatar the", "avatar aang", "looney",
    "bugs bunny", "tweety", "garfield", "smurfs", "paw patrol", "lego", "spongebob",
    "mickey", "winnie", "lilo", "frozen", "mighty morphin", "power rangers",
    "kamen rider", "iron man (2010)", "blade (2011)", "scott pilgrim", "arthur",
    "bob the builder", "peppa", "oggy", "mr bean", "gumball", "johnny test",
    "kids next door", "codename", "pixi post", "peabody", "turning mecard",
    "mecard", "ladybug", "the loud house",
)
_CARTOON_EXTRA = tuple(w.strip().lower() for w in
                       os.environ.get("CARTOON_EXTRA", "").split(",") if w.strip())


def _kind(name):
    n = (name or "").lower()
    return "cartoon" if any(w in n for w in _CARTOON_WORDS + _CARTOON_EXTRA) else "anime"


def _latest_ep(rec):
    """(season, episode) of the newest episode, or None for movies."""
    if rec["movie"]:
        return None
    ks = [k for k in rec["eps"] if k[0]]
    return list(max(ks)) if ks else None


def _short_desc(t, n=320):
    """Description trimmed to ~n chars on a word boundary (for hero/previews)."""
    t = re.sub(r"\s+", " ", t or "").strip()
    if len(t) <= n:
        return t
    return t[:n].rsplit(" ", 1)[0].rstrip(" ,;:-") + "…"


def _api_shows_build():
    """Compact list for the website grid (name, slug, poster, movie?)."""
    items = []
    with STORE_LOCK:
        for i, r in enumerate(SHOWS.values()):
            info = _show_info_cached(r)   # cache-only: no thread per show
            items.append({"slug": r["slug"], "name": r["name"],
                          "poster": r.get("poster") or "", "movie": bool(r["movie"]),
                          "langs": _show_langs(r), "kind": _kind(r["name"]), "ord": i,
                          "le": _latest_ep(r), "genres": info.get("g", []),
                          "rating": info.get("r"), "d": _short_desc(info.get("d")),
                          "n": sum(1 for k in r["eps"] if k[0])})
    upd = _updates()
    for it in items:
        it["upd"] = int(upd.get(it["slug"], 0))
        if it["poster"].startswith("https://"):
            it["poster"] = "/img/s/" + it["slug"]      # short link; hides the source site
    items.sort(key=lambda x: x["name"].lower())
    return {"shows": items, "now": int(time.time()), "popular": _popular(),
            "trending": _trending("week"),
            "trending_day": _trending("day")}


def _show_info_cached(rec):
    """Cache-only read for the list endpoint.  The old _show_info() spawned
    a background TMDB lookup thread for EVERY stale show on every request;
    the backfill thread already keeps those fresh."""
    slug = rec["slug"]
    info = _TMDB_CACHE.get(slug)
    if not info:
        return {}
    k = (slug, info.get("t"))
    g = _FIN_MEMO.get(k)
    if g is None:
        g = _FIN_MEMO[k] = G.finalize(info.get("g"), info.get("d"), info.get("rs"))
    out = dict(info)
    out["g"] = g
    return out


_shows_cache = {"t": 0, "raw": None, "gz": None}
_shows_lock = threading.Lock()


def _shows_rebuild():
    raw = json.dumps(_api_shows_build(), ensure_ascii=False).encode("utf-8")
    _shows_cache.update(raw=raw, gz=gzip.compress(raw, 6), t=time.time())


def index_page():
    """index.html with the show list already INSIDE it (window.__BOOT__), so
    the cards render on first paint instead of after a second request."""
    path = os.path.join(BASE_DIR, "index.html")
    try:
        mt = os.path.getmtime(path)
    except OSError:
        return None, None
    try:
        raw_json, _ = shows_payload()
    except Exception:
        raw_json = None
    key = (_shows_cache["t"], mt)
    c = _page_cache
    if c["key"] == key and c["raw"]:
        return c["raw"], c["gz"]
    with open(path, "rb") as fh:
        html = fh.read().decode("utf-8")
    if raw_json:
        boot = (raw_json.decode("utf-8").replace("<", "\\u003c")
                .replace("\u2028", "\\u2028").replace("\u2029", "\\u2029"))
        i = html.find("const LITE=")
        j = html.rfind("<script", 0, i) if i > 0 else -1
        if j > 0:
            html = html[:j] + "<script>window.__BOOT__=" + boot + ";</script>\n" + html[j:]
    raw = html.encode("utf-8")
    c.update(key=key, raw=raw, gz=gzip.compress(raw, 6))
    return c["raw"], c["gz"]


def shows_payload():
    """(raw_json, gzipped_json).  Built once, served from memory, refreshed
    in the background after SHOWS_TTL - requests never wait for a rebuild."""
    c = _shows_cache
    if c["raw"] is None:
        with _shows_lock:                  # first build: one builder, rest wait
            if c["raw"] is None:
                _shows_rebuild()
    elif time.time() - c["t"] > SHOWS_TTL:
        _bg_once(("shows",), _shows_rebuild)
    return c["raw"], c["gz"]


_img_cache = {}
_page_cache = {"key": None, "raw": None, "gz": None}


IMG_DIR = os.environ.get("IMG_CACHE_DIR") or os.path.join(tempfile.gettempdir(), "rt_img")
try:
    os.makedirs(IMG_DIR, exist_ok=True)
except OSError:
    pass


def _img_path(token):
    return os.path.join(IMG_DIR, hashlib.sha1(token.encode()).hexdigest())


def _img_mem(token, hit):
    if len(_img_cache) > 300:
        _img_cache.pop(next(iter(_img_cache)), None)
    _img_cache[token] = hit


def _img_load(token, url):
    """memory -> disk -> upstream.  Returns (bytes, content_type) or None.
    Posters used to be re-fetched from the source site (TLS handshake +
    Cloudflare) every time the 400-entry memory cache rolled over - that
    was the 'card is there but the picture comes late' delay."""
    hit = _img_cache.get(token)
    if hit:
        return hit
    pth = _img_path(token)
    try:
        with open(pth, "rb") as fh:
            ct, _, body = fh.read().partition(b"\n")
        if body:
            hit = (body, ct.decode() or "image/jpeg")
            _img_mem(token, hit)
            return hit
    except OSError:
        pass
    with _walk_lock_for("img:" + token):          # one upstream fetch per image
        hit = _img_cache.get(token)
        if hit:
            return hit
        r = upstream_get(url, referer=SITE, timeout=15)
        ctype = r.headers.get("content-type") or ""
        if r.status_code != 200 or "image" not in ctype:
            return None
        hit = (r.content, ctype)
        try:
            tmp = pth + ".tmp%d" % threading.get_ident()
            with open(tmp, "wb") as fh:
                fh.write(ctype.encode() + b"\n" + r.content)
            os.replace(tmp, pth)
        except OSError:
            pass
        _img_mem(token, hit)
        return hit


def _serve_img(handler, token, url=None):
    url = url or _unseal(token)
    if not url.startswith("https://"):
        return handler._send({"error": "bad image"}, 400)
    hit = _img_load(token, url)
    if not hit:
        return handler._send({"error": "no image"}, 404)
    handler.send_response(200)
    handler.send_header("Content-Type", hit[1])
    handler.send_header("Content-Length", str(len(hit[0])))
    handler.send_header("Cache-Control", "public, max-age=604800, immutable")
    handler.end_headers()
    if not handler._is_head:
        handler.wfile.write(hit[0])


def _img_prewarm():
    """Background: pull every poster to disk once (visible-first), so a
    visitor never waits on the source site for a picture."""
    time.sleep(8)
    while True:
        try:
            order, seen = [], set()
            upd = _updates()
            lists = (_trending("week"), _trending("day"), _popular(),
                     sorted(SHOWS, key=lambda k: -upd.get(k, 0)), list(SHOWS))
            for lst in lists:
                for slug in lst:
                    if slug not in seen and slug in SHOWS:
                        seen.add(slug)
                        order.append(slug)
            q = [sl for sl in order
                 if (SHOWS[sl].get("poster") or "").startswith("https://")
                 and not os.path.exists(_img_path("s:" + sl))]
            lock = threading.Lock()

            def _worker():
                while True:
                    with lock:
                        if not q:
                            return
                        sl = q.pop(0)
                    try:
                        _img_load("s:" + sl, SHOWS[sl]["poster"])
                    except Exception:
                        pass
                    time.sleep(0.1)
            ws = [threading.Thread(target=_worker, daemon=True) for _ in range(3)]
            for w in ws:
                w.start()
            for w in ws:
                w.join()
        except Exception as e:
            print("[rt2] img prewarm:", repr(e), flush=True)
        time.sleep(3600)


_pop_cache = {"t": 0, "data": []}


def _popular():
    if time.time() - _pop_cache["t"] > 600 and not _pop_cache.get("busy"):
        _pop_cache["busy"] = True

        def _run():
            try:
                _pop_cache.update(t=time.time(), data=accounts.popular())
            except Exception:
                _pop_cache["t"] = time.time() - 540
            finally:
                _pop_cache["busy"] = False
        threading.Thread(target=_run, daemon=True).start()
    return _pop_cache["data"]


# ------------------------------------------- TMDB daily/weekly trending ---
# TMDB trending (day + week; tv + movies; many pages) matched by title
# against the shows we actually have (exact + fuzzy), then filled with
# TMDB's most-popular Japanese animation.  Cached 1 h per window; failures
# keep the last good list.
TREND_TTL = _env_int("TREND_TTL", 600)
TREND_PAGES = _env_int("TREND_PAGES", 15)         # 20 titles per page per kind
_trend_cache = {w: {"t": 0, "data": [], "busy": False} for w in ("day", "week")}


def _tn_norm(s):
    return re.sub(r"[^a-z0-9]+", "", (s or "").lower())


def _tn_index():
    with STORE_LOCK:
        idx = {}
        for rec in SHOWS.values():
            for nm in (rec.get("name"), _tmdb_clean(rec.get("name"))):
                k = _tn_norm(nm)
                if k:
                    lst = idx.setdefault(k, [])
                    if rec["slug"] not in lst:
                        lst.append(rec["slug"])
    return idx


def _tn_match(idx, keys, item):
    """Slugs for one TMDB item: exact title first, then prefix/containment
    (e.g. 'Attack on Titan' <-> 'Attack on Titan The Final Season')."""
    names = [item.get(k) for k in ("name", "original_name", "title", "original_title")]
    hit = []
    for nm in names:
        for slug in idx.get(_tn_norm(nm), []):
            if slug not in hit:
                hit.append(slug)
    if hit:
        return hit
    for nm in names:
        t = _tn_norm(nm)
        if len(t) < 6:
            continue
        for k in keys:
            if len(k) < 6:
                continue
            short, long_ = (t, k) if len(t) <= len(k) else (k, t)
            if long_.startswith(short) and len(short) / len(long_) >= 0.55:
                for slug in idx[k]:
                    if slug not in hit:
                        hit.append(slug)
    return hit


_disc_cache = {"t": 0, "data": []}


def _tmdb_discover_anime():
    if _disc_cache["data"] and time.time() - _disc_cache["t"] < TREND_TTL:
        return _disc_cache["data"]
    out = []
    for kind in ("tv", "movie"):
        for page in range(1, 7):
            try:
                out += _tmdb_get(f"/discover/{kind}", with_genres=16,
                                 with_original_language="ja",
                                 sort_by="popularity.desc", page=page).get("results") or []
            except Exception as e:
                print(f"[rt2] tmdb discover {kind} p{page} failed: {repr(e)}", flush=True)
    if out:
        _disc_cache.update(t=time.time(), data=out)
    return out or _disc_cache["data"]


def _tmdb_trending_slugs(window):
    """-> [slug, ...] ordered by TMDB trending rank (best first)."""
    idx = _tn_index()
    keys = list(idx)
    out, seen = [], set()

    def take(item):
        for slug in _tn_match(idx, keys, item):
            if slug not in seen:
                seen.add(slug)
                out.append(slug)

    ok = False
    pages = TREND_PAGES if window == "week" else max(8, TREND_PAGES // 2)
    for page in range(1, pages + 1):
        for kind in ("tv", "movie"):
            try:
                res = _tmdb_get(f"/trending/{kind}/{window}", page=page).get("results") or []
            except Exception as e:
                print(f"[rt2] tmdb trending {kind}/{window} p{page} failed: {repr(e)}", flush=True)
                continue
            ok = ok or bool(res)
            anim = [r for r in res if 16 in (r.get("genre_ids") or [])]
            for r in anim + [r for r in res if r not in anim]:
                take(r)
    # fill: most popular Japanese animation on TMDB right now (shared by day+week)
    for r in _tmdb_discover_anime():
        ok = True
        take(r)
    if not ok:
        raise RuntimeError("tmdb trending unavailable")
    return out


def _trending(window="week"):
    """TMDB trending slugs first, then our own most-watched; never blocks."""
    c = _trend_cache[window]
    if time.time() - c["t"] > TREND_TTL and not c["busy"]:
        c["busy"] = True

        def _run():
            try:
                c.update(t=time.time(), data=_tmdb_trending_slugs(window))
            except Exception as e:
                print(f"[rt2] trending {window} refresh failed: {repr(e)}", flush=True)
                c["t"] = time.time() - TREND_TTL + 300   # retry in 5 min
            finally:
                c["busy"] = False
        threading.Thread(target=_run, daemon=True).start()
    seen, out = set(), []
    for slug in list(c["data"]) + list(_popular()):
        if slug not in seen:
            seen.add(slug)
            out.append(slug)
    return out

_upd_cache = {"t": 0, "data": {}}


def _updates():
    """slug -> unix time its episode count last grew (0 = since tracking began).
    Never blocks a request: serves the cached copy and refreshes in the background."""
    if time.time() - _upd_cache["t"] >= 600 and not _upd_cache.get("busy"):
        _upd_cache["busy"] = True
        threading.Thread(target=_updates_refresh, daemon=True).start()
    return _upd_cache["data"]


def _updates_refresh():
    now = time.time()
    try:
        with STORE_LOCK:
            counts = {slug: len(rec["eps"]) for slug, rec in SHOWS.items()}
        raw = accounts.kv_get("ep_counts")
        old = json.loads(raw) if raw else None
        new, dirty = {}, old is None
        for slug, c in counts.items():
            o = (old or {}).get(slug)
            if o is None:
                new[slug] = [c, 0 if old is None else now]; dirty = True
            elif c > o[0]:
                new[slug] = [c, now]; dirty = True
            else:
                new[slug] = [o[0], o[1]]
        if dirty:
            accounts.kv_set("ep_counts", json.dumps(new, separators=(",", ":")))
        _upd_cache.update(t=now, data={k: v[1] for k, v in new.items()})
    except Exception as e:
        print("[rt2] updates tracking failed:", e, flush=True)
        _upd_cache["t"] = now - 540      # retry in ~1 minute
    finally:
        _upd_cache["busy"] = False


def api_watch(slug, season, episode):
    """Playable sources for one episode/movie, simplified for the website."""
    rec = SHOWS.get(slug)
    if not rec:
        return {"sources": [], "error": "unknown show"}
    mid = f"raretoons2:{slug}"
    if not rec["movie"] and season is not None:
        mid += f":{int(season)}:{int(episode)}"
    res = handle_stream("movie" if rec["movie"] else "series", mid)
    out = []
    for c in res.get("streams", []):
        lines = (c.get("title") or "").split("\n")
        ml = re.search(r"⌗\s*(.+)$", lines[0] if lines else "")
        mq = re.search(r"(\d{3,4}p)", lines[-1] if lines else "")
        is_mq = "MQ" in (c.get("name") or "")
        url = c.get("url") or ""
        if is_mq:
            url = urlparse(url).path        # same-origin: no http/https mix
        out.append({"lang": (ml.group(1).strip() if ml else "Default"),
                    "kind": "mq" if is_mq else "direct",
                    "quality": mq.group(1) if mq else "",
                    "url": url})
    return {"name": rec["name"], "sources": out}


# ---------------------------------------------------- /mq HLS rewriter -----
_B64_RE = r"[A-Za-z0-9_\-]"
_URL_ATTR_RE = re.compile(r'URI="([^"]+)"')


_u64, _u64d = _seal, _unseal


def _rewrite_m3u8(text, base_url, proxy_prefix):
    """Rewrite every URI in an HLS playlist to same-origin /mq/u/<b64>:
    absolute + relative URLs, variant lines, segment lines, URI="..."
    attributes.  #EXT-X-BYTERANGE is EXPLODED into the segment URL
    (?rt=start-end) so a player that ignores the tag never downloads the
    whole origin resource (the "full download" bug)."""
    out, br, last_end = [], None, 0
    for line in text.splitlines():
        ls = line.strip()
        if not ls:
            continue
        if ls.startswith("#EXT-X-BYTERANGE"):
            mb = re.match(r"#EXT-X-BYTERANGE:(\d+)(?:@(\d+))?", ls)
            if mb:
                ln = int(mb.group(1))
                st = int(mb.group(2)) if mb.group(2) is not None else last_end
                br = (st, st + ln - 1)
                last_end = st + ln
            continue
        if ls.startswith(("#EXT-X-KEY", "#EXT-X-MAP", "#EXT-X-MEDIA",
                          "#EXT-X-I-FRAME")):
            def _attr(mm):
                u = urljoin(base_url, mm.group(1))
                ext = ".key" if "KEY" in ls[:12] else ".bin"
                return f'URI="{proxy_prefix}/u/{_u64(u)}{ext}"'
            out.append(_URL_ATTR_RE.sub(_attr, ls))
        elif ls.startswith("#"):
            out.append(ls)
        else:
            u = urljoin(base_url, ls)
            ext = ".m3u8" if ".m3u8" in u.lower() else ".ts"
            seg = f"{proxy_prefix}/u/{_u64(u)}{ext}"
            if br:
                seg += f"?rt={br[0]}-{br[1]}"
                br = None
            out.append(seg)
    return "\n".join(out) + "\n"


_HTML_HEADS = (b"<!DO", b"<htm")


def _pump(handler, response, length=None, skip=0):
    """Stream the upstream body to the client, guarding against the
    origin slipping in an HTML page instead of media."""
    first = True
    written = 0
    for chunk in response.iter_content(64 * 1024):
        if not chunk:
            continue
        if first:
            if chunk.lstrip()[:4] in _HTML_HEADS:
                handler.close_connection = True
                return False
            first = False
        if skip:
            if len(chunk) <= skip:
                skip -= len(chunk)
                continue
            chunk, skip = chunk[skip:], 0
        if length is not None and written + len(chunk) > length:
            chunk = chunk[:length - written]
        handler.wfile.write(chunk)
        written += len(chunk)
        if length is not None and written >= length:
            break
    if length is not None and written < length:
        handler.close_connection = True      # short body: never reuse socket
    return True


_pl_cache = {}
_pl_lock = threading.Lock()


def _pl_cached(url):
    with _pl_lock:
        h = _pl_cache.get(url)
    return h[1] if h and h[0] > time.time() else None


def _pl_put(url, text):
    if not text:
        return
    with _pl_lock:
        if len(_pl_cache) > 300:
            for k in list(_pl_cache)[:100]:
                _pl_cache.pop(k, None)
        _pl_cache[url] = (time.time() + PL_TTL, text)


def _pl_fetch(url, timeout=20):
    """(status, text) - VOD playlists are static, so a hit skips a whole
    upstream round trip (every quality switch / seek reload used one)."""
    t = _pl_cached(url)
    if t is not None:
        return 200, t
    r = upstream_get(url, referer=ARGON, timeout=timeout)
    if r.status_code == 200:
        _pl_put(url, r.text or "")
    return r.status_code, (r.text or "")


def _warm_variants(master, text):
    """Pre-fetch the variant playlists in the background: the player asks
    for one of them right after the master."""
    for ln in (text or "").splitlines():
        ln = ln.strip()
        if ln and not ln.startswith("#") and ".m3u8" in ln.lower():
            u = urljoin(master, ln)
            if _pl_cached(u) is None:
                _bg_once(("pl", u), lambda u=u: _pl_fetch(u))


def _finish_master(handler, zipper, master, text):
    hs = [int(h) for h in _MASTER_RES_RE.findall(text or "")]
    if hs:
        with _hls_lock:
            _mqres_cache[master] = (time.time() + 6 * 3600, f"{max(hs)}p")
    body = _rewrite_m3u8(text or "", master, f"/mq/{_mq_token(zipper)}").encode()
    _warm_variants(master, text or "")
    handler._send_raw(body, CONTENT_TYPES[".m3u8"])


def _serve_m3u8_master(handler, zipper):
    master, _ = _mq_resolve(zipper)
    if not master:
        handler._send({"error": "MQ stream unavailable - try again"}, 502)
        return
    cached = _pl_cached(master)
    if cached is not None:
        try:
            _finish_master(handler, zipper, master, cached)
        except Exception as exc:
            handler._send({"error": f"master: {exc}"}, 502)
        return
    try:
        # the site's video host (groovy) sometimes hangs at connect
        # level during load spikes - one bounded retry rides out blips
        r = None
        for attempt in (1, 2):
            try:
                r = upstream_get(master, referer=ARGON,
                                 timeout=RESOLVE_TIMEOUT)
                break
            except Exception:
                if attempt == 2:
                    raise
        if r is None or r.status_code != 200:
            # signed URL may have expired - refresh the resolve once
            with _hls_lock:
                _hls_cache.pop(zipper, None)
            master, _ = _mq_resolve(zipper)
            if not master:
                handler._send({"error": "MQ expired"}, 502)
                return
            r = upstream_get(master, referer=ARGON)
            if r.status_code != 200:
                handler._send({"error": f"master {r.status_code}"}, 502)
                return
        _pl_put(master, r.text or "")
        _finish_master(handler, zipper, master, r.text or "")
    except Exception as exc:
        handler._send({"error": f"master: {exc}"}, 502)


def _serve_m3u8_child(handler, zipper, b64url, ext, rt=""):
    target = _u64d(b64url)
    if not target.startswith("http"):
        handler._send({"error": "bad child"}, 400)
        return
    proxy_prefix = f"/mq/{_mq_token(zipper)}"
    rng = handler.headers.get("Range")
    forced = None
    if rt:
        mr = re.match(r"(\d+)-(\d+)", rt)
        if mr:
            forced = f"bytes={mr.group(1)}-{mr.group(2)}"
            rng = forced                # the segment IS this byte slice
    up = None
    try:
        # Variant/media playlists must be REWRITTEN too; media streams.
        if ext == ".m3u8":
            code_, txt_ = _pl_fetch(target)
            if code_ != 200:
                handler._send({"error": f"playlist {code_}"}, 502)
                return
            body = _rewrite_m3u8(txt_, target, proxy_prefix).encode()
            handler._send_raw(body, CONTENT_TYPES[".m3u8"])
            return

        up = upstream_stream(target, referer=ARGON, rng=rng, timeout=30)
        code = up.status_code
        if code not in (200, 206, 416):
            handler._send({"error": f"child {code}"}, 502)
            return
        ctype = up.headers.get("Content-Type")
        if not ctype or "text/html" in ctype.lower():
            ctype = CONTENT_TYPES.get(ext, "application/octet-stream")
        total_s = up.headers.get("Content-Length") or ""
        total = int(total_s) if total_s.isdigit() else 0
        crange = up.headers.get("Content-Range")

        def _headers(cl, crng=None):
            handler.send_response(206 if crng else code)
            handler.send_header("Content-Type", ctype)
            if crng:
                handler.send_header("Content-Range", crng)
            # Content-Length is MANDATORY: without it HTTP/1.1 clients
            # stall until socket close (that was the broken seeking).
            if cl:
                handler.send_header("Content-Length", str(cl))
            handler.send_header("Accept-Ranges", "bytes")
            handler.send_header("Access-Control-Allow-Origin", "*")
            handler.send_header("Access-Control-Expose-Headers",
                                "Content-Length, Content-Range, "
                                "Accept-Ranges")
            handler.send_header("Cache-Control", "private, max-age=3600")
            if not cl:      # only an unknown length needs close; else keep-alive
                handler.send_header("Connection", "close")
            handler.end_headers()

        # normalizer: the client's requested slice is ALWAYS what goes
        # out, whatever the origin does:
        #   200 + full body        (googleusercontent) -> skip=start
        #   206 but open-ended     (google honours start, not end)
        #   206 exact              (R2, groovy)         -> pass through
        if rng and total > 0 and code in (200, 206):
            m2 = re.match(r"\s*bytes=(\d*)-(\d*)", rng)
            if m2 and (m2.group(1) or m2.group(2)):
                start = int(m2.group(1)) if m2.group(1) else 0
                end = int(m2.group(2)) if m2.group(2) else total - 1
                if start < total:
                    end = min(end, total - 1)
                    need = end - start + 1
                    cr_start = 0
                    if code == 206 and crange:
                        mc = re.match(r"\s*bytes\s+(\d+)-(\d+)/", crange)
                        if mc:
                            cr_start = int(mc.group(1))
                    skip = max(0, start - cr_start)
                    _headers(need, f"bytes {start}-{end}/{total}")
                    if not handler._is_head:
                        _pump(handler, up, length=need, skip=skip)
                    return

        if forced:
            # exploded standalone segment: plain 200 + exact body
            handler.send_response(200)
            handler.send_header("Content-Type", ctype)
            if total:
                handler.send_header("Content-Length", str(total))
            handler.send_header("Accept-Ranges", "bytes")
            handler.send_header("Access-Control-Allow-Origin", "*")
            handler.send_header("Access-Control-Expose-Headers",
                                "Content-Length, Accept-Ranges")
            handler.send_header("Cache-Control", "private, max-age=3600")
            if not total:
                handler.send_header("Connection", "close")
            handler.end_headers()
            if not handler._is_head:
                _pump(handler, up)
            return

        _headers(total or None, crange)
        if not handler._is_head:
            _pump(handler, up)
    except (BrokenPipeError, ConnectionResetError):
        pass
    except Exception as exc:
        handler.close_connection = True
        try:
            handler._send({"error": f"child: {exc}"}, 502)
        except Exception:
            pass
    finally:
        # seeking aborts in-flight segments: always release the upstream
        # connection, or stale ones pile up and the player starts to stall
        if up is not None:
            try:
                up.close()
            except Exception:
                pass



def _serve_download(handler, zipper, b64url, name, check=False):
    """Straight-to-disk download: the server joins the playlist's segments
    into ONE file and streams it with Content-Disposition: attachment, so
    the browser's own download manager saves it (nothing is held in RAM)."""
    target = _u64d(b64url)
    if not target.startswith("http"):
        handler._send({"error": "bad link"}, 400)
        return
    try:
        r = upstream_get(target, referer=ARGON, timeout=20)
        if r.status_code != 200:
            handler._send({"error": f"playlist {r.status_code}"}, 502)
            return
        text = r.text or ""
        if re.search(r"#EXT-X-KEY:METHOD=(?!NONE)", text):
            handler._send({"error": "This stream is encrypted and cannot be downloaded."}, 400)
            return
        items, init, br, last_end = [], None, None, 0
        for line in text.splitlines():
            ls = line.strip()
            if not ls:
                continue
            if ls.startswith("#EXT-X-MAP"):
                mm = _URL_ATTR_RE.search(ls)
                if mm:
                    init = urljoin(target, mm.group(1))
            elif ls.startswith("#EXT-X-BYTERANGE"):
                mb = re.match(r"#EXT-X-BYTERANGE:(\d+)(?:@(\d+))?", ls)
                if mb:
                    ln = int(mb.group(1))
                    st = int(mb.group(2)) if mb.group(2) is not None else last_end
                    br = (st, st + ln - 1)
                    last_end = st + ln
            elif not ls.startswith("#"):
                items.append((urljoin(target, ls), br))
                br = None
        if init:
            items.insert(0, (init, None))
        if not items:
            handler._send({"error": "Nothing to download."}, 400)
            return
        if check:
            handler._send({"ok": True, "parts": len(items)})
            return
        ext = ".mp4" if init else ".ts"
        safe = re.sub(r"[^\w\- ]+", "", name or "video").strip().replace(" ", "_")[:80] or "video"
        handler.send_response(200)
        handler.send_header("Content-Type", "video/mp4" if init else "video/mp2t")
        handler.send_header("Content-Disposition", f'attachment; filename="{safe}{ext}"')
        handler.send_header("Cache-Control", "no-store")
        handler.send_header("Connection", "close")
        handler.end_headers()
        handler.close_connection = True
        if handler._is_head:
            return
        for url, rngt in items:
            ok = False
            for attempt in range(3):
                up = None
                try:
                    rng = f"bytes={rngt[0]}-{rngt[1]}" if rngt else None
                    up = upstream_stream(url, referer=ARGON, rng=rng, timeout=30)
                    if up.status_code not in (200, 206):
                        raise RuntimeError(f"seg {up.status_code}")
                    length = skip = None
                    if rngt:
                        length = rngt[1] - rngt[0] + 1
                        skip = rngt[0] if up.status_code == 200 else 0
                    # nothing is written before _pump's first-chunk check,
                    # so a failed attempt can be retried cleanly
                    if _pump(handler, up, length=length, skip=skip or 0):
                        ok = True
                        break
                except (BrokenPipeError, ConnectionResetError):
                    return
                except Exception:
                    time.sleep(0.5 * (attempt + 1))
                finally:
                    if up is not None:
                        try:
                            up.close()
                        except Exception:
                            pass
            if not ok:
                return                      # abort: the browser shows a failed download
    except (BrokenPipeError, ConnectionResetError):
        pass
    except Exception as exc:
        try:
            handler._send({"error": f"download: {exc}"}, 502)
        except Exception:
            pass


_wn_size_cache = {}                        # target -> (expires, size)


def _wn_plain(url, rng, timeout):
    """Plain urllib streaming client for WatchNow file hosts (google-
    sensible: no browser impersonation needed there, and urllib's
    read(n)/close() never buffers the whole body).  Returns
    (status, resp) or (error_status, None)."""
    req = urllib.request.Request(url, headers={
        "User-Agent": UA, "Accept": "*/*", **({"Range": rng} if rng else {})})
    try:
        resp = urllib.request.urlopen(req, timeout=timeout)
        return resp.status, resp
    except urllib.error.HTTPError as e:
        return e.code, None
    except Exception:
        return 0, None


def _wn_pump(handler, resp, need, skip):
    """Chunked copy for urllib responses: drop `skip` bytes, send exactly
    `need` bytes, abort on dead/stalled clients (30s write timeout)."""
    handler.connection.settimeout(30)
    written = skipped = 0
    while written < need:
        chunk = resp.read(min(262144, need - written + skipped))
        if not chunk:
            break
        if skipped < skip:
            take = min(skip - skipped, len(chunk))
            skipped += take
            chunk = chunk[take:]
            if not chunk:
                continue
        handler.wfile.write(chunk)
        written += len(chunk)
    return written





def _wn_size(target):
    """File size via a headers-only ranged probe.  stream=True + close()
    so the body is never downloaded (a plain upstream_get here once
    pulled 796 MB into RAM and OOM-killed the box)."""
    now = time.time()
    with _hls_lock:
        hit = _wn_size_cache.get(target)
    if hit and hit[0] > now:
        return hit[1]
    total = 0
    code, r = _wn_plain(target, "bytes=0-0", 15)
    if r is not None:
        try:
            mc = re.match(r"\s*bytes\s+\d+-\d+/(\d+)",
                          r.headers.get("Content-Range") or "")
            if mc:
                total = int(mc.group(1))
            else:
                cl = r.headers.get("Content-Length") or ""
                total = int(cl) if cl.isdigit() else 0
        finally:
            r.close()
    else:
        total = 0
    with _hls_lock:
        _wn_size_cache[target] = (now + 3600, total)
    return total


def _serve_wn_slice(handler, b64url):
    """WatchNow slice-proxy.  googleusercontent answers ranged GETs
    INCONSISTENTLY (open-ended 206 sometimes, 200 + whole file other
    times) - so upstream status/CL are never trusted for the outgoing
    headers.  We probe the size ourselves (cached), always answer a
    proper 206 with an exact Content-Range + matching Content-Length,
    then pump exactly that many bytes, skipping whatever junk offset
    the origin decided to send.  A player cannot stall on this."""
    target = _u64d(b64url)
    if not target.startswith("https://"):
        handler._send({"error": "bad direct"}, 400)
        return
    total = _wn_size(target)
    if not total:
        handler._send({"error": "size unknown"}, 502)
        return
    rng = handler.headers.get("Range") or ""
    mr = re.match(r"\s*bytes=(\d+)-(\d*)", rng)
    start = int(mr.group(1)) if mr else 0
    client_end = mr.group(2) if mr else ""
    end = min(int(client_end), total - 1) if client_end else total - 1
    if start >= total or start > end:
        handler.send_response(416)
        handler.send_header("Content-Range", f"bytes */{total}")
        handler.end_headers()
        return
    need = end - start + 1
    handler.send_response(206)
    handler.send_header("Content-Type", "video/x-matroska")
    handler.send_header("Content-Range", f"bytes {start}-{end}/{total}")
    handler.send_header("Content-Length", str(need))
    handler.send_header("Accept-Ranges", "bytes")
    handler.send_header("Access-Control-Allow-Origin", "*")
    handler.send_header("Access-Control-Expose-Headers",
                        "Content-Length, Content-Range, Accept-Ranges")
    handler.send_header("Cache-Control", "no-store")
    handler.send_header("Connection", "close")
    handler.end_headers()
    if handler._is_head or need <= 0:
        return
    try:
        code, up = _wn_plain(target,
                             f"bytes={start}-" if start else None, 45)
        if up is None:
            return                          # headers sent; client retries
        skip = start                        # 200 = whole file from 0
        if code == 206:                     # honoured our start-only rng
            mc = re.match(r"\s*bytes\s+(\d+)-",
                          up.headers.get("Content-Range") or "")
            skip = max(0, start - int(mc.group(1))) if mc else 0
        _wn_pump(handler, up, need, skip)
    except (BrokenPipeError, ConnectionResetError, OSError, TimeoutError):
        pass
    finally:
        try:
            up.close()
        except Exception:
            pass


# ---------------------------------------------------------- http server ----
_admin_fails = {}


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "RareToons2"
    timeout = 75            # idle keep-alive sockets are dropped, not leaked
    disable_nagle_algorithm = True   # headers+body in separate sends cost ~40 ms each otherwise

    def log_message(self, fmt, *args):
        sys.stderr.write("[rt2] " + (fmt % args) + "\n")

    # ------------------------------------------------------ helpers ----
    def _send(self, obj, code=200, ctype="application/json"):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        gz = len(body) > 1500 and "gzip" in (self.headers.get("Accept-Encoding") or "")
        if gz:
            body = gzip.compress(body, 5)
        self.send_response(code)
        if gz:
            self.send_header("Content-Encoding", "gzip")
            self.send_header("Vary", "Accept-Encoding")
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "no-cache")
        self.end_headers()
        self.wfile.write(body)

    def _send_raw(self, body, ctype, code=200):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(body)

    # ------------------------------------------------------- routes ----
    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, HEAD, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "range, origin, "
                          "content-type, accept, authorization")
        self.send_header("Access-Control-Max-Age", "86400")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_HEAD(self):
        self._is_head = True
        self._route()

    def do_GET(self):
        self._is_head = False
        self._route()

    def _token(self):
        a = self.headers.get("Authorization") or ""
        return a[7:] if a.startswith("Bearer ") else ""

    def _body(self):
        try:
            n = min(int(self.headers.get("Content-Length") or 0), 10000)
            return json.loads(self.rfile.read(n) or b"{}")
        except Exception:
            return {}

    def _admin(self, path, b):
        """Admin API. Disabled unless the ADMIN_KEY env var is set."""
        key = os.environ.get("ADMIN_KEY", "")
        ip = (self.headers.get("X-Forwarded-For") or self.client_address[0]).split(",")[0].strip()
        bad = _admin_fails.get(ip, (0, 0))
        if bad[0] >= 5 and time.time() - bad[1] < 600:
            return self._send({"error": "Too many attempts. Try again in 10 minutes."}, 429)
        given = self.headers.get("X-Admin-Key") or ""
        if not key or not hmac.compare_digest(given.encode(), key.encode()):
            _admin_fails[ip] = (bad[0] + 1, time.time())
            return self._send({"error": "Wrong admin key."}, 403)
        _admin_fails.pop(ip, None)
        if path == "/api/admin/stats":
            return self._send(accounts.admin_stats())
        err = None
        if path == "/api/admin/password":
            err = accounts.admin_set_password(str(b.get("username", "")), str(b.get("password", "")))
        elif path == "/api/admin/delete":
            err = accounts.admin_delete(str(b.get("username", "")))
        else:
            return self._send({"error": "not found"}, 404)
        return self._send({"error": err}, 400) if err else self._send({"ok": True})

    def do_POST(self):
        self._is_head = False
        path = unquote(urlparse(self.path).path)
        try:
            b = self._body()
            if path.startswith("/api/admin/"):
                return self._admin(path, b)
            if path in ("/api/signup", "/api/login"):
                fn = accounts.signup if path == "/api/signup" else accounts.login
                tok, err = fn(str(b.get("username", "")).strip(), str(b.get("password", "")))
                if err:
                    return self._send({"error": err}, 400)
                return self._send({"token": tok, "user": accounts.user_for(tok)})
            if path == "/api/logout":
                accounts.logout(self._token())
                return self._send({"ok": True})
            u = accounts.user_for(self._token())
            if not u:
                return self._send({"error": "Please sign in."}, 401)
            if path == "/api/progress":
                slug = str(b.get("slug", ""))[:100]

                def _save(uid=u["id"], b=b, slug=slug):
                    try:
                        accounts.save_progress(uid, slug, b.get("season"), b.get("episode"),
                                               b.get("pos"), b.get("dur"))
                        if float(b.get("dur") or 0) > 0 and float(b.get("pos") or 0) / float(b["dur"]) >= 0.85:
                            accounts.mark_seen(uid, slug, b.get("season"), b.get("episode"))
                    except Exception as e:
                        print("[rt2] progress save failed:", e, flush=True)
                threading.Thread(target=_save, daemon=True).start()
                return self._send({"ok": True})
            if path == "/api/fav":
                accounts.set_fav(u["id"], str(b.get("slug", ""))[:100], bool(b.get("on")))
                return self._send({"ok": True})
            if path == "/api/password":
                err = accounts.change_password(u["id"], self._token(), str(b.get("old", "")), str(b.get("new", "")))
                return self._send({"error": err}, 400) if err else self._send({"ok": True})
            self._send({"error": "not found"}, 404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:
            self._send({"error": str(exc)}, 500)

    def _route(self):
        parsed = urlparse(self.path)
        path = unquote(parsed.path)
        qs = parse_qs(parsed.query)
        _public_base_holder["base"] = public_base_from(self)
        try:
            if path.rstrip("/") in ("", "/"):
                raw, gz = index_page()
                if raw is None:
                    self._send({"addon": ADDON_NAME, "version": VERSION,
                                "status": "ok"})
                    return
                use_gz = "gzip" in (self.headers.get("Accept-Encoding") or "")
                body = gz if use_gz else raw
                self.send_response(200)
                if use_gz:
                    self.send_header("Content-Encoding", "gzip")
                self.send_header("Vary", "Accept-Encoding")
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Cache-Control", "no-cache")
                self.end_headers()
                if not self._is_head:
                    self.wfile.write(body)
                return
            if path == "/status":
                self._send({"addon": ADDON_NAME, "version": VERSION,
                            "status": "ok", "series": len(SERIES),
                            "movies": len(MOVIES), "rows": len(ROWS)})
                return
            m = re.match(r"^/img/s/([a-z0-9_]+)$", path)
            if m:
                rec = SHOWS.get(m.group(1))
                if not rec or not rec.get("poster"):
                    return self._send({"error": "no image"}, 404)
                _serve_img(self, "s:" + m.group(1), rec["poster"])
                return
            m = re.match(rf"^/img/({_B64_RE}+)$", path)
            if m:
                _serve_img(self, m.group(1))
                return
            if path == "/admin":
                with open(os.path.join(BASE_DIR, "admin.html"), "rb") as fh:
                    self._send_raw(fh.read(), "text/html; charset=utf-8")
                return
            if path == "/api/me":
                u = accounts.user_for(self._token())
                if not u:
                    return self._send({"error": "Please sign in."}, 401)
                box = {}
                th = threading.Thread(target=lambda: box.update(f=accounts.get_favs(u["id"])))
                th.start()                                  # the two lookups run in parallel
                prog = accounts.get_progress(u["id"])
                th.join()
                return self._send({"user": u, "progress": prog, "favs": box.get("f", [])})
            m = re.match(r"^/api/seen/([a-z0-9_]+)$", path)
            if m:
                u = accounts.user_for(self._token())
                return self._send({"seen": accounts.get_seen(u["id"], m.group(1)) if u else []})
            if path == "/api/shows":
                raw, gz = shows_payload()
                use_gz = "gzip" in (self.headers.get("Accept-Encoding") or "")
                body = gz if use_gz else raw
                self.send_response(200)
                if use_gz:
                    self.send_header("Content-Encoding", "gzip")
                self.send_header("Vary", "Accept-Encoding")
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Access-Control-Allow-Origin", "*")
                self.send_header("Cache-Control", "no-cache")
                self.end_headers()
                if not self._is_head:
                    self.wfile.write(body)
                return
            m = re.match(r"^/api/watch/([a-z0-9_]+)(?:/(\d+)/(\d+))?$", path)
            if m:
                self._send(api_watch(m.group(1), m.group(2), m.group(3)))
                return
            if path == "/manifest.json":
                self._send(handle_manifest(_public_base_holder["base"]))
                return
            static = {"/logo.png": ("icon-512.png", "image/png"), "/icon-192.png": ("icon-192.png", "image/png"),
                      "/icon-512.png": ("icon-512.png", "image/png"), "/sw.js": ("sw.js", "text/javascript"),
                      "/app.webmanifest": ("app.webmanifest", "application/manifest+json")}
            if path in static:
                try:
                    with open(os.path.join(BASE_DIR, static[path][0]), "rb") as fh:
                        self._send_raw(fh.read(), static[path][1])
                except Exception:
                    # icons are embedded: no PNG file needs to be in the repo
                    emb = _ICONS.get(static[path][0])
                    if emb:
                        self._send_raw(base64.b64decode(emb), static[path][1])
                    elif path == "/sw.js":
                        self._send_raw(b"self.addEventListener('install',()=>self.skipWaiting());", static[path][1])
                    elif path == "/app.webmanifest":
                        self._send_raw(json.dumps({"name": "mollad_jaat", "short_name": "mollad_jaat", "start_url": "/", "display": "standalone", "background_color": "#0b0b0f", "theme_color": "#0b0b0f", "icons": [{"src": "/icon-192.png", "sizes": "192x192", "type": "image/png"}, {"src": "/icon-512.png", "sizes": "512x512", "type": "image/png"}]}).encode(), static[path][1])
                    else:
                        self._send({"error": "not found"}, 404)
                return

            m = re.match(r"^/meta/(series|movie)/(raretoons2:.+)\.json$",
                         path)
            if m:
                meta = handle_meta(m.group(1), m.group(2))
                self._send({"meta": meta} if meta else {"meta": {}},
                           200 if meta else 404)
                return

            m = re.match(r"^/stream/(series|movie)/"
                         r"(raretoons2:[^/]+|tt\d+(?::\d+)*)\.json$", path)
            if m:
                self._send(handle_stream(m.group(1), m.group(2)))
                return

            m = re.match(rf"^/mq/({_B64_RE}+)\.m3u8$", path)
            if m:
                zipper = _mq_decode_token(m.group(1))
                if not zipper.startswith("https://codedew.com/"):
                    self._send({"error": "bad token"}, 400)
                    return
                _serve_m3u8_master(self, zipper)
                return

            m = re.match(rf"^/mq/({_B64_RE}+)/dl/({_B64_RE}+)(\.[A-Za-z0-9]{{1,5}})?$", path)
            if m:
                zipper = _mq_decode_token(m.group(1))
                if not zipper.startswith("https://codedew.com/"):
                    self._send({"error": "bad token"}, 400)
                    return
                _serve_download(self, zipper, m.group(2),
                                (qs.get("name", [""])[0] if qs else ""),
                                check=bool(qs and qs.get("check")))
                return

            m = re.match(rf"^/mq/({_B64_RE}+)/u/({_B64_RE}+)"
                         rf"(\.[A-Za-z0-9]{{1,5}})?$", path)
            if m:
                zipper = _mq_decode_token(m.group(1))
                if not zipper.startswith("https://codedew.com/"):
                    self._send({"error": "bad token"}, 400)
                    return
                _serve_m3u8_child(self, zipper, m.group(2),
                                  (m.group(3) or ".ts").lower(),
                                  rt=(qs.get("rt", [""])[0] if qs else ""))
                return

            m = re.match(rf"^/wn/({_B64_RE}+)$", path)
            if m:
                target = _u64d(m.group(1))
                if target.startswith("https://codedew.com/"):
                    # zipper payload: resolve FRESH at play time - the
                    # card may be hours old, the file link is not
                    u, _kind = _wn_resolve(target, stale_ok=False)
                    if not u:
                        with _hls_lock:
                            _wn_cache.pop(target, None)
                        u, _kind = _wn_resolve(target, stale_ok=False)
                    if not u:
                        self._send({"error": "wn resolve failed"}, 502)
                        return
                    self.close_connection = True
                    _serve_wn_slice(self, _u64(u))
                    return
                if "workers.dev/" in target:     # worker-wrapped (legacy)
                    inner = _wn_inner(target)
                    if not inner.startswith("https://"):
                        self._send({"error": "bad direct"}, 400)
                        return
                    _serve_m3u8_child(self, "", _u64(inner), ".mkv")
                    return
                # legacy bare-URL payload: known file hosts only
                if not (target.startswith("https://")
                        and ("googleusercontent.com" in target
                             or "cloudflarestorage.com" in target)):
                    self._send({"error": "bad direct"}, 400)
                    return
                self.close_connection = True
                _serve_wn_slice(self, m.group(1))
                return

            self._send({"error": "not found"}, 404)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:
            try:
                self._send({"error": str(exc)}, 500)
            except Exception:
                pass


def public_base_from(handler):
    host = handler.headers.get("Host") or ""
    if "." not in host and HOST_SUFFIX and not host.endswith(HOST_SUFFIX):
        host = host + HOST_SUFFIX
    proto = handler.headers.get("X-Forwarded-Proto") or "http"
    return f"{proto}://{host}"


print("[rt2] BOOT v=" + VERSION, flush=True)

def _auto_refresh():
    """Keeps episode lists fresh without a redeploy: re-reads one series'
    hub page every AUTO_REFRESH_SECONDS, oldest-checked first."""
    gap = float(os.environ.get("AUTO_REFRESH_SECONDS", "5"))
    if gap <= 0:
        return
    last = {}
    time.sleep(60)
    while True:
        try:
            with STORE_LOCK:
                slugs = [k for k, r in SHOWS.items() if not r["movie"] and r.get("hub")]
            if slugs:
                slug = min(slugs, key=lambda k: last.get(k, 0))
                last[slug] = time.time()
                rec = SHOWS[slug]
                _absorb_live(rec, _live_rows(rec))
        except Exception as e:
            print("[rt2] auto refresh:", e, flush=True)
        time.sleep(gap)


_INDEX_LOCK = threading.Lock()      # only ONE refresh_index.run at a time


def _reload_catalog():
    """Re-read episodes_index.jsonl and merge new shows/episodes into the
    live SHOWS dict (no restart).  New shows get a poster in background."""
    global ROWS
    ROWS = _load_jsonl(os.path.join(BASE_DIR, "episodes_index.jsonl"))
    with STORE_LOCK:
        _build_shows()
        missing = [r for r in SHOWS.values() if not r.get("poster")]
    for rec in missing:
        _bg_once(("poster", rec["slug"]), lambda rec=rec: _fetch_poster(rec))


def _fresh_tick(feed_pages):
    """Look at the site's newest posts (RSS).  Known shows are re-read at
    once (new episodes show up now, not hours later); unknown hubs trigger
    an index refresh so brand-new shows appear."""
    import refresh_index as RI
    links = []
    for page in range(1, feed_pages + 1):
        r = requests.get(f"{SITE}feed/?paged={page}", headers={"User-Agent": UA},
                         timeout=20)
        for it in re.findall(r"<item>(.*?)</item>", r.text or "", re.S):
            m = re.search(r"<link>(.*?)</link>", it, re.S)
            if m:
                links.append(m.group(1).strip())
    if not links:
        return
    with STORE_LOCK:
        by_hub = {RI.strong(r["hub"]): r for r in SHOWS.values() if r.get("hub")}
    unknown, touched = False, 0
    for u in dict.fromkeys(links):
        rec = by_hub.get(RI.strong(u))
        if rec:
            with _live_lock:
                _live_cache.pop(rec.get("hub"), None)
            try:
                _absorb_live(rec, _live_rows(rec))
                touched += 1
            except Exception:
                pass
        elif RI.is_real_hub(u):
            unknown = True
    added = 0
    if unknown and _INDEX_LOCK.acquire(blocking=False):
        try:
            before = len(SHOWS)
            RI.run(feed_pages=feed_pages, quiet=True)
            _reload_catalog()
            added = len(SHOWS) - before
        finally:
            _INDEX_LOCK.release()
    print(f"[rt2] fresh watch: {touched} shows re-read, +{added} new shows", flush=True)


def _fresh_watch():
    """Every FRESH_SECONDS (default 10 min) pull newly posted episodes and
    shows from the site feed."""
    gap = float(os.environ.get("FRESH_SECONDS", "600"))
    pages = int(os.environ.get("FRESH_FEED_PAGES", "2"))
    if gap <= 0:
        return
    time.sleep(45)
    while True:
        t0 = time.time()
        try:
            _fresh_tick(pages)
        except Exception as e:
            print("[rt2] fresh watch failed:", repr(e), flush=True)
        time.sleep(max(30.0, gap - (time.time() - t0)))


def _catalog_refresh():
    """Finds shows missing from the catalog and adds them, so Home/Search
    stop missing anime that's on the site but never made it into our
    crawled snapshot. _auto_refresh above only revisits shows already in
    SHOWS; this is the piece that discovers shows we don't have yet.

    Two passes, both merged into the live SHOWS dict without a restart
    (existing shows/posters untouched):
      - recent (every CATALOG_REFRESH_SECONDS, default 6h): RSS feed +
        home page only, fast, catches brand-new uploads.
      - full backfill (every CATALOG_FULL_REFRESH_SECONDS, default 24h):
        ALSO walks the whole /hindi/page/N/ archive from page 1, so shows
        that are weeks/months old and simply never got crawled in the
        first place (the original gap, not just a freshness gap) get
        picked up too. Slower, so it runs less often."""
    gap = float(os.environ.get("CATALOG_REFRESH_SECONDS", str(6 * 3600)))
    full_gap = float(os.environ.get("CATALOG_FULL_REFRESH_SECONDS", str(24 * 3600)))
    if gap <= 0:
        return
    time.sleep(120)
    last_full = 0.0
    first = True
    while True:
        try:
            import refresh_index
            do_full = full_gap > 0 and (first or time.time() - last_full >= full_gap)
            first = False
            if do_full:
                last_full = time.time()
            before = len(SHOWS)
            with _INDEX_LOCK:
                summary = refresh_index.run(quiet=True, full=do_full)
                _reload_catalog()
            added = len(SHOWS) - before
            if added or summary:
                print(f"[rt2] catalog refresh ({'full' if do_full else 'recent'}): "
                      f"+{added} new shows", flush=True)
        except Exception as e:
            print("[rt2] catalog refresh failed:", e, flush=True)
        time.sleep(gap)


def main():
    threading.Thread(target=_tmdb_boot, daemon=True).start()
    threading.Thread(target=_auto_refresh, daemon=True).start()
    threading.Thread(target=_catalog_refresh, daemon=True).start()
    threading.Thread(target=_fresh_watch, daemon=True).start()
    threading.Thread(target=_tmdb_backfill, daemon=True).start()
    threading.Thread(target=shows_payload, daemon=True).start()   # warm /api/shows
    threading.Thread(target=_img_prewarm, daemon=True).start()    # posters -> disk
    _updates(); _popular(); _trending("week"); _trending("day")   # warm the caches at boot
    port = int(sys.argv[1]) if len(sys.argv) > 1 else PORT
    srv = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    print(f"[rt2] {ADDON_NAME} v{VERSION} | series={len(SERIES)} "
          f"movies={len(MOVIES)} rows={len(ROWS)} posters={len(POSTERS)}")
    print(f"[rt2] listening on 0.0.0.0:{port}")
    srv.serve_forever()


if __name__ == "__main__":
    main()
