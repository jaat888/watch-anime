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
import difflib
import zlib
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

import applog
applog.install()          # keep every printed line + crashes in the SQL `logs` table
import accounts
import guard                 # protection plan: real IP, PROTECT mode, VIP keys
import captcha               # protection plan Step 7: game captcha (server side) + pass token
import genres as G
import skiptimes
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

VERSION  = "3.6.0"
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


_JUNK_HUB_RE = re.compile(r"comment-page|replytocom|\?")


def _canon_hub(u):
    return re.sub(r"/comment-page-\d+/?$", "/", (u or "").split("#")[0].split("?")[0])


def _clean_rows(rows):
    """WordPress comment-pagination copies of a hub (/comment-page-N/,
    ?replytocom=) carry the SAME episodes with freshly randomised zipper
    tokens, so they never dedupe by link.  Drop those copies whenever the real
    hub has rows; for a hub only ever seen through copies keep the first copy
    (rewritten to the canonical URL)."""
    clean_hubs = {_canon_hub(r.get("hub_url")) for r in rows
                  if not _JUNK_HUB_RE.search(r.get("hub_url") or "")}
    first, out = {}, []
    for r in rows:
        u = r.get("hub_url") or ""
        if not _JUNK_HUB_RE.search(u):
            out.append(r)
            continue
        c = _canon_hub(u)
        if c in clean_hubs:
            continue
        if first.setdefault(c, u) == u:
            r["hub_url"] = c
            out.append(r)
    return out

ROWS = _clean_rows(_load_jsonl(os.path.join(BASE_DIR, "episodes_index.jsonl")))


def _hub_key(r):
    return (r.get("hub_url") or "").split("#")[0].rstrip("/").lower()


def _hub_hashes(rows):
    """hub -> md5 of its rows (order independent)."""
    by = {}
    for r in rows:
        by.setdefault(_hub_key(r), []).append(json.dumps(r, sort_keys=True, ensure_ascii=False))
    return {k: hashlib.md5("\n".join(sorted(v)).encode("utf-8")).hexdigest() for k, v in by.items()}


POSTERS = {}
try:
    with open(os.path.join(BASE_DIR, "posters.json"), encoding="utf-8") as fh:
        POSTERS = json.load(fh)
except Exception:
    pass


def _display(show):
    """Human hub name; Subbed/Dubbed variants must stay distinct."""
    s = re.split(r"\s+(?:[-–]\s+)?(?:Hindi|Tamil|Telugu|WatchMulti|Multi|English(?=\s+(?:Sub|Dub))|Download\b)",
                 show or "", maxsplit=1)[0].strip(" -–")
    s = re.sub(r"\s*(?:[-–]\s*)?Episodes?\.?\s*$", "", s, flags=re.I).strip(" -–")
    # movie titles: "X (2025) Movie" / "X (Movie - 2021)" -> "X (2025)" / "X (2021)"
    s = re.sub(r"\(\s*Movie\s*[-–:]?\s*(\d{4})\s*\)", r"(\1)", s, flags=re.I)
    s = re.sub(r"(\(\s*\d{4}\s*\))\s*Movie\s*$", r"\1", s, flags=re.I)
    s = re.sub(r"\s+", " ", s).strip(" -–")
    if re.search(r"subbed", show or "", re.I):
        s += " (Eng Sub)" if re.search(r"english", show or "", re.I) else " (Hindi Sub)"
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
        applog.log_once("tmdb-save", 300, "error", "app", f"tmdb save failed (last: {slug}): {e!r}")


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


_DB_READY = threading.Event()      # set once the last saved state was read back from the DB
_TMDB_LOADED = threading.Event()


def _tmdb_boot():
    """Background boot: load the whole tmdb table, fill genres/desc/rating into
    the already-built SHOWS, then run the one-time genre migration."""
    global _TMDB_CACHE
    delay = 5
    while True:                      # DB asleep? keep trying - never fall back to re-fetching everything
        try:
            loaded = accounts.tmdb_all()
            break
        except Exception as e:
            print(f"[rt2] tmdb cache load failed (DB asleep?), retry in {delay}s: {repr(e)}", flush=True)
            time.sleep(delay)
            delay = min(delay * 2, 120)
    _TMDB_LOADED.set()
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
        r["hub_url"] = re.sub(r"/comment-page-\d+/?$", "/",
                              (r.get("hub_url") or "").split("#")[0].split("?")[0])
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
        # rebuild-safe + mirror-safe: the same link under another hub URL
        # (WordPress comment-page / ?replytocom copies) is NOT a new row
        if not any(o.get("lang") == r.get("lang") and o.get("mq") == r.get("mq")
                   and o.get("sb") == r.get("sb") for o in lst):
            lst.append(r)
    for rec in SHOWS.values():
        # season-less hubs (Hagemaru, Luckyman, Monster Kid, AoT OAD ...) have
        # many episodes under season 0: that is a SERIES (as season 1), not a
        # movie - otherwise their new episodes never show up.  Real movies
        # have a single (0, n) entry.
        if rec["eps"] and all((k[0] or 0) == 0 for k in rec["eps"]) and len(rec["eps"]) > 1:
            rec["eps"] = {(1, k[1]): v for k, v in rec["eps"].items()}
            for rows in rec["eps"].values():
                for r in rows:
                    r["season"] = 1
        rec["movie"] = all((k[0] or 0) == 0 for k in rec["eps"]) if rec["eps"] else False
        rec["poster"] = rec["poster"] or POSTERS.get(rec["site_name"], "")
        rec["genres"] = _TMDB_CACHE.get(rec["slug"], {}).get("g", [])
        rec["desc"] = _TMDB_CACHE.get(rec["slug"], {}).get("d", "")
        rec["rating"] = _TMDB_CACHE.get(rec["slug"], {}).get("r")


_build_shows()
SERIES = [r for r in SHOWS.values() if not r["movie"]]
MOVIES = [r for r in SHOWS.values() if r["movie"]]

# what shipped with this deploy (taken AFTER _build_shows, which normalises some
# rows): anything that differs later is saved to the DB
BASE_HUBS = _hub_hashes(ROWS)
BASE_SIG = hashlib.md5(json.dumps(sorted(BASE_HUBS.items())).encode("utf-8")).hexdigest()

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


def _cf_blocked(text):
    """True when the body is a Cloudflare challenge page instead of the site."""
    t = (text or "")[:6000].lower()
    return "just a moment" in t or "cf-chl" in t or "attention required! | cloudflare" in t


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
captcha.configure(_TK)            # the captcha pass token is signed with the same secret
threading.Thread(target=captcha.load_cfg, daemon=True).start()     # Step 8: game numbers saved from the lab come back after a restart

# ---- Step 3: session-bound links --------------------------------------------
# Old (Stremio / VIP / guard off) link : sealed(zipper)                    -> no session, works as before.
# Website link (guard on or log)       : sealed("v2" kind sid ip-key expiry zipper), parts split by \x1f.
#   kind "s" = stream (playlist + every segment), kind "d" = download.  The SAME token rides along in
#   every rewritten playlist URL, so segments are bound to the same IP / session / expiry.
_SEP = "\x1f"


def _mq_new(zipper, sess, kind="s", life=None, uid=""):
    """Session-bound token.  kind: s stream (HLS), w WN stream, d download.  life = seconds (capped by the
    session's own expiry).  uid = the signed-in account (download links only)."""
    exp = sess["exp"] if not life else min(sess["exp"], time.time() + life)
    return _seal(_SEP.join(("v3", kind, sess["sid"], sess["ipk"], "%d" % exp, str(uid or ""), zipper)))


def _mq_parse(tok):
    """token -> {"z","kind","sid","ipk","exp","uid"} or None.  Old tokens come back with sid "" (no session)."""
    plain = _unseal(tok)
    if not plain:
        return None
    try:
        if plain.startswith("v3" + _SEP):
            _, kind, sid, ipk, exp, uid, z = plain.split(_SEP, 6)
            return {"z": z, "kind": kind, "sid": sid, "ipk": ipk, "exp": float(exp), "uid": uid}
        if plain.startswith("v2" + _SEP):            # made by Step 3 (a player tab that is still open)
            _, kind, sid, ipk, exp, z = plain.split(_SEP, 5)
            return {"z": z, "kind": kind, "sid": sid, "ipk": ipk, "exp": float(exp), "uid": ""}
    except Exception:
        return None
    return {"z": plain, "kind": "", "sid": "", "ipk": "", "exp": 0.0, "uid": ""}


def _wn_proxied():
    """Do WN (movie) streams go through our own /wn proxy?  auto = only once PROTECT=on.
    WN_PROXY=1 forces it (to test in dry-run), WN_PROXY=0 keeps the direct origin link."""
    v = (os.environ.get("WN_PROXY") or "auto").strip().lower()
    if v in ("0", "off", "no"):
        return False
    if v in ("1", "on", "yes"):
        return True
    return guard.mode() == "on"


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
        _resp = upstream_get(hub, referer=SITE)
        page = _resp.text or ""
        if _resp.status_code != 200 or _cf_blocked(page):
            applog.log_once("live-" + str(_resp.status_code), 300, "error", "live",
                            f"hub fetch blocked/failed HTTP {_resp.status_code}"
                            f"{' (Cloudflare challenge)' if _cf_blocked(page) else ''}: {hub}")
            page = ""
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
    except Exception as e:
        applog.log_once("live-exc-" + type(e).__name__, 300, "error", "live",
                        f"hub parse failed {hub}: {e!r}")
        rows = []
    if not rows and rec.get("hub"):
        applog.log_once("live-empty-" + hub, 3600, "warn", "live", f"no episodes parsed from {hub}")
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
            applog.log_once("jikan-" + type(e).__name__, 600, "error", "jikan",
                            f"jikan lookup failed (e.g. '{name}'): {str(e)[-160:]}  - same error is hidden for 10 min")
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
        applog.log_once("tmdb-" + type(e).__name__, 600, "error", "tmdb",
                        f"tmdb lookup failed (e.g. '{slug}'): {str(e)[-160:]}  - same error is hidden for 10 min")
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
    _TMDB_LOADED.wait(900)           # only look things up that the DB really does not have
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
              kind="fsl", qres="", wz=""):
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
            **({"rt2z": wz} if wz else {}),      # WN: the site's own button link (fresh-resolved by /wn)
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


# ------------------------------------------------- episode titles ---
# "S1 E1" -> "S1 E1 · The Iceblade Sorcerer ...".  Order: AniList (the
# Crunchyroll titles) -> TMDB -> nothing (the page then keeps plain "S1 E1").
# Only the TITLE is taken.  Results live in memory + the same SQL table the
# TMDB info uses (key "ept:<slug>", "gf":1 keeps the genre migration away).
ANILIST_URL = "https://graphql.anilist.co"
EPT_TTL_OK = 14 * 86400      # every wanted episode has a title
EPT_TTL_NEW = 6 * 3600       # some wanted episode still has none (airing show)
EPT_TTL_NF = 24 * 3600       # nothing found anywhere -> look again daily
EPT_RETRY = 600              # network error -> try again after ~10 min
EPT_VER = 2                  # bump = every saved title list is thrown away and fetched again (v1 could hold
                             # the SEASON 1 titles under a Season 2 show)
_EPT_FAIL = {}               # slug -> time of last network failure (memory only)
_ept_lock = threading.Lock()
_ANILIST_Q = ("query($q:String){Page(perPage:8){media(search:$q,type:ANIME,"
              "sort:SEARCH_MATCH){id format episodes title{romaji english}"
              " synonyms streamingEpisodes{title}}}}")
_EPT_NUM_RE = re.compile(
    r"^\s*(?:episode|ep\.?|e)\s*(\d{1,4})\s*[-\u2013\u2014:.]\s*(.+?)\s*$", re.I)
_EPT_GENERIC_RE = re.compile(r"^\s*(?:episode|ep\.?|e)\s*\d{0,4}\s*$", re.I)


def _ept_norm(s):
    return re.sub(r"[^a-z0-9]+", " ", (s or "").lower()).strip()


def _ept_season_hint(title):
    """Season number a title mentions ('... Season 2', '3rd Season', 'II'), else 0."""
    t = _ept_norm(title)
    m = (re.search(r"\bseason (\d{1,2})\b", t) or re.search(r"\b(\d{1,2})(?:st|nd|rd|th) season\b", t)
         or re.search(r"\bpart (\d{1,2})\b", t))
    if m:
        return int(m.group(1))
    m = re.search(r"\b(ii|iii|iv|v|vi)\b$", t)
    return {"ii": 2, "iii": 3, "iv": 4, "v": 5, "vi": 6}[m.group(1)] if m else 0


def _ept_clean_title(t):
    t = re.sub(r"\s+", " ", (t or "")).strip()
    if not t or _EPT_GENERIC_RE.match(t):
        return ""
    return t[:160]


def _ept_covers(titles, eps):
    """True when the title list really belongs to this season of the show
    (guards against absolute numbering, e.g. AniList's One Piece 1089+)."""
    return bool(eps) and len(set(titles) & set(eps)) / len(eps) >= 0.6


def _ept_anilist(name, season, eps):
    """{episode: title} from AniList's streamingEpisodes (Crunchyroll titles)."""
    query = name if season <= 1 else f"{name} Season {season}"
    r = requests.post(ANILIST_URL, json={"query": _ANILIST_Q, "variables": {"q": query}},
                      timeout=8, headers={"Accept": "application/json"})
    r.raise_for_status()
    media = ((r.json().get("data") or {}).get("Page") or {}).get("media") or []
    want = _ept_norm(name)
    best, best_score = None, 0.0
    for m in media:
        if not m.get("streamingEpisodes"):
            continue
        names = [(m.get("title") or {}).get("english"), (m.get("title") or {}).get("romaji")] + list(m.get("synonyms") or [])
        score = 0.0
        for nm in names:
            if not nm:
                continue
            base = _ept_norm(re.sub(r"\b(?:season|part)\s*\d+\b|\b\d+(?:st|nd|rd|th) season\b", " ", nm, flags=re.I))
            score = max(score, difflib.SequenceMatcher(None, want, base).ratio())
        hint = max((_ept_season_hint(nm) for nm in names if nm), default=0)
        full = max((difflib.SequenceMatcher(None, want, _ept_norm(nm)).ratio() for nm in names if nm), default=0)
        if season > 1:
            if hint == season:
                score += 0.15
            elif hint:               # an entry that names ANOTHER season is never the answer
                score -= 0.5
            elif full >= 0.97:       # plain "<Show>" with no season word = the FIRST season, never season 2+
                score -= 0.5
        elif hint > 1:
            score -= 0.5
        if (m.get("format") or "") in ("MOVIE", "MUSIC", "SPECIAL"):
            score -= 0.3
        if score > best_score:
            best, best_score = m, score
    if not best or best_score < 0.6:
        return {}
    out, pos = {}, 0
    for se in best["streamingEpisodes"]:
        pos += 1
        mm = _EPT_NUM_RE.match(se.get("title") or "")
        if mm:
            n, t = int(mm.group(1)), _ept_clean_title(mm.group(2))
        else:
            n, t = pos, _ept_clean_title(se.get("title"))
        if t and n not in out:
            out[n] = t
    return out if _ept_covers(out, eps) else {}


def _ept_tmdb(name, season, eps):
    """{episode: title} from TMDB /tv/{id}/season/{n}; placeholder names skipped."""
    want = _ept_norm(name)
    cands = _tmdb_get("/search/tv", query=name, language="en-US").get("results") or []
    tried = 0
    for c in cands[:5]:
        sim = max(difflib.SequenceMatcher(None, want, _ept_norm(c.get(k))).ratio()
                  for k in ("name", "original_name"))
        if sim < 0.6:
            continue
        tried += 1
        if tried > 3:
            break
        try:
            j = _tmdb_get(f"/tv/{c['id']}/season/{season}", language="en-US")
        except requests.HTTPError as e:           # no such season on this entry
            if getattr(e.response, "status_code", 0) == 404:
                continue
            raise
        out = {}
        for ep in j.get("episodes") or []:
            t = _ept_clean_title(ep.get("name"))
            if t and ep.get("episode_number") is not None:
                out[int(ep["episode_number"])] = t
        if _ept_covers(out, eps):
            return out
    return {}


def _ept_fetch(rec):
    """-> ({"s:e": title}, network_failed)."""
    with STORE_LOCK:
        want = {}
        for (s, e) in rec["eps"]:
            if e:
                want.setdefault(s or 1, set()).add(e)
    name = _tmdb_clean(rec["name"])
    out, failed = {}, False
    for s, eps in want.items():
        got = {}
        try:
            got = _ept_anilist(name, s, eps)
        except requests.RequestException:
            failed = True
        except Exception:
            got = {}
        if set(eps) - set(got):                   # AniList missed some -> TMDB fills only those
            try:
                for e, t in _ept_tmdb(name, s, eps).items():
                    got.setdefault(e, t)
            except requests.RequestException:
                failed = True
            except Exception:
                pass
        for e, t in got.items():
            if e in eps:
                out[f"{s}:{e}"] = t
    return out, failed


def _ept_job(rec):
    slug = rec["slug"]
    out, failed = _ept_fetch(rec)
    if failed and not out:
        _EPT_FAIL[slug] = time.time()             # nothing cached: retried in ~10 min
        return
    _EPT_FAIL.pop(slug, None)
    entry = {"gf": 1, "t": time.time(), "m": out, "v": EPT_VER}
    with _tmdb_lock:
        _TMDB_CACHE["ept:" + slug] = entry
    try:
        accounts.tmdb_set("ept:" + slug, entry)
    except Exception as e:
        applog.log_once("ept-save", 300, "error", "app", f"episode titles save failed ({slug}): {e!r}")


def _ept_ent(slug):
    """Saved title list of this show - only if it was made by the current rules (older ones may be wrong)."""
    ent = _TMDB_CACHE.get("ept:" + slug)
    return ent if isinstance(ent, dict) and ent.get("v") == EPT_VER else None


def _ep_titles(rec, wait=0.0):
    """-> ({"s:e": title}, pending).  Never raises, never blocks longer than `wait` s.
    A stale entry is served at once and refreshed in the background."""
    slug = rec["slug"]
    try:
        with STORE_LOCK:
            wanted = {f"{s or 1}:{e}" for (s, e) in rec["eps"] if e}
        ent = _ept_ent(slug)
        age = time.time() - float(ent.get("t", 0)) if isinstance(ent, dict) else None
        m = (ent or {}).get("m") or {} if isinstance(ent, dict) else {}
        if age is not None:
            ttl = EPT_TTL_OK if wanted <= set(m) else (EPT_TTL_NEW if m else EPT_TTL_NF)
            if age > ttl:
                _bg_once(("ept", slug), lambda r=rec: _ept_job(r))
            return m, False
        if time.time() - _EPT_FAIL.get(slug, 0) < EPT_RETRY:
            return {}, False
        _bg_once(("ept", slug), lambda r=rec: _ept_job(r))
        t0 = time.time()
        while time.time() - t0 < wait:
            time.sleep(0.1)
            ent = _ept_ent(slug)
            if isinstance(ent, dict):
                return ent.get("m") or {}, False
            if time.time() - _EPT_FAIL.get(slug, 0) < EPT_RETRY:
                return {}, False
        return {}, True
    except Exception:
        return {}, False



_live_inflight = {}          # hub -> Event, set when that hub's live refresh finished
META_LIVE_WAIT = float(os.environ.get("META_LIVE_WAIT", "0.5"))


def _live_soft(rec, wait):
    """Like _absorb_live(rec, _live_rows(rec)) but the CALLER waits at most
    `wait` seconds: a cold hub fetch (Cloudflare-fronted site, 5-10 s) keeps
    running in the background and merges when done.  -> True if finished."""
    hub = rec.get("hub")
    if not hub:
        return True
    with _live_lock:
        hit = _live_cache.get(hub)
        fresh = bool(hit and hit[0] > time.time())
        ev = None if fresh else _live_inflight.get(hub)
        start = False
        if not fresh and ev is None:
            ev = _live_inflight[hub] = threading.Event()
            start = True
    if fresh:
        _absorb_live(rec, hit[1])
        return True
    if start:
        def _run(rec=rec, hub=hub, ev=ev):
            try:
                _absorb_live(rec, _live_rows(rec))
            except Exception:
                pass
            finally:
                with _live_lock:
                    _live_inflight.pop(hub, None)
                ev.set()
        threading.Thread(target=_run, daemon=True, name="live-soft").start()
    return ev.wait(wait)


def handle_meta(mtype, mid):
    slug = mid.split(":", 1)[1] if ":" in mid else mid
    rec = SHOWS.get(slug)
    if not rec:
        return None
    # SPEED: the detail page used to wait for the live hub fetch (5-10 s when
    # the cache was cold), then the poster fetch (up to 10 s), then TMDB (3 s).
    # Now: a show that already has episodes opens at once (live refresh keeps
    # running in the background, 2 s max wait); only a show with NO episodes
    # yet (brand-new) waits for the site.
    t_meta = time.monotonic()
    META_BUDGET = 1.0                     # ONE shared wait for everything below
    try:                                  # start TMDB info + episode titles NOW
        _show_info(rec, wait=0)           # (background threads) so the site
        _ep_titles(rec, wait=0.0)         # fetch, TMDB and titles run in PARALLEL
    except Exception:
        pass
    try:
        with STORE_LOCK:
            has_eps = bool(rec["eps"])
        live_done = _live_soft(rec, META_LIVE_WAIT if has_eps else RESOLVE_TIMEOUT + 4)
    except Exception:
        live_done = True
    if not rec.get("poster"):
        _bg_once(("poster", slug), lambda rec=rec: _fetch_poster(rec))
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
    info = _show_info(rec, wait=max(0.0, META_BUDGET - (time.monotonic() - t_meta)))
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
        titles, pending = _ep_titles(rec, wait=max(0.0, META_BUDGET - (time.monotonic() - t_meta)))
        for v in vids:
            t = titles.get(f"{v['season']}:{v['episode']}")
            if t:
                v["title"] = v["name"] = t
        if pending or not live_done:        # app re-asks soon -> picks up the late data
            meta["ept_pending"] = True
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
                                     base, src="WN", kind=kind, qres=wq, wz=z))
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
    # western animated movies (not anime)
    "toy story", "minions", "despicable me", "cloudy with a chance", "spirit untamed",
    "atlantis", "shrek", "kung fu panda", "ice age", "madagascar", "moana", "zootopia",
    "the incredibles", "finding nemo", "finding dory", "how to train your dragon",
    "hotel transylvania", "puss in boots", "lion king", "wreck-it ralph", "big hero 6",
    "grand theft auto", "super mario", "sonic the hedgehog", "angry birds", "the croods",
    "megamind", "coraline", "boss baby", "chicken run", "inside out", "monsters, inc",
    "monsters inc", "encanto",
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
    added = _added()
    for it in items:
        it["upd"] = int(upd.get(it["slug"], 0))
        it["add"] = int(added.get(it["slug"], 0))
        if it["poster"].startswith("https://"):
            it["poster"] = "/img/s/" + it["slug"]      # short link; hides the source site
    top_rated, top_movies, recent, recent_movies = _derived_lists(items)
    for it in items:
        if it["slug"] in _EN:
            it["en"] = _EN[it["slug"]]
    if guard.mode() != "off":                       # Step 6: fake anime for the honeypot (the website hides z:1)
        items.extend(guard.decoy_items(list(items)))
    items.sort(key=lambda x: x["name"].lower())
    return {"shows": items, "now": int(time.time()), "popular": _popular(),
            "trending": _trending("week"),
            "trending_day": _trending("day"),
            "trending_movies": _trending("movies"),
            "top_rated": top_rated, "top_movies": top_movies,
            "recent": recent, "recent_movies": recent_movies}


def _al_top(rows, is_movie, rated, limit):
    """Top Rated like AniList's own list (score order) but only what we carry
    WITH Hindi; one entry per franchise (its first season, the rest sit behind
    the season picker).  The shortfall is topped up with our own best-rated."""
    keyf = _mv_key if is_movie else _fr_key
    hi = [it for it in rows if "Hindi" in (it.get("langs") or [])]
    fam = {}
    for it in hi:
        fam.setdefault(keyf(it["name"]), []).append(it)
    lst = _al["mtop" if is_movie else "top"]
    out, seen = [], set()
    if lst and fam:
        for fk, _sc, m in _match_al_list(lst, _fam_matcher(list(fam)), 100.0):
            its = fam[fk]
            rep_ = min(its, key=lambda it: (_season_no(it["name"]), it["ord"]))
            if rep_["slug"] in seen:
                continue
            seen.add(rep_["slug"])
            if m.get("sc"):
                rep_["rating"] = round(m["sc"] / 10.0, 1)      # AniList score, same 0-10 scale
            _note_en(rep_["name"], rep_["slug"], m)
            out.append(rep_["slug"])
            if len(out) >= limit:
                return out
    done = {keyf(it["name"]) for it in rows if it["slug"] in seen}
    for it in rated(hi) + rated(rows):                       # top-up: Hindi first, then the rest
        k = keyf(it["name"])
        if k in done:
            continue
        done.add(k)
        out.append(it["slug"])
        if len(out) >= limit:
            break
    return out


def _derived_lists(items):
    """Top rated / Recently added lists (slugs), one entry per franchise.
    Pure in-memory; cheap enough to recompute with every payload build."""
    ok = [it for it in items if it["kind"] == "anime" and it["poster"]]

    def pick(rows, keyf, n):
        seen, out = set(), []
        for it in rows:
            k = keyf(it)
            if k in seen:
                continue
            seen.add(k)
            out.append(it["slug"])
            if len(out) >= n:
                break
        return out

    ser = [it for it in ok if not it["movie"]]
    mov = [it for it in ok if it["movie"]]
    rated = lambda rows: sorted((it for it in rows if it.get("rating")),
                                key=lambda it: (-float(it["rating"]), -it["n"], it["ord"]))
    top_rated = _al_top(ser, False, rated, TOP_RATED_N)
    top_movies = _al_top(mov, True, rated, TOP_MOVIES_N)
    newest = lambda rows: sorted(rows, key=lambda it: (-it["add"], -it["ord"]))
    recent = pick(newest(ser), lambda it: _fr_key(it["name"]), RECENT_N)
    recent_movies = pick(newest(mov), lambda it: _mv_key(it["name"]), RECENT_N)
    return top_rated, top_movies, recent, recent_movies


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


_img_fail = {}                       # token -> time of last failed upstream fetch
_img_sem = threading.Semaphore(6)    # at most 6 poster fetches to the source at once


def _img_load(token, url):
    try:
        return _img_load2(token, url)
    except Exception as e:           # network/TLS/Cloudflare hiccup must never become a 500
        _img_fail[token] = time.time()
        print("[img] fetch failed:", token[:24], repr(e)[:120], flush=True)
        return None


def _img_load2(token, url):
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
    if time.time() - _img_fail.get(token, 0) < 300:   # failed recently: don't hammer the source
        return None
    with _walk_lock_for("img:" + token), _img_sem:    # one upstream fetch per image
        hit = _img_cache.get(token)
        if hit:
            return hit
        r = upstream_get(url, referer=SITE, timeout=10)
        ctype = r.headers.get("content-type") or ""
        if r.status_code != 200 or "image" not in ctype:
            _img_fail[token] = time.time()
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
    try:
        url = url or _unseal(token)
    except Exception:
        url = ""
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


# --------------------------------- AniList + own-signal trending (DB-backed) ---
# India/Hindi-first trending, anime only (no cartoons).  Series and movies are
# ranked SEPARATELY ("week" / "day" -> series, "movies" -> movies only).
#
# Everything slow or remote is saved in the database (accounts.kv) so a
# restart/redeploy never starts from zero:
#   al_cache / al_meta   last AniList answer + when it was fetched
#   trend_<window>       last finished list per window
#   added_at             first time each show was seen (Recently added)
#   sync_t               last hourly sync
# AniList is asked at most once per AL_TTL (1 h).  When the answer is the same
# as the stored one nothing is written; a failed answer never replaces the last
# complete one.
#
# Signals (series): AniList trending rank, AniList airing-now popularity rank,
# new episode on OUR site recently, distinct users watching on our site.
# Only shows that exist on our site WITH Hindi are eligible; ONE entry per
# franchise (the newest season) - never "Season 1" and "Season 4" together.
TREND_TTL = _env_int("TREND_TTL", 3600)
AL_TTL = _env_int("ANILIST_TTL", 3600)
SYNC_SECONDS = _env_int("SYNC_SECONDS", 3600)
TREND_N = {"week": _env_int("TREND_WEEK_N", 80),
           "day": _env_int("TREND_DAY_N", 50),
           "movies": _env_int("TREND_MOVIES_N", 40)}
TOP_RATED_N = _env_int("TOP_RATED_N", 55)
TOP_MOVIES_N = _env_int("TOP_MOVIES_N", 40)
RECENT_N = _env_int("RECENT_N", 40)
AL_URL = "https://graphql.anilist.co"
_al = {"t": 0.0, "ok": 0.0, "trend": [], "air": [], "mtrend": [], "mpop": [],
       "top": [], "mtop": [],
       "busy": False, "err": "", "h": ""}
_trend_cache = {w: {"t": 0.0, "data": [], "busy": False, "h": ""}
                for w in ("day", "week", "movies")}


def _kv_float(k, default=0.0):
    try:
        return float(accounts.kv_get(k) or default)
    except Exception:
        return default


def _kv_put(k, v):
    try:
        accounts.kv_set(k, v if isinstance(v, str) else str(v))
        return True
    except Exception as e:
        applog.log_once("kv-" + k, 300, "warn", "app", f"db save '{k}' failed: {e!r}")
        return False


def _h(obj):
    return hashlib.md5(json.dumps(obj, sort_keys=True, separators=(",", ":"),
                                  ensure_ascii=False).encode("utf-8")).hexdigest()


def _tn_norm(s):
    return re.sub(r"[^a-z0-9]+", "", (s or "").lower())


_FR_NOISE = re.compile(r"\b(?:oad|ova|ona|specials?|recap|movie|the\s+movie|tv)\b", re.I)
_YEAR = re.compile(r"\(?\b(?:19|20)\d{2}\b\)?")


def _fr_key(name):
    """Franchise key: season / part / dub / OAD words removed
    ('AoT Season 2 (Hindi Dub)' and 'AoT OAD' -> same key)."""
    s = _tmdb_clean(name)
    s = _FR_NOISE.sub(" ", s)
    s = _YEAR.sub(" ", s)
    return _tn_norm(s) or _tn_norm(name)


def _mv_key(name):
    """Movie key: year / 'Movie' / language words removed."""
    s = _tmdb_clean(name)
    s = re.sub(r"\b(?:the\s+)?movie\b", " ", s, flags=re.I)
    s = _YEAR.sub(" ", s)
    return _tn_norm(s) or _tn_norm(name)


def _al_slim(m):
    t = m.get("title") or {}
    return {"i": m.get("id"), "t": [t.get("romaji"), t.get("english"), t.get("native")],
            "s": list(m.get("synonyms") or [])[:6], "f": m.get("format"),
            "sc": m.get("averageScore") or 0}


def _al_page(sort, page, status=None, fmt=None):
    var = {"p": page, "sort": [sort]}
    decl, args = "$p:Int,$sort:[MediaSort]", "type:ANIME,sort:$sort,countryOfOrigin:JP,isAdult:false"
    if status:
        var["st"] = status
        decl += ",$st:MediaStatus"
        args += ",status:$st"
    if fmt:
        var["fm"] = fmt
        decl += ",$fm:MediaFormat"
        args += ",format:$fm"
    q = ("query(%s){Page(page:$p,perPage:50){media(%s){id title{romaji english native} "
         "synonyms format status trending popularity averageScore}}}" % (decl, args))
    r = creq.post(AL_URL, json={"query": q, "variables": var},
                  headers={"User-Agent": UA, "Accept": "application/json"},
                  timeout=20, impersonate="chrome")
    if r.status_code != 200:
        raise RuntimeError(f"anilist HTTP {r.status_code} {(r.text or '')[:120]!r}")
    j = r.json()
    if j.get("errors"):
        raise RuntimeError("anilist error " + str(j["errors"])[:160])
    return ((j.get("data") or {}).get("Page") or {}).get("media") or []


def _al_list(sort, pages, status=None, fmt=None):
    out = []
    for p in range(1, pages + 1):
        res = _al_page(sort, p, status, fmt)
        if not res:
            raise RuntimeError(f"anilist {sort} page {p} empty")
        out += res
        time.sleep(0.7)               # AniList allows ~90 req/min
    return out


def _al_titles(m):
    names = list(m.get("t") or []) + list(m.get("s") or [])
    ks = []
    for n in names:
        k = _fr_key(n) if n else ""
        if len(k) >= 4 and k not in ks:
            ks.append(k)
    return ks


def _al_load_db():
    """Boot: take the last AniList answer from the database (no network)."""
    try:
        raw = accounts.kv_get("al_cache")
        meta = json.loads(accounts.kv_get("al_meta") or "{}")
        if raw:
            d = json.loads(raw)
            t_db = float(meta.get("t") or 0)
            if t_db <= _al["t"]:
                return                           # already fetched something newer meanwhile
            _al.update({k: d.get(k) or [] for k in ("trend", "air", "mtrend", "mpop", "top", "mtop")})
            _al["h"] = meta.get("h") or _h(d)
            _al["t"] = t_db
            _al["ok"] = _al["t"]
            print(f"[trend] AniList restored from DB ({len(_al['trend'])} trending, "
                  f"{len(_al['mtrend'])} movies), age {int(time.time() - _al['t'])}s", flush=True)
    except Exception as e:
        print("[trend] AniList restore failed:", repr(e), flush=True)


def _al_refresh():
    """Reload the AniList lists.  All-or-nothing.  Returns True when the
    answer DIFFERS from the stored one (and was saved), False otherwise."""
    try:
        d = {"trend": _al_list("TRENDING_DESC", 3),
             "air": _al_list("POPULARITY_DESC", 2, status="RELEASING"),
             "mtrend": _al_list("TRENDING_DESC", 2, fmt="MOVIE"),
             "mpop": _al_list("POPULARITY_DESC", 2, fmt="MOVIE"),
             # AniList "Top Rated" = score order (TV series / movies kept apart, like our site)
             "top": _al_list("SCORE_DESC", 4, fmt="TV"),
             "mtop": _al_list("SCORE_DESC", 2, fmt="MOVIE")}
    except Exception as e:
        _al["err"] = repr(e)[:200]
        _al["t"] = time.time() - AL_TTL + 300         # retry in 5 min
        applog.log_once("al-fail", 600, "error", "trend",
                        f"AniList refresh failed (keeping last good list, "
                        f"{len(_al['trend'])} titles): {_al['err']}")
        return False
    d = {k: [_al_slim(m) for m in v] for k, v in d.items()}
    # trending rank shifts constantly, so compare the SET of titles per list
    sig = _h({k: sorted(str(m["i"]) for m in v) for k, v in d.items()})
    changed = sig != _al["h"]
    now = time.time()
    _al.update(d, t=now, ok=now, err="")
    if changed:
        _al["h"] = sig
        _kv_put("al_cache", json.dumps(d, separators=(",", ":"), ensure_ascii=False))
    _kv_put("al_meta", json.dumps({"t": now, "h": _al["h"]}))
    print(f"[trend] AniList ok: {len(d['trend'])} trending, {len(d['air'])} airing, "
          f"{len(d['mtrend'])} movies ({'changed' if changed else 'unchanged'})", flush=True)
    return changed


_BOOT_T = time.time()


def _al_ensure():
    # cold DB: wait (max 5 min) for the saved AniList answer before asking AniList again
    if not _DB_READY.is_set() and time.time() - _BOOT_T < 300:
        return
    if time.time() - _al["t"] > AL_TTL and not _al["busy"]:
        _al["busy"] = True

        def _run():
            try:
                _al_refresh()
            finally:
                _al["busy"] = False
        threading.Thread(target=_run, daemon=True).start()


def _season_no(name):
    m = re.search(r"season\s*0*(\d+)|(\d+)(?:st|nd|rd|th)\s+season", name or "", re.I)
    return int(m.group(1) or m.group(2)) if m else 1


def _rating_of(slug):
    try:
        return float((_TMDB_CACHE.get(slug) or {}).get("r") or 0)
    except (TypeError, ValueError):
        return 0.0


def _fresh_w(ts, now, steps):
    if not ts:
        return 0.0
    age = (now - ts) / 3600.0
    return next((v for lim, v in steps if age <= lim), 0.0)


_EN = {}          # slug -> English title from AniList (only where the site name is not English)


def _note_en(rec_name, slug, m):
    """Remember AniList's English title when the site's own name is romaji/mixed."""
    try:
        en = ((m.get("t") or [None, None])[1] or "").strip()
        if not en:
            return
        site = _tn_norm(_tmdb_clean(rec_name))
        base = _tn_norm(en)
        if not base or base in site or site in base:
            return                                   # site name already says it in English
        sn = _season_no(rec_name)
        if sn > 1 and not re.search(r"season\s*\d|\d(?:st|nd|rd|th)\s+season|part\s*\d", en, re.I):
            en += f" Season {sn}"
        _EN[slug] = en
    except Exception:
        pass


def _match_al_list(lst, fam_for, n):
    """AniList list (in AniList's own order) -> [(franchise key, rank score 0..1, entry)],
    each franchise once, at its best AniList position."""
    seen, out = set(), []
    for rank, m in enumerate(lst):
        for k in _al_titles(m):
            fk = fam_for(k)
            if fk:
                if fk not in seen:
                    seen.add(fk)
                    out.append((fk, 1.0 - rank / n, m))
                break
    return out


def _fam_matcher(keys):
    ks = set(keys)
    klist = list(keys)

    def fam_for(k):
        if k in ks:
            return k
        if len(k) >= 8:                        # strict prefix, never loose fuzzy
            for fk in klist:
                if len(fk) >= 8:
                    s_, l_ = (k, fk) if len(k) <= len(fk) else (fk, k)
                    if l_.startswith(s_) and len(s_) / len(l_) >= 0.75:
                        return fk
        return None
    return fam_for


def _build_trending(window):
    """-> ordered [slug,...], best first.  SERIES only (movies have their own list)."""
    now = time.time()
    span = 86400 if window == "day" else 7 * 86400
    try:
        watch = accounts.recent_watch(now - span)
    except Exception as e:
        applog.log_once("tw-fail", 600, "warn", "trend", f"watch-count query failed: {e!r}")
        watch = {}
    upd = _updates()
    with STORE_LOCK:
        recs = [r for r in SHOWS.values()
                if not r["movie"] and _kind(r["name"]) == "anime" and "Hindi" in _show_langs(r)]
    fam = {}                                   # franchise key -> [rec]
    for r in recs:
        fam.setdefault(_fr_key(r["name"]), []).append(r)
    keys = list(fam)

    def fam_for(k):
        if k in fam:
            return k
        if len(k) >= 8:                        # strict prefix, never loose fuzzy
            for fk in keys:
                if len(fk) >= 8:
                    s, l = (k, fk) if len(k) <= len(fk) else (fk, k)
                    if l.startswith(s) and len(s) / len(l) >= 0.75:
                        return fk
        return None

    score = {}                                 # franchise key -> {"a":..,"t":..}
    for src, lst, n in (("t", _al["trend"], 150.0), ("a", _al["air"], 100.0)):
        for rank, m in enumerate(lst):
            if m.get("f") == "MOVIE":
                continue
            for k in _al_titles(m):
                fk = fam_for(k)
                if fk:
                    d = score.setdefault(fk, {})
                    if 1.0 - rank / n > d.get(src, 0.0):
                        d[src] = 1.0 - rank / n
                        if src == "t":
                            d["m"] = m
                    break
    for fk in fam:                             # own signals can add shows AniList missed
        score.setdefault(fk, {})

    steps = ((24, 1.0), (72, 0.6), (168, 0.3)) if window == "day" else ((72, 1.0), (168, 0.7), (336, 0.3))
    # AniList's own "Trending Now" order leads; our site signals only nudge it
    wt = (0.50, 0.10, 0.25, 0.15) if window == "day" else (0.55, 0.15, 0.15, 0.15)
    ranked, rest = [], []
    for fk, d in score.items():
        rs = fam[fk]
        # ONE entry per franchise: the newest season (never S1 next to S4)
        best = max(rs, key=lambda r: (_season_no(r["name"]), upd.get(r["slug"], 0) or 0, len(r["eps"])))
        fr = max(_fresh_w(upd.get(r["slug"], 0), now, steps) for r in rs)
        wc = sum(watch.get(r["slug"], 0) for r in rs)
        s = (wt[0] * d.get("t", 0) + wt[1] * d.get("a", 0) + wt[2] * fr + wt[3] * min(1.0, wc / 5.0))
        if d.get("t") or d.get("a"):
            m_ = d.get("m")
            if m_:
                _note_en(best["name"], best["slug"], m_)
        if s > 0:
            ranked.append((s, best["slug"]))
        else:
            rest.append((max(_rating_of(r["slug"]) for r in rs), best["slug"]))
    ranked.sort(key=lambda x: -x[0])
    out = [slug for _s, slug in ranked]
    # not enough signals for a long list -> top up with the best-rated franchises
    rest.sort(key=lambda x: -x[0])
    out += [slug for _r, slug in rest]
    return out[:TREND_N[window]]


def _al_movie_match(recs_keys, lst, n):
    """AniList movie list -> {slug: best 0..1 rank score}."""
    out = {}
    for rank, m in enumerate(lst):
        for k in _al_titles(m):
            hit = None
            for slug, rk in recs_keys:
                if rk == k:
                    hit = slug
                elif len(k) >= 8 and len(rk) >= 8:
                    s, l = (k, rk) if len(k) <= len(rk) else (rk, k)
                    if s in l and len(s) / len(l) >= 0.6:
                        hit = slug
                if hit:
                    out[hit] = max(out.get(hit, 0.0), 1.0 - rank / n)
                    break
            if hit:
                break
    return out


def _build_trending_movies():
    now = time.time()
    added = _added()
    with STORE_LOCK:
        recs = [r for r in SHOWS.values() if r["movie"] and _kind(r["name"]) == "anime"]
    rk = [(r["slug"], _mv_key(r["name"])) for r in recs]
    tr = _al_movie_match(rk, _al["mtrend"], 100.0)
    pop = _al_movie_match(rk, _al["mpop"], 100.0)
    steps = ((24 * 30, 1.0), (24 * 90, 0.6), (24 * 180, 0.3))
    ranked, rest = [], []
    for r in recs:
        sl = r["slug"]
        rating = _rating_of(sl)
        s = (0.40 * tr.get(sl, 0) + 0.25 * pop.get(sl, 0)
             + 0.15 * _fresh_w(added.get(sl, 0), now, steps) + 0.20 * min(1.0, rating / 10.0))
        if "Hindi" not in _show_langs(r):
            s *= 0.7
        # real signal = AniList knows it; the rest only tops the list up
        if tr.get(sl) or pop.get(sl):
            ranked.append((s, sl))
        elif rating >= 6.8:
            rest.append((s, sl))
    ranked.sort(key=lambda x: -x[0])
    rest.sort(key=lambda x: -x[0])
    out = [sl for _s, sl in ranked]
    if len(out) < 20:                       # too few signals: top up with the best-rated movies
        out += [sl for _s, sl in rest][:20 - len(out)]
    return out[:TREND_N["movies"]]


def _trend_load_db():
    for w, c in _trend_cache.items():
        try:
            raw = accounts.kv_get("trend_" + w)
            if raw:
                data = json.loads(raw)
                if isinstance(data, list) and not c["t"]:      # not rebuilt yet
                    c["data"] = data
                    c["h"] = _h(data)
        except Exception as e:
            print("[trend] restore failed:", w, repr(e), flush=True)


def _trend_rebuild(window):
    """Rebuild one list; save to the DB only when it actually changed.  -> changed?"""
    c = _trend_cache[window]
    data = _build_trending_movies() if window == "movies" else _build_trending(window)
    nh = _h(data)
    changed = nh != c["h"]
    c.update(t=time.time(), data=data, h=nh)
    if changed:
        _kv_put("trend_" + window, json.dumps(data, separators=(",", ":")))
    return changed


def _trending(window="week"):
    """Cached list for the website.  Never blocks; refreshes in background."""
    _al_ensure()
    c = _trend_cache[window]
    if time.time() - c["t"] > TREND_TTL and not c["busy"]:
        c["busy"] = True

        def _run():
            try:
                _trend_rebuild(window)
                if not _al["ok"]:
                    applog.log_once("tr-noal", 900, "warn", "trend",
                                    f"{window}: AniList not loaded yet - using own signals only ({len(c['data'])})")
            except Exception as e:
                applog.log_once("tr-fail-" + window, 300, "error", "trend",
                                f"{window} build failed: {e!r}")
                c["t"] = time.time() - TREND_TTL + 120
            finally:
                c["busy"] = False
        threading.Thread(target=_run, daemon=True).start()
    return list(c["data"])


# ------------------------------------------- first-seen / episode tracking ---
_upd_cache = {"t": 0, "data": {}, "added": {}}


def _updates():
    """slug -> unix time its episode count last grew (0 = since tracking began).
    Never blocks a request: serves the cached copy and refreshes in the background."""
    if time.time() - _upd_cache["t"] >= 600 and not _upd_cache.get("busy"):
        _upd_cache["busy"] = True
        threading.Thread(target=_updates_refresh, daemon=True).start()
    return _upd_cache["data"]


def _added():
    """slug -> unix time the show first appeared (Recently added)."""
    _updates()
    return _upd_cache["added"]


def _poster_ts(rec):
    """Old shows: upload month of the poster image ~ when the hub was created."""
    m = re.search(r"/uploads/(\d{4})/(\d{2})/", rec.get("poster") or "")
    if not m:
        return 0
    try:
        import calendar
        return calendar.timegm((int(m.group(1)), int(m.group(2)), 15, 0, 0, 0))
    except Exception:
        return 0


def _updates_refresh():
    now = time.time()
    try:
        with STORE_LOCK:
            counts = {slug: len(rec["eps"]) for slug, rec in SHOWS.items()}
            posters = {slug: _poster_ts(rec) for slug, rec in SHOWS.items()}
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
        # first-seen time per show (kept in the DB, so it survives restarts)
        araw = accounts.kv_get("added_at")
        aold = json.loads(araw) if araw else None
        added, adirty = {}, aold is None
        for slug in counts:
            o = (aold or {}).get(slug)
            if o is None:
                added[slug] = posters.get(slug, 0) if aold is None else int(now)
                adirty = True
            else:
                added[slug] = o
        if adirty:
            accounts.kv_set("added_at", json.dumps(added, separators=(",", ":")))
        _upd_cache.update(t=now, data={k: v[1] for k, v in new.items()}, added=added)
    except Exception as e:
        applog.log_once("upd-track", 300, "error", "app", f"updates tracking failed: {e}")
        _upd_cache["t"] = now - 540      # retry in ~1 minute
    finally:
        _upd_cache["busy"] = False


def api_watch(slug, season, episode, sess=None):
    """Playable sources for one episode/movie, simplified for the website.
    sess (guard.sess_open) -> every MQ link is bound to that session (Step 3)."""
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
            if sess:
                mt = re.match(rf"^/mq/({_B64_RE}+)\.m3u8$", url)
                z = _unseal(mt.group(1)) if mt else ""
                if z.startswith("https://codedew.com/"):
                    url = f"/mq/{_mq_new(z, sess, 's')}.m3u8"
        elif sess and _wn_proxied():
            wz = (c.get("behaviorHints") or {}).get("rt2z") or ""
            tgt = wz if wz.startswith("https://codedew.com/") else url
            if tgt.startswith("https://"):
                url = f"/wn/{_mq_new(tgt, sess, 'w')}"      # same-origin, bound to this IP + session
        out.append({"lang": (ml.group(1).strip() if ml else "Default"),
                    "kind": "mq" if is_mq else "direct",
                    "quality": mq.group(1) if mq else "",
                    "url": url})
    res_ = {"name": rec["name"], "sources": out}
    if sess:
        res_["sess"] = True                 # tells the player to send heartbeats
    return res_


def api_skip(slug, season, episode):
    """Skip-intro / skip-ending candidates for the website player (see skiptimes.py).
    Never raises and never touches the stream path: no data -> {"segments": []}."""
    rec = SHOWS.get(slug)
    if not rec:
        return {"segments": []}
    try:
        return skiptimes.lookup(
            _tmdb_clean(rec["name"]), season or 1, episode or 1, bool(rec["movie"]), _tmdb_get,
            log=lambda prov, msg: applog.log_once(
                "skip-" + prov, 600, "warn", "skip",
                f"skip-times via {prov} failed ({msg}) - same error is hidden for 10 min"))
    except Exception as e:
        applog.log_once("skip-" + type(e).__name__, 600, "error", "skip", f"skip lookup crashed: {e}")
        return {"segments": []}


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
    body = _rewrite_m3u8(text or "", master,
                         f"/mq/{getattr(handler, '_mqtok', '') or _mq_token(zipper)}").encode()
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
    proxy_prefix = f"/mq/{getattr(handler, '_mqtok', '') or _mq_token(zipper)}"
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


def _serve_wn_slice(handler, b64url, attach=None):
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
    full = bool(attach) and not mr          # a download without Range: plain 200 + attachment
    handler.send_response(200 if full else 206)
    handler.send_header("Content-Type", "video/x-matroska")
    if attach:
        fn = re.sub(r"[^\w\-. ]+", "", attach).strip().replace(" ", "_")[:80] or "video"
        if not fn.lower().endswith(".mkv"):
            fn += ".mkv"
        handler.send_header("Content-Disposition", f'attachment; filename="{fn}"')
    if not full:
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


# ----------------------------------------------- Step 3: heartbeat, dl token --
def api_hb(tok, ip, vip):
    """Heartbeat of the website player (every 30 s).  The player is told to fetch a fresh link
    (renew) when its link is nearly over, or - once PROTECT=on - when it is no longer valid."""
    try:
        p = _mq_parse(tok)
        if not p:
            return {"ok": False, "renew": True, "why": "bad"}
        if not p["sid"] or vip:
            return {"ok": True, "renew": False}
        why = guard.sess_check(p, ip, "s", beat=True)
        left = int(p["exp"] - time.time())
        if why and guard.violation("session:" + why, ip, "heartbeat"):
            return {"ok": False, "renew": True, "why": why}
        return {"ok": True, "left": left, "renew": left < guard.SESS_RENEW_LEFT}
    except Exception:
        return {"ok": True, "renew": False}


def api_dltok(tok, ip, vip, uid=None):
    """Stream link (HLS or WN) -> separate short-lived download link.  Download needs a signed-in
    account (uid); without it: violation (blocked only once PROTECT=on)."""
    p = _mq_parse(tok)
    if not p or not p["z"].startswith("https://"):
        return {"error": "bad token"}, 400
    if not p["sid"] or vip:
        return {"tok": tok}, 200            # unbound link (Stremio / VIP / guard off)
    why = guard.sess_check(p, ip, p["kind"])
    if why and guard.violation("session:" + why, ip, "download token"):
        return {"error": "Session ended. Please reload the video.", "renew": True, "why": why}, 403
    if not uid and guard.violation("dl_login", ip, "download without sign-in"):
        return {"error": "Download ke liye pehle sign in karo.", "login": True}, 401
    sess = {"sid": p["sid"], "ipk": p["ipk"], "exp": p["exp"]}
    return {"tok": _mq_new(p["z"], sess, "d", guard.DL_LIFE, uid=uid)}, 200


# ---------------------------------------------------------- http server ----
_admin_fails = {}
_shadow_sem = threading.BoundedSemaphore(25)       # at most 25 banned visitors are slowed down at once (Step 6)


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
                          "content-type, accept, authorization, x-vip-key, x-device, x-captcha")
        self.send_header("Access-Control-Max-Age", "86400")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_HEAD(self):
        self._is_head = True
        self._route()

    def do_GET(self):
        self._is_head = False
        self._route()

    def _gctx(self, qs=None):
        """Per request: real IP + VIP check (guard.py). Never breaks the request."""
        self._mqtok = ""            # one Handler serves many keep-alive requests: never reuse an old token
        self._mquid = ""
        self._dev, self._banned, self._pass, self._tvn = "", "", False, ""
        try:
            self._ip = guard.client_ip(self.headers, self.client_address[0])
            self._vip = guard.is_vip(self.headers, qs, self._ip)    # key name or None
            self._pass = (not self._vip) and captcha.check_pass(self.headers.get("X-Captcha"), self._ip)   # Step 7: passed a captcha lately
            if not self._vip and not self._pass:      # Step 9: or a TV pass (a phone played the game for this TV)
                self._tvn = captcha.check_tv_pass(self.headers.get("X-Captcha"), self._ip)
                self._pass = bool(self._tvn)
            self._dev = guard.device_id(self.headers)               # the browser's random id (X-Device), or ""
            self._banned = "" if self._vip else guard.is_banned(self._ip, self._dev)   # Step 6: why, or ""
            guard.note(self._ip)
        except Exception:
            self._ip, self._vip = self.client_address[0], None

    # ---- Step 5 / 6 helpers -------------------------------------------------
    def _limit(self, name, win, ip_max, dev_max=0, detail=""):
        """Request-rate rule (Step 5).  True = answered with 429 (only when PROTECT=on) - stop."""
        if self._vip:
            return False
        if guard.rate(name, self._ip, self._dev, win, ip_max, dev_max, detail or name):
            self._send({"error": "Thoda ruko - bahut zyada requests.", "retry": win}, 429)
            return True
        return False

    def _trap(self, slug, how):
        """Step 6 honeypot: a fake anime was asked for.  True = visitor is banned now (PROTECT=on)."""
        if self._vip or not guard.is_decoy(slug):
            return False
        if guard.trap(self._ip, self._dev, slug, how):
            self._banned = "jaal: nakli anime"
            return True
        return False

    def _quiet(self, kind):
        """Step 6: a banned visitor gets an empty, error-free answer (a little slow for data routes).
        True = answered, stop.  Dry-run (PROTECT=log) only logs and returns False."""
        if not self._banned or self._vip:
            return False
        if not guard.violation("banned", self._ip, self._banned, dev=self._dev):
            return False
        if kind != "mq" and _shadow_sem.acquire(blocking=False):
            try:
                time.sleep(2.5)
            finally:
                _shadow_sem.release()
        if kind == "watch":
            self._send({"name": "", "sources": []})
        elif kind == "stream":
            self._send({"streams": []})
        elif kind == "meta":
            self._send({"meta": {}}, 404)
        elif kind == "mq":
            self._send({"error": "session idle", "renew": True, "why": "idle"}, 403)
        else:
            self._send({"error": "not found"}, 404)
        return True

    def _pre(self, kind, slug=None):
        """Front door of the data routes: fake-anime trap, behaviour count, ban check.
        True = the request was answered quietly - stop."""
        if self._vip:
            return False
        if slug:
            self._trap(slug, kind)
        guard.track(kind, self._ip, self._dev)
        return self._quiet(kind)

    def _watch(self, slug, season, episode):
        """/api/watch - the video links for the website (Step 3 session + Step 5 rules)."""
        ip, dev = self._ip, self._dev
        if self._vip or guard.mode() == "off":
            return self._send(api_watch(slug, season, episode, None if self._vip else guard.sess_open(ip)))
        if self._pre("watch", slug):
            return
        if slug not in SHOWS:                         # unknown (or fake) anime: nothing to hand out
            return self._send(api_watch(slug, season, episode, None))
        if guard.check_score(ip, dev):                # Step 6: behaves like a bot -> banned (PROTECT=on)
            self._banned = "bot score"
            if self._quiet("watch"):
                return
        # 1. the anime's page must have been opened first (the website opens it and retries by itself)
        if not guard.was_opened(ip, dev, slug):
            if guard.violation("no_detail", ip, "video link for %s without opening its page" % slug, dev=dev):
                return self._send({"error": "Pehle anime ka page kholo.", "open": True}, 403)
        # 1a. Step 9: a TV pass is good for TV_VIDEOS different videos; after that the QR comes again
        if self._tvn:
            okv, _nv = captcha.tv_video(self._tvn, "%s:%s:%s" % (slug, season or "", episode or ""))
            if not okv:
                self._pass, self._tvn = False, ""
                if guard.captcha_needed(ip, "TV pass: %d video ho gaye" % captcha.TV_VIDEOS, dev=dev):
                    return self._send({"error": "TV ke liye naya QR scan karo.", "captcha": True, "why": "tv pass khatam"}, 403)
        # 1b. Step 7: unusual activity (many videos at once / bot score) -> game captcha, unless one was passed lately
        if not self._pass:
            why = self._captcha_why(slug, season, episode)
            if why and guard.captcha_needed(ip, why, dev=dev):
                return self._send({"error": "Ek chhota game khelo, phir video chalega.", "captcha": True, "why": why}, 403)
        # 2. guest: max GUEST_MAX different videos, then sign-in
        try:
            u = accounts.user_for(self._token())
        except Exception:
            u = None
        if not u and guard.guest_start(ip, dev, "%s:%s:%s" % (slug, season or "", episode or "")):
            return self._send({"error": "Guest ke %d video ho gaye. Aage ke liye sign in karo." % guard.GUEST_MAX,
                               "signin": True}, 401)
        # 3. at most CONC_MAX streams at the same time from one IP
        if guard.conc_check(ip, dev):                 # (True only when PROTECT=on)
            if not self._pass:                        # Step 7: too many at once -> captcha first, not a plain error
                return self._send({"error": "Ek chhota game khelo, phir video chalega.", "captcha": True,
                                   "why": "ek saath %d se zyada video" % guard.CONC_MAX}, 403)
            if len(guard.live_streams(ip)) >= captcha.CONC_HARD:     # even a proven human has a ceiling
                return self._send({"error": "Is IP se %d se zyada video ek saath nahi chal sakte." % captcha.CONC_HARD,
                                   "busy": True}, 429)
        sess = guard.sess_open(ip, dev=dev)
        if u and sess:                                # Step 10: one account = one stream, the latest wins
            old = guard.acct_stream(u["id"], sess["sid"], "%s:%s:%s" % (slug, season or "", episode or ""), dev, ip)
            if old:
                guard.sess_end(old)
        if self._tvn and sess:                        # Step 9: one TV pass = one stream, the latest wins
            old = captcha.tv_stream(self._tvn, sess["sid"], "%s:%s:%s" % (slug, season or "", episode or ""))
            if old:
                guard.sess_end(old)
        self._send(api_watch(slug, season, episode, sess))

    def _captcha_why(self, slug, season, episode):
        """Step 7: is there a reason to ask the game captcha?  -> text, or "" (all normal)."""
        try:
            n = captcha.burst(self._ip, "%s:%s:%s" % (slug, season or "", episode or ""))
            if n >= captcha.BURST_MAX:
                return "%d alag video %d sec me" % (n, captcha.BURST_WIN)
            sc, why = guard.score_of(self._ip, self._dev)
            if sc >= guard.FLAG_SCORE:
                return "bot score %d%% (%s)" % (sc, "; ".join(why)[:120])
        except Exception:
            pass
        return ""

    def _is_admin(self):
        key = os.environ.get("ADMIN_KEY", "")
        given = self.headers.get("X-Admin-Key") or ""
        return bool(key) and hmac.compare_digest(given.encode(), key.encode())

    def _captcha(self, path, b):
        """/api/captcha/new | verify | status  (Step 7).  The admin key unlocks lab mode (own type / numbers,
        full detail back) for the game lab of Step 8."""
        ip, dev = self._ip, self._dev
        if path == "/api/captcha/status":
            return self._send({"pass": bool(self._pass or self._vip), "vip": bool(self._vip), "mode": guard.mode(),
                               "tv": bool(self._tvn), "tv_left": captcha.tv_left(self._tvn) if self._tvn else 0})
        if path not in ("/api/captcha/new", "/api/captcha/verify"):
            return self._send({"error": "not found"}, 404)
        if self._banned and self._quiet("captcha"):               # banned: quiet, slow, nothing to learn from
            return
        lab = bool(b.get("lab")) and self._is_admin()
        if not lab and self._limit("captcha", 60, 20, 8, "/api/captcha"):      # the admin's game lab plays freely
            return
        if path == "/api/captcha/new":
            g = captcha.new(ip, dev, typ=b.get("type") if lab else None, over=b.get("cfg") if lab else None)
            if not g:
                return self._send({"error": "captcha error"}, 500)
            return self._send(g)
        return self._send(captcha.verify(b.get("id"), ip, b, lab=lab))

    def _tv(self, path, b):
        """/api/tv/new | poll | done | check  (Step 9).  The TV shows a QR, a phone plays the game, the TV gets a pass."""
        ip = self._ip
        if self._banned and self._quiet("captcha"):               # banned: quiet and slow, like the captcha routes
            return
        if path == "/api/tv/new":
            if self._limit("tvnew", 60, 8, 4, "/api/tv/new"):
                return
            g = captcha.tv_new(ip)
            return self._send(g) if g else self._send({"error": "tv error"}, 500)
        if path == "/api/tv/poll":                                # the TV asks every 2 s (2 TVs on one IP fit)
            if self._limit("tvpoll", 60, 120, 60, "/api/tv/poll"):
                return
            return self._send(captcha.tv_poll(b.get("pid"), ip))
        if path == "/api/tv/check":                               # the phone page: is this code still open?
            if self._limit("tvcheck", 60, 20, 10, "/api/tv/check"):
                return
            return self._send({"ok": captcha.tv_peek(b.get("code"))})
        if path == "/api/tv/done":                                # the phone hands in the pass of the game it just won
            if self._limit("tvdone", 60, 10, 6, "/api/tv/done"):
                return
            ok, why = captcha.tv_finish(b.get("code"), ip, self.headers.get("X-Captcha"))
            return self._send({"ok": True}) if ok else self._send({"ok": False, "why": why}, 400)
        return self._send({"error": "not found"}, 404)

    def _mq_gate(self, tok, want, any_z=False):
        """Check a /mq link (and its session).  Returns the zipper, or None after answering the request.
        want: "s" playlist/segments, "d" download.  Old unbound links (Stremio) skip the session check."""
        p = _mq_parse(tok)
        if not p or not p["z"].startswith("https://" if any_z else "https://codedew.com/"):
            self._send({"error": "bad token"}, 400)
            return None
        if self._banned and self._quiet("mq"):          # Step 6: banned visitor, old link
            return None
        if p["sid"] and not self._vip:
            why = guard.sess_check(p, self._ip, want)
            if why and guard.violation("session:" + why, self._ip, "/mq " + want):
                self._send({"error": "session " + why, "renew": True, "why": why}, 403)
                return None
        self._mqtok = tok
        self._mquid = p.get("uid") or ""
        return p["z"]

    def _dl_slot(self, tok):
        """Count a running download (max DL_MAX at once per account).  Returns the key to release,
        "" = nothing to release, None = refused (answer already sent)."""
        p = _mq_parse(tok)
        if not p or not p["sid"] or self._vip:
            return ""
        key = ("u" + p["uid"]) if p.get("uid") else ("i" + p["ipk"])
        n = guard.dl_begin(key)
        if n > guard.DL_MAX and guard.violation("dl_limit", self._ip, "%d downloads at once (%s)" % (n, key)):
            guard.dl_end(key)
            self._send({"error": "Ek saath max %d download. Pehla khatam hone do." % guard.DL_MAX}, 429)
            return None
        return key

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
        ip = getattr(self, "_ip", None) or guard.client_ip(self.headers, self.client_address[0])
        bad = _admin_fails.get(ip, (0, 0))
        if bad[0] >= 5 and time.time() - bad[1] < 600:
            return self._send({"error": "Too many attempts. Try again in 10 minutes."}, 429)
        given = self.headers.get("X-Admin-Key") or ""
        if not key or not hmac.compare_digest(given.encode(), key.encode()):
            _admin_fails[ip] = (bad[0] + 1, time.time())
            applog.log_once("adminfail:" + ip, 60, "warn", "admin", "wrong admin key from " + ip)
            return self._send({"error": "Wrong admin key."}, 403)
        _admin_fails.pop(ip, None)
        if path == "/api/admin/stats":
            try:
                return self._send(accounts.admin_stats())
            except Exception as e:     # database down/damaged: still answer, so the panel can show the repair buttons
                return self._send({"total": 0, "users": [], "error": str(e), "sql": accounts.sql_state()})
        if path == "/api/admin/db":
            act = str(b.get("action") or "info")
            if act not in ("info", "check", "sync", "discard"):
                return self._send({"error": "unknown action"}, 400)
            if act == "discard" and b.get("confirm") is not True:
                return self._send({"error": "send confirm:true to reload the database from Telegram"}, 400)
            res = accounts.db_admin(act)
            applog.info("admin", f"db {act}: {json.dumps(res, default=str)[:300]}")
            return self._send(res, 400 if res.get("error") else 200)
        if path == "/api/admin/logs":
            def _i(v, d):
                try:
                    return int(v)
                except Exception:
                    return d
            rows, origin = applog.query(limit=_i(b.get("limit"), 200), level=str(b.get("level") or "all"),
                                        src=str(b.get("src") or "")[:24], text=str(b.get("text") or "")[:100],
                                        before=_i(b.get("before"), 0))
            return self._send({"rows": rows, "origin": origin, "sources": applog.sources(),
                               "stats": applog.stats()})
        if path == "/api/admin/logs/clear":
            try:
                applog.clear()
            except Exception as e:
                return self._send({"error": "clear failed: %s" % e}, 500)
            return self._send({"ok": True})
        if path == "/api/admin/catalog":
            act = str(b.get("action") or "status")
            if act == "start":
                ok, msg = _force_catalog_start(bool(b.get("full", True)))
                if not ok:
                    return self._send({"error": msg, **_force_state_view()}, 409)
            elif act != "status":
                return self._send({"error": "unknown action"}, 400)
            return self._send(_force_state_view())
        if path == "/api/admin/captcha":
            act = str(b.get("action") or "stats")
            if act == "cfg":
                captcha.set_cfg(b.get("cfg"), reset=bool(b.get("reset")), save=True)     # Step 8: kept in the DB too
            elif act != "stats":
                return self._send({"error": "unknown action"}, 400)
            return self._send(captcha.stats())
        if path == "/api/admin/guard":
            act = str(b.get("action") or "info")
            try:
                if act == "mode":
                    guard.set_mode(b.get("mode"))
                elif act == "vip_new":
                    res = guard.vip_new(b.get("name"))
                    return self._send({**res, **guard.info(self.headers, self.client_address[0])})
                elif act == "vip_del":
                    if not guard.vip_del(b.get("id")):
                        return self._send({"error": "Key nahi mili."}, 404)
                elif act == "ban":
                    try:
                        hrs = max(0.0, min(24 * 365.0, float(b.get("hours") or 0)))
                    except Exception:
                        hrs = 0.0
                    guard.ban(b.get("key"), "admin ne ban kiya", hrs)
                elif act == "unban":
                    if not guard.unban(b.get("key")):
                        return self._send({"error": "Ye ban list me nahi tha."}, 404)
                elif act not in ("info", "bots"):
                    return self._send({"error": "unknown action"}, 400)
            except ValueError as e:
                return self._send({"error": str(e)}, 400)
            except Exception as e:           # database down: say so, do not crash the panel
                return self._send({"error": "Database error: %s" % e}, 500)
            res_ = guard.info(self.headers, self.client_address[0])
            res_["captcha"] = captcha.stats()
            if act in ("bots", "ban", "unban"):
                res_["bots"] = guard.bot_list()
                res_["ban_list"] = guard.ban_list()
            return self._send(res_)
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
        self._gctx(parse_qs(urlparse(self.path).query))
        try:
            b = self._body()
            if path.startswith("/api/admin/"):
                return self._admin(path, b)
            if path.startswith("/api/captcha/"):
                return self._captcha(path, b)
            if path.startswith("/api/tv/"):
                return self._tv(path, b)
            if path in ("/api/signup", "/api/login"):
                return self._auth(path, b)
            if path == "/api/logout":
                accounts.logout(self._token())
                return self._send({"ok": True})
            u = accounts.user_for(self._token())
            if not u:
                return self._send({"error": "Please sign in."}, 401)
            if path == "/api/progress":
                if not self._vip:
                    guard.track("prog", self._ip, self._dev)
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

    def _auth(self, path, b):
        """/api/signup and /api/login (Step 10).
        Signup: game captcha ALWAYS (one passed game pays for ONE account), max SIGNUP_MAX accounts per IP (DB).
        Sign-in: captcha only when it looks like guessing (many wrong passwords / many tries).
        PROTECT=off: nothing extra.  log: only writes it down.  on: real 403 {captcha:true} / 429.  VIP: no rule."""
        ip, dev = self._ip, self._dev
        user, pw = str(b.get("username", "")).strip(), str(b.get("password", ""))
        guarded = (not self._vip) and guard.mode() != "off"
        tok_in = self.headers.get("X-Captcha")
        if guarded and self._banned and self._quiet("auth"):
            return
        if path == "/api/signup":
            if guarded:
                if self._limit("signup", 60, 10, 5, "/api/signup"):
                    return
                # 1. captcha every time: a pass that already paid for an account does not count again
                if (not self._pass or captcha.signup_spent(tok_in)) and guard.captcha_needed(ip, "signup (hamesha)", dev=dev):
                    return self._send({"error": "Account banane se pehle ek chhota game khelo.", "captcha": True,
                                       "why": "signup"}, 403)
                # 2. at most SIGNUP_MAX accounts from one IP (counted in the database)
                n = accounts.signup_count(guard.ip_key(ip))
                if n >= accounts.SIGNUP_MAX and guard.violation("signup_ip", ip, "%d account / %dh" % (n, accounts.SIGNUP_HOURS), dev=dev):
                    return self._send({"error": "Is network se %d account ban chuke hain. Apne account se sign in karo, ya baad me try karo." % accounts.SIGNUP_MAX}, 429)
            tok, err = accounts.signup(user, pw, guard.ip_key(ip) if guarded else "")
            if err:
                return self._send({"error": err}, 400)
            if guarded and self._pass:
                captcha.signup_spend(tok_in)
            return self._send({"token": tok, "user": accounts.user_for(tok)})
        # sign-in
        if guarded:
            why = guard.login_why(ip, user)
            if why and not self._pass and guard.captcha_needed(ip, "signin: " + why, dev=dev):
                return self._send({"error": "Ek chhota game khelo, phir sign in hoga.", "captcha": True, "why": why}, 403)
            if guard.login_hard(ip, user):
                return self._send({"error": "Bahut koshish ho gayi. Thodi der baad try karo."}, 429)
        tok, err = accounts.login(user, pw)
        if guarded:
            guard.login_note(ip, user, not err)
        if err:
            return self._send({"error": err}, 400)
        return self._send({"token": tok, "user": accounts.user_for(tok)})

    def _wn_route(self, target, b64, attach=None):
        """WN file through our own proxy.  attach = file name -> a download (200 + attachment)."""
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
            _serve_wn_slice(self, _u64(u), attach)
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
        _serve_wn_slice(self, b64, attach)
        return

    def _route(self):
        parsed = urlparse(self.path)
        path = unquote(parsed.path)
        qs = parse_qs(parsed.query)
        mv = re.match(r"^/vk/([A-Za-z0-9_\-]{8,200})(/.*)$", path)
        if mv:                                            # Stremio addon link with the VIP key inside: /vk/<key>/manifest.json
            qs = dict(qs)
            qs["vk"] = [mv.group(1)]
            path = mv.group(2)
        self._gctx(qs)
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
                if guard.is_decoy(m.group(1)):             # Step 6: a fake anime's poster
                    self._trap(m.group(1), "poster")
                    return self._send({"error": "no image"}, 404)
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
            if path == "/tv":                                  # Step 9: the phone page a TV's QR opens
                try:
                    with open(os.path.join(BASE_DIR, "tvpass.html"), "rb") as fh:
                        body_ = fh.read()
                except Exception:
                    return self._send({"error": "not found"}, 404)
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body_)))
                self.send_header("Cache-Control", "no-cache")
                self.send_header("Referrer-Policy", "no-referrer")     # the code is in the address: do not pass it on
                self.end_headers()
                if not self._is_head:
                    self.wfile.write(body_)
                return
            if path == "/api/tv/check":                        # Step 9: GET version for the phone page
                q_ = parse_qs(urlparse(self.path).query)
                return self._tv(path, {"code": (q_.get("c") or [""])[0]})
            if path in ("/captcha-lab", "/captcha.js"):          # Step 8: the game (loaded only when needed) and its lab page
                try:
                    isjs = path == "/captcha.js"
                    with open(os.path.join(BASE_DIR, "captcha.js" if isjs else "captcha-lab.html"), "rb") as fh:
                        body_ = fh.read()
                except Exception:
                    return self._send({"error": "not found"}, 404)
                self.send_response(200)
                self.send_header("Content-Type", "text/javascript; charset=utf-8" if isjs else "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body_)))
                self.send_header("Cache-Control", "no-cache")
                self.send_header("Access-Control-Allow-Origin", "*")
                self.end_headers()
                if not self._is_head:
                    self.wfile.write(body_)
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
                if not self._vip:
                    guard.track("shows", self._ip, self._dev)
                    if self._limit("shows", 60, guard.SHOWS_IP_MIN, guard.SHOWS_DEV_MIN, "/api/shows"):
                        return
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
            if path == "/api/captcha/status":                  # Step 7: do I hold a valid pass?
                return self._captcha(path, {})
            m = re.match(r"^/api/watch/([a-z0-9_]+)(?:/(\d+)/(\d+))?$", path)
            if m:
                self._watch(m.group(1), m.group(2), m.group(3))
                return
            m = re.match(rf"^/api/hb/({_B64_RE}+)$", path)
            if m:
                if not self._vip:
                    guard.track("hb", self._ip, self._dev)
                self._send(api_hb(m.group(1), self._ip, self._vip))
                return
            m = re.match(rf"^/api/dltok/({_B64_RE}+)$", path)
            if m:
                try:
                    u_ = None if self._vip else accounts.user_for(self._token())
                except Exception:
                    u_ = None
                body_, code_ = api_dltok(m.group(1), self._ip, self._vip, (u_ or {}).get("id"))
                self._send(body_, code_)
                return
            m = re.match(r"^/api/skip/([a-z0-9_]+)(?:/(\d+)/(\d+))?$", path)
            if m:
                if self._pre("skip", m.group(1)):
                    return
                self._send(api_skip(m.group(1), int(m.group(2) or 1), int(m.group(3) or 1)))
                return
            if path == "/manifest.json":
                if self._limit("manifest", 60, guard.MANIFEST_MIN, 0, "/manifest.json"):
                    return
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
                if not self._vip:
                    mslug = m.group(2).split(":")[1]
                    if self._pre("meta", mslug):
                        return
                    if (self._limit("meta_burst", guard.META_WIN, guard.META_MAX, guard.META_MAX, "/meta")
                            or self._limit("meta_min", 60, guard.META_MIN_MAX, 0, "/meta")):
                        return
                    guard.open_mark(self._ip, self._dev, mslug)     # its video links may now be asked for
                meta = handle_meta(m.group(1), m.group(2))
                self._send({"meta": meta} if meta else {"meta": {}},
                           200 if meta else 404)
                return

            m = re.match(r"^/stream/(series|movie)/"
                         r"(raretoons2:[^/]+|tt\d+(?::\d+)*)\.json$", path)
            if m:
                if not self._vip:
                    sid_ = m.group(2).split(":")
                    if self._pre("stream", sid_[1] if sid_[0] == "raretoons2" and len(sid_) > 1 else None):
                        return
                    if self._limit("stream", 60, guard.STREAM_MIN, 0, "/stream"):     # Stremio: only a rate limit
                        return
                self._send(handle_stream(m.group(1), m.group(2)))
                return

            m = re.match(rf"^/mq/({_B64_RE}+)\.m3u8$", path)
            if m:
                zipper = self._mq_gate(m.group(1), "s")
                if zipper is None:
                    return
                _serve_m3u8_master(self, zipper)
                return

            m = re.match(rf"^/mq/({_B64_RE}+)/dl/({_B64_RE}+)(\.[A-Za-z0-9]{{1,5}})?$", path)
            if m:
                zipper = self._mq_gate(m.group(1), "d")
                if zipper is None:
                    return
                slot = self._dl_slot(m.group(1))
                if slot is None:
                    return
                try:
                    _serve_download(self, zipper, m.group(2),
                                    (qs.get("name", [""])[0] if qs else ""),
                                    check=bool(qs and qs.get("check")))
                finally:
                    if slot:
                        guard.dl_end(slot)
                return

            m = re.match(rf"^/mq/({_B64_RE}+)/u/({_B64_RE}+)"
                         rf"(\.[A-Za-z0-9]{{1,5}})?$", path)
            if m:
                zipper = self._mq_gate(m.group(1), "s")
                if zipper is None:
                    return
                _serve_m3u8_child(self, zipper, m.group(2),
                                  (m.group(3) or ".ts").lower(),
                                  rt=(qs.get("rt", [""])[0] if qs else ""))
                return

            m = re.match(rf"^/wn/({_B64_RE}+)(/dl)?$", path)
            if m:
                tok_, b64_ = m.group(1), m.group(1)
                pw = _mq_parse(tok_)
                if pw and pw["sid"]:                     # session-bound WN link (Step 4)
                    if self._mq_gate(tok_, "d" if m.group(2) else "w", any_z=True) is None:
                        return
                    target = pw["z"]
                    b64_ = _u64(target)
                    attach = ((qs.get("name", [""])[0] if qs else "") or "video") if m.group(2) else None
                    slot = self._dl_slot(tok_) if m.group(2) else ""
                    if slot is None:
                        return
                else:
                    target, attach, slot = _u64d(tok_), None, ""
                try:
                    return self._wn_route(target, b64_, attach)
                finally:
                    if slot:
                        guard.dl_end(slot)
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
    try:
        last = {k: float(v) for k, v in json.loads(accounts.kv_get("auto_last") or "{}").items()}
    except Exception:
        last = {}
    saved_at = time.time()
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
            if time.time() - saved_at > 600:            # remember the round across restarts
                saved_at = time.time()
                _kv_put("auto_last", json.dumps({k: int(v) for k, v in last.items() if k in SHOWS}))
        except Exception as e:
            print("[rt2] auto refresh:", e, flush=True)
        time.sleep(gap)


_INDEX_LOCK = threading.Lock()      # only ONE refresh_index.run at a time


def _reload_catalog():
    """Re-read episodes_index.jsonl and merge new shows/episodes into the
    live SHOWS dict (no restart).  New shows get a poster in background."""
    global ROWS
    ROWS = _clean_rows(_load_jsonl(os.path.join(BASE_DIR, "episodes_index.jsonl")))
    with STORE_LOCK:
        _build_shows()
        missing = [r for r in SHOWS.values() if not r.get("poster")]
    for rec in missing:
        _bg_once(("poster", rec["slug"]), lambda rec=rec: _fetch_poster(rec))
    try:
        _catalog_delta_save()
    except Exception as e:
        applog.log_once("cat-save", 300, "error", "app", f"catalog backup to DB failed: {e!r}")


# ---- catalog backup in the database ---------------------------------------
# episodes_index.jsonl lives on the container disk, which is wiped by every
# restart/redeploy.  Everything the site refresh discovered AFTER the shipped
# file (new shows, updated hubs) is therefore also saved in the DB (compressed,
# in chunks) and merged back at boot - so a restart never has to crawl it again.
_CAT_CHUNK = 150000
_cat_saved = {"h": ""}


def _catalog_delta_save():
    changed_hubs = {}
    for r in ROWS:
        k = _hub_key(r)
        changed_hubs.setdefault(k, []).append(r)
    cur = _hub_hashes(ROWS)
    delta = [r for k, rows in changed_hubs.items() if cur.get(k) != BASE_HUBS.get(k) for r in rows]
    blob = base64.b64encode(zlib.compress(json.dumps(delta, ensure_ascii=False,
                                                     separators=(",", ":")).encode("utf-8"), 9)).decode("ascii")
    h = hashlib.md5((BASE_SIG + blob).encode("ascii")).hexdigest()
    if h == _cat_saved["h"]:
        return                                   # nothing new since the last save
    parts = [blob[i:i + _CAT_CHUNK] for i in range(0, len(blob), _CAT_CHUNK)] or [""]
    for i, part in enumerate(parts):
        accounts.kv_set("cat_delta_%d" % i, part)
    accounts.kv_set("cat_delta_meta", json.dumps({"n": len(parts), "base": BASE_SIG, "h": h,
                                                  "rows": len(delta), "t": time.time()}))
    _cat_saved["h"] = h
    print(f"[rt2] catalog backup saved to DB: {len(delta)} rows in {len(parts)} part(s)", flush=True)


def _catalog_delta_apply():
    """Boot: merge the saved delta into ROWS (and the file on disk, so the
    refresher sees those hubs as already known)."""
    global ROWS
    try:
        meta = json.loads(accounts.kv_get("cat_delta_meta") or "null")
        if not meta:
            return 0
        blob = "".join(accounts.kv_get("cat_delta_%d" % i) or "" for i in range(int(meta["n"])))
        if hashlib.md5((meta["base"] + blob).encode("ascii")).hexdigest() != meta["h"]:
            print("[rt2] catalog backup in DB is damaged - ignored", flush=True)
            return 0
        delta = json.loads(zlib.decompress(base64.b64decode(blob)).decode("utf-8"))
    except Exception as e:
        print("[rt2] catalog backup restore failed:", repr(e), flush=True)
        return 0
    if not delta:
        _cat_saved["h"] = meta.get("h", "")
        return 0
    same_base = meta.get("base") == BASE_SIG
    dh = {_hub_key(r) for r in delta}
    if same_base:
        keep = [r for r in ROWS if _hub_key(r) not in dh]      # the DB copy is newer
        merged = keep + delta
    else:                                                       # new deploy: shipped data wins,
        merged = ROWS + [r for r in delta if _hub_key(r) not in BASE_HUBS]   # only add unknown hubs
    ROWS = _clean_rows(merged)
    try:
        path = os.path.join(BASE_DIR, "episodes_index.jsonl")
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            for r in ROWS:
                fh.write(json.dumps(r, ensure_ascii=False) + "\n")
        os.replace(tmp, path)
    except OSError as e:
        print("[rt2] could not rewrite episodes_index.jsonl:", e, flush=True)
    with STORE_LOCK:
        _build_shows()
    _cat_saved["h"] = meta.get("h", "") if same_base else ""
    print(f"[rt2] catalog restored from DB: {len(delta)} rows ({'same' if same_base else 'new'} deploy)", flush=True)
    return len(delta)


def _fresh_tick(feed_pages):
    """Look at the site's newest posts (RSS).  Known shows are re-read at
    once (new episodes show up now, not hours later); unknown hubs trigger
    an index refresh so brand-new shows appear."""
    import refresh_index as RI
    links = []
    for page in range(1, feed_pages + 1):
        r = upstream_get(f"{SITE}feed/?paged={page}", timeout=25)
        if r.status_code != 200 or _cf_blocked(r.text):
            applog.log_once("feed-blocked", 600, "error", "fresh",
                            f"RSS feed page {page}: HTTP {r.status_code}"
                            f"{' - Cloudflare challenge' if _cf_blocked(r.text) else ''}")
            continue
        for it in re.findall(r"<item>(.*?)</item>", r.text or "", re.S):
            m = re.search(r"<link>(.*?)</link>", it, re.S)
            if m:
                links.append(m.group(1).strip())
    if not links:
        applog.log_once("feed-empty", 600, "warn", "fresh", "RSS feed returned no posts")
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
            except Exception as e:
                applog.log_once("fresh-absorb", 300, "error", "fresh",
                                f"re-read failed for {rec.get('slug')}: {e!r}")
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
    gap = float(os.environ.get("FRESH_SECONDS", "3600"))
    pages = int(os.environ.get("FRESH_FEED_PAGES", "2"))
    if gap <= 0:
        return
    # restart-safe: if the last check was less than `gap` ago, wait out the rest
    time.sleep(max(45.0, gap - (time.time() - _kv_float("t_fresh"))))
    while True:
        t0 = time.time()
        try:
            _fresh_tick(pages)
            _kv_put("t_fresh", time.time())
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
    gap = float(os.environ.get("CATALOG_REFRESH_SECONDS", "3600"))
    full_gap = float(os.environ.get("CATALOG_FULL_REFRESH_SECONDS", str(24 * 3600)))
    if gap <= 0:
        return
    # restart-safe: the last run (and the last FULL walk) are remembered in the DB
    time.sleep(max(120.0, gap - (time.time() - _kv_float("t_catalog"))))
    last_full = _kv_float("t_catalog_full")
    while True:
        try:
            import refresh_index
            do_full = full_gap > 0 and time.time() - last_full >= full_gap
            if do_full:
                last_full = time.time()
            before = len(SHOWS)
            with _INDEX_LOCK:
                summary = refresh_index.run(quiet=True, full=do_full)
                _reload_catalog()
            added = len(SHOWS) - before
            _kv_put("t_catalog", time.time())
            if do_full:
                _kv_put("t_catalog_full", last_full)
            if added or summary:
                print(f"[rt2] catalog refresh ({'full' if do_full else 'recent'}): "
                      f"+{added} new shows", flush=True)
        except Exception as e:
            print("[rt2] catalog refresh failed:", e, flush=True)
        time.sleep(gap)


# ---- admin: force a catalog update from the site, right now ---------------
_force_state = {"running": False, "mode": "", "started": 0.0, "finished": 0.0,
                "before": 0, "after": 0, "summary": None, "error": ""}


def _force_state_view():
    v = dict(_force_state)
    v["shows_now"] = len(SHOWS)
    v["busy"] = _INDEX_LOCK.locked()          # auto refresh may hold it too
    v["now"] = time.time()
    return v


def _force_catalog_worker(full):
    try:
        _force_state["before"] = len(SHOWS)
        summary = refresh_index_run(full)
        _reload_catalog()
        _force_state["after"] = len(SHOWS)
        _force_state["summary"] = summary
        now = time.time()
        _kv_put("t_catalog", now)
        if full:
            _kv_put("t_catalog_full", now)
        applog.info("admin", f"forced catalog update ({'full' if full else 'recent'}) done: "
                             f"{_force_state['before']} -> {_force_state['after']} shows, {summary}")
    except Exception as e:
        _force_state["error"] = repr(e)
        applog.log_once("force-cat", 5, "error", "admin", f"forced catalog update failed: {e!r}")
    finally:
        _force_state["running"] = False
        _force_state["finished"] = time.time()
        _INDEX_LOCK.release()


def refresh_index_run(full):
    import refresh_index
    return refresh_index.run(quiet=True, full=full)


def _force_catalog_start(full=True):
    """Starts the site->catalog refresh in a background thread (full=True
    walks the whole archive + sitemap). Returns (ok, message)."""
    if not _INDEX_LOCK.acquire(blocking=False):
        return False, "A catalog update is already running - wait for it to finish."
    _force_state.update(running=True, mode="full" if full else "recent", started=time.time(),
                        finished=0.0, summary=None, error="", before=len(SHOWS), after=0)
    try:
        threading.Thread(target=_force_catalog_worker, args=(bool(full),), daemon=True,
                         name="force-catalog").start()
    except Exception as e:
        _force_state.update(running=False, error=repr(e))
        _INDEX_LOCK.release()
        return False, "could not start: %r" % e
    applog.info("admin", f"forced catalog update started ({'full' if full else 'recent'})")
    return True, "started"


def _sync_once():
    """Look at AniList + our own data; rebuild the lists.  Only when something
    really changed is it saved and the website payload rebuilt."""
    changed = _al_refresh()
    for w in ("week", "day", "movies"):
        try:
            changed = _trend_rebuild(w) or changed
        except Exception as e:
            applog.log_once("sync-" + w, 300, "error", "trend", f"hourly rebuild {w} failed: {e!r}")
    before = (_shows_cache["raw"] or b"")
    try:
        _updates_refresh()
        raw = json.dumps(_api_shows_build(), ensure_ascii=False).encode("utf-8")
        if raw != before:
            _shows_cache.update(raw=raw, gz=gzip.compress(raw, 6), t=time.time())
            changed = True
    except Exception as e:
        applog.log_once("sync-build", 300, "error", "app", f"hourly payload build failed: {e!r}")
    print(f"[sync] hourly check done - {'lists updated' if changed else 'no change, nothing touched'}", flush=True)
    return changed


def _hourly_sync():
    """Every SYNC_SECONDS (1 h): refresh the lists; resumes the clock after a
    restart (no fetch at all when the last sync was less than an hour ago)."""
    if SYNC_SECONDS <= 0:
        return
    time.sleep(max(60.0, SYNC_SECONDS - (time.time() - _kv_float("sync_t"))))
    while True:
        t0 = time.time()
        try:
            _sync_once()
            _kv_put("sync_t", time.time())
        except Exception as e:
            print("[sync] failed:", repr(e), flush=True)
        time.sleep(max(60.0, SYNC_SECONDS - (time.time() - t0)))


def _boot_from_db():
    """Everything the last run saved: catalog, AniList, trending lists."""
    try:
        _catalog_delta_apply()
    except Exception as e:
        print("[rt2] catalog restore failed:", repr(e), flush=True)
    _al_load_db()
    _trend_load_db()
    _shows_cache["t"] = 0            # rebuild the website list with the restored data


def _restore_from_db():
    """The SQL service may be asleep.  The site starts at once on the shipped
    data; this keeps knocking until the DB answers, then reads the last saved
    state back.  Updates happen after that, in their own time."""
    delay = 5
    while True:
        try:
            accounts.kv_get("al_meta")               # probe: raises while the DB is unreachable
            break
        except Exception as e:
            print(f"[rt2] DB not reachable yet (asleep?) - running on saved files, retry in {delay}s: {e!r}", flush=True)
            time.sleep(delay)
            delay = min(delay * 2, 120)
    _boot_from_db()
    _DB_READY.set()
    print("[rt2] state restored from DB", flush=True)


def _startup():
    """Restore everything saved in the DB FIRST, then start the workers - so
    nothing is fetched again that the last run already has."""
    threading.Thread(target=_restore_from_db, daemon=True).start()
    threading.Thread(target=_tmdb_boot, daemon=True).start()
    _DB_READY.wait(300)              # cold DB: give it up to 5 min, then go on with the saved files
    threading.Thread(target=_hourly_sync, daemon=True).start()
    threading.Thread(target=_auto_refresh, daemon=True).start()
    threading.Thread(target=_catalog_refresh, daemon=True).start()
    threading.Thread(target=_fresh_watch, daemon=True).start()
    threading.Thread(target=_tmdb_backfill, daemon=True).start()
    threading.Thread(target=shows_payload, daemon=True).start()   # warm /api/shows
    threading.Thread(target=_img_prewarm, daemon=True).start()    # posters -> disk
    _updates(); _popular(); _trending("week"); _trending("day"); _trending("movies")   # warm the caches at boot

    def _posters():
        with STORE_LOCK:
            missing = [r for r in SHOWS.values() if not r.get("poster")]
        for rec in missing:
            _fetch_poster(rec)
            time.sleep(1)
    threading.Thread(target=_posters, daemon=True).start()


def main():
    guard.start()                                                 # VIP keys + saved PROTECT mode (background)
    threading.Thread(target=_startup, daemon=True).start()        # port opens at once
    port = int(sys.argv[1]) if len(sys.argv) > 1 else PORT
    srv = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    print(f"[rt2] {ADDON_NAME} v{VERSION} | series={len(SERIES)} "
          f"movies={len(MOVIES)} rows={len(ROWS)} posters={len(POSTERS)}")
    print(f"[rt2] listening on 0.0.0.0:{port}")
    srv.serve_forever()


if __name__ == "__main__":
    main()
