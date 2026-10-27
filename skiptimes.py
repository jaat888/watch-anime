# -*- coding: utf-8 -*-
"""
Skip-intro / skip-recap / skip-ending timestamps for the website player.

Nothing here is on the playback path: the player asks /api/skip/... in
parallel with /api/watch/... and simply shows no button when this returns
nothing, so a slow or dead provider can never delay or break a stream.

PROVIDERS (tried in this order, the next one only when intro or ending is
still missing):

    1. AniSkip     api.aniskip.com      free, no key, needs the MyAnimeList id
                                        (found through AniList, free, no key)
    2. IntroDB     api.introdb.app      free, no key, needs the IMDb id
                                        (found through TMDB external_ids)
    3. Anime-Skip  api.anime-skip.com   free, but needs a client id: set the
                                        ANIMESKIP_CLIENT_ID env var, otherwise
                                        this step is skipped.  Written from the
                                        public GraphQL schema and NOT tested
                                        against the live API - it can only ever
                                        add segments, a failure is ignored.

lookup() returns CANDIDATES, not one answer:

    {"segments": [{"type": "intro"|"recap"|"outro", "start": s, "end": s,
                   "len": episode length the timestamps were made for (0 =
                   unknown), "src": "aniskip", "rank": 0}, ...]}

The player picks the candidate whose "len" matches the video it is actually
playing (the site's dub can be cut differently from the database's copy) and
ignores the rest - a skip in the wrong place is worse than no button.
"""
import difflib
import os
import re
import threading
import time

import requests

ANISKIP_URL = "https://api.aniskip.com/v2/skip-times"
INTRODB_URL = "https://api.introdb.app/segments"
ANILIST_URL = "https://graphql.anilist.co"
ANIMESKIP_URL = "https://api.anime-skip.com/graphql"
UA = {"User-Agent": "watch-anime/1.0"}
HTTP_TIMEOUT = 6
TOTAL_BUDGET = 25                    # seconds for one lookup, all providers

TTL_HIT = 24 * 3600                  # something found
TTL_MISS = 30 * 60                   # every provider answered "nothing"
TTL_FAIL = 2 * 60                    # a provider was unreachable: retry soon
ID_TTL = 7 * 86400

# sane lengths (seconds) - anything outside is a bad submission, drop it
LIMITS = {"intro": (5, 300), "recap": (5, 480), "outro": (5, 1200)}

_lock = threading.Lock()
_cache = {}                          # (name, season, episode, movie) -> (expires, payload)
_mal_cache = {}                      # (name, season, movie) -> (expires, [(id, episodes)] )
_imdb_cache = {}                     # (name, movie) -> (expires, imdb_id|None)
_inflight = {}                       # key -> Event (identical concurrent lookups share one run)


class _Unreachable(Exception):
    """A provider could not be asked (network / 5xx / 429): do not cache a miss for long."""


def _get(url, **kw):
    kw.setdefault("timeout", HTTP_TIMEOUT)
    kw.setdefault("headers", UA)
    try:
        return requests.get(url, **kw)
    except requests.RequestException as e:
        raise _Unreachable(type(e).__name__)


def _norm(s):
    return re.sub(r"[^a-z0-9]+", " ", (s or "").lower()).strip()


def _seg(kind, start, end, length, src, rank):
    try:
        start, end, length = float(start), float(end), float(length or 0)
    except (TypeError, ValueError):
        return None
    lo, hi = LIMITS[kind]
    if start < 0 or end <= start or not (lo <= end - start <= hi):
        return None
    return {"type": kind, "start": round(start, 2), "end": round(end, 2),
            "len": round(length, 1) if length > 0 else 0, "src": src, "rank": rank}


# ------------------------------------------------------------ id mapping ---
_SEASON_WORDS = re.compile(
    r"\bseason\s*(\d+)\b|\b(\d+)(?:st|nd|rd|th)\s+season\b|\bpart\s*(\d+)\b", re.I)
_ROMAN = {"ii": 2, "iii": 3, "iv": 4, "v": 5}


def _season_hint(title):
    m = _SEASON_WORDS.search(title or "")
    if m:
        return int(next(g for g in m.groups() if g))
    m = re.search(r"\s(ii|iii|iv|v)$", (title or "").strip(), re.I)
    return _ROMAN.get(m.group(1).lower(), 0) if m else 0


def _strip_season(title):
    return _norm(re.sub(r"\bseason\s*\d+\b|\b\d+(?:st|nd|rd|th)\s+season\b|\bpart\s*\d+\b", " ",
                        title or "", flags=re.I))


_AL_Q = ("query($q:String){Page(perPage:10){media(search:$q,type:ANIME,sort:SEARCH_MATCH){"
         "idMal format episodes title{romaji english} synonyms}}}")


def _anilist_mal(name, season, movie):
    """-> (mal_id, episode_count|None) of the AniList/MAL entry that is this season, or None."""
    key = (name, season, movie)
    now = time.time()
    with _lock:
        hit = _mal_cache.get(key)
        if hit and hit[0] > now:
            return hit[1]
    queries = [name] if season <= 1 or movie else [f"{name} Season {season}", name]
    want = _norm(name)
    best, best_score = None, 0.0
    for q in queries:
        try:
            r = requests.post(ANILIST_URL, json={"query": _AL_Q, "variables": {"q": q}},
                              timeout=HTTP_TIMEOUT, headers={**UA, "Accept": "application/json"})
        except requests.RequestException as e:
            raise _Unreachable(type(e).__name__)
        if r.status_code >= 500 or r.status_code == 429:
            raise _Unreachable("anilist %d" % r.status_code)
        if r.status_code != 200:
            continue
        media = (((r.json() or {}).get("data") or {}).get("Page") or {}).get("media") or []
        for m in media:
            if not m.get("idMal"):
                continue
            names = [(m.get("title") or {}).get("english"), (m.get("title") or {}).get("romaji")] \
                + list(m.get("synonyms") or [])
            score = max((difflib.SequenceMatcher(None, want, _strip_season(n)).ratio()
                         for n in names if n), default=0.0)
            hint = max((_season_hint(n) for n in names if n), default=0)
            fmt = m.get("format") or ""
            if movie:
                score += 0.15 if fmt == "MOVIE" else -0.3
            else:
                if season > 1:
                    score += 0.15 if hint == season else (-0.25 if hint and hint != season else -0.05)
                elif hint > 1:
                    score -= 0.25
                if fmt in ("MOVIE", "MUSIC"):
                    score -= 0.3
            if score > best_score:
                best, best_score = m, score
        if best and best_score >= 0.6:
            break
    out = (best["idMal"], best.get("episodes")) if best and best_score >= 0.6 else None
    with _lock:
        _mal_cache[key] = (now + ID_TTL, out)
    return out


def _tmdb_imdb(name, movie, tmdb_get):
    """-> IMDb id (tt...) for the title, or None.  tmdb_get(path, **params) is addon._tmdb_get."""
    key = (name, movie)
    now = time.time()
    with _lock:
        hit = _imdb_cache.get(key)
        if hit and hit[0] > now:
            return hit[1]
    kind = "movie" if movie else "tv"
    try:
        results = tmdb_get(f"/search/{kind}", query=name).get("results") or []
    except requests.RequestException as e:
        raise _Unreachable(type(e).__name__)
    want, best, best_score = _norm(name), None, 0.0
    for r in results[:10]:
        titles = [r.get("name"), r.get("original_name"), r.get("title"), r.get("original_title")]
        score = max((difflib.SequenceMatcher(None, want, _norm(t)).ratio() for t in titles if t), default=0.0)
        if 16 in (r.get("genre_ids") or []):
            score += 0.1                                   # Animation
        if score > best_score:
            best, best_score = r, score
    imdb = None
    if best and best_score >= 0.6:
        try:
            imdb = tmdb_get(f"/{kind}/{best['id']}/external_ids").get("imdb_id") or None
        except requests.RequestException as e:
            raise _Unreachable(type(e).__name__)
    with _lock:
        _imdb_cache[key] = (now + ID_TTL, imdb)
    return imdb


# -------------------------------------------------------------- providers ---
def _aniskip(name, season, episode, movie):
    ids = _anilist_mal(name, season, movie)
    if not ids:
        return []
    mal, total = ids
    ep = 1 if movie else episode
    if total and ep > total:          # wrong season mapping (absolute numbering): never guess
        return []
    r = _get(f"{ANISKIP_URL}/{mal}/{ep}",
             params=[("types", t) for t in ("op", "ed", "mixed-op", "mixed-ed", "recap")]
             + [("episodeLength", 0)])
    if r.status_code == 404:
        return []
    if r.status_code >= 500 or r.status_code == 429:
        raise _Unreachable("aniskip %d" % r.status_code)
    if r.status_code != 200:
        return []
    kinds = {"op": "intro", "mixed-op": "intro", "ed": "outro", "mixed-ed": "outro", "recap": "recap"}
    out = []
    for it in (r.json() or {}).get("results") or []:
        kind = kinds.get(it.get("skipType"))
        iv = it.get("interval") or {}
        if kind:
            s = _seg(kind, iv.get("startTime"), iv.get("endTime"), it.get("episodeLength"), "aniskip", 0)
            if s:
                out.append(s)
    return out


def _introdb(name, season, episode, movie, tmdb_get):
    imdb = _tmdb_imdb(name, movie, tmdb_get)
    if not imdb:
        return []
    params = {"imdb_id": imdb}
    if movie:
        params["is_movie"] = "true"
    else:
        params.update(season=season, episode=episode)
    r = _get(INTRODB_URL, params=params)
    if r.status_code == 404:
        return []
    if r.status_code >= 500 or r.status_code == 429:
        raise _Unreachable("introdb %d" % r.status_code)
    if r.status_code != 200:
        return []
    j = r.json() or {}
    out = []
    for kind, field in (("intro", "intro"), ("recap", "recap"), ("outro", "outro")):
        v = j.get(field)
        if isinstance(v, dict):
            s = _seg(kind, v.get("start_sec"), v.get("end_sec"), 0, "introdb", 1)
            if s:
                out.append(s)
    return out


_AS_SEARCH = "query($q:String!){searchShows(search:$q,limit:5){id name}}"
_AS_EPS = ("query($id:ID!){findEpisodesByShowId(showId:$id){number season absoluteNumber "
           "timestamps{at type{name}}}}")


def _animeskip(name, season, episode, movie):
    cid = os.environ.get("ANIMESKIP_CLIENT_ID", "").strip()
    if not cid or movie:
        return []
    hdr = {**UA, "X-Client-ID": cid, "Content-Type": "application/json"}

    def gql(q, v):
        try:
            r = requests.post(ANIMESKIP_URL, json={"query": q, "variables": v},
                              timeout=HTTP_TIMEOUT, headers=hdr)
        except requests.RequestException as e:
            raise _Unreachable(type(e).__name__)
        if r.status_code != 200:
            raise _Unreachable("animeskip %d" % r.status_code)
        j = r.json() or {}
        if j.get("errors"):
            raise _Unreachable("animeskip graphql error")
        return j.get("data") or {}

    shows = gql(_AS_SEARCH, {"q": name}).get("searchShows") or []
    want = _norm(name)
    shows = [s for s in shows if difflib.SequenceMatcher(None, want, _norm(s.get("name"))).ratio() >= 0.8]
    if not shows:
        return []
    shows.sort(key=lambda s: -difflib.SequenceMatcher(None, want, _norm(s.get("name"))).ratio())
    eps = gql(_AS_EPS, {"id": shows[0]["id"]}).get("findEpisodesByShowId") or []

    def num(v):
        try:
            return int(float(v))
        except (TypeError, ValueError):
            return None
    cand = [e for e in eps if num(e.get("number")) == episode and (num(e.get("season")) in (None, 0, season))]
    if not cand:
        return []
    stamps = sorted((t for t in cand[0].get("timestamps") or [] if t.get("at") is not None),
                    key=lambda t: t["at"])
    out = []
    for i, t in enumerate(stamps):
        tn = ((t.get("type") or {}).get("name") or "").lower()
        kind = "intro" if "intro" in tn else "recap" if "recap" in tn else "outro" if "credit" in tn else None
        if not kind:
            continue
        end = stamps[i + 1]["at"] if i + 1 < len(stamps) else t["at"] + LIMITS[kind][1]
        s = _seg(kind, t["at"], end, 0, "animeskip", 2)
        if s:
            out.append(s)
    return out


# ------------------------------------------------------------------ main ---
def lookup(name, season, episode, movie, tmdb_get, log=None):
    """Candidates for one episode/movie.  Never raises.  Cached; identical concurrent calls share one run."""
    season, episode = int(season or 1), int(episode or 1)
    key = (name, 0 if movie else season, 0 if movie else episode, bool(movie))
    now = time.time()
    with _lock:
        hit = _cache.get(key)
        if hit and hit[0] > now:
            return hit[1]
        ev = _inflight.get(key)
        mine = ev is None
        if mine:
            ev = _inflight[key] = threading.Event()
    if not mine:                                   # someone else is already asking: wait for them
        ev.wait(TOTAL_BUDGET + 5)
        with _lock:
            hit = _cache.get(key)
        return hit[1] if hit else {"segments": []}
    try:
        deadline = now + TOTAL_BUDGET
        segs, failed, tried = [], False, 0
        steps = (("aniskip", lambda: _aniskip(name, season, episode, movie)),
                 ("introdb", lambda: _introdb(name, season, episode, movie, tmdb_get)),
                 ("animeskip", lambda: _animeskip(name, season, episode, movie)))
        for pname, fn in steps:
            have = {s["type"] for s in segs}
            if "intro" in have and "outro" in have:
                break                              # nothing left to look for
            if time.time() > deadline:
                failed = True
                break
            tried += 1
            try:
                segs += fn()
            except _Unreachable as e:
                failed = True
                if log:
                    log(pname, str(e))
            except Exception as e:                 # a provider changed its format: never break the page
                failed = True
                if log:
                    log(pname, "%s: %s" % (type(e).__name__, str(e)[:120]))
        segs.sort(key=lambda s: (s["rank"], s["type"], s["start"]))
        payload = {"segments": segs}
        ttl = TTL_HIT if segs else (TTL_FAIL if failed else TTL_MISS)
        with _lock:
            _cache[key] = (time.time() + ttl, payload)
            if len(_cache) > 4000:                 # keep memory bounded on a free host
                for k in sorted(_cache, key=lambda k: _cache[k][0])[:1000]:
                    _cache.pop(k, None)
        return payload
    finally:
        with _lock:
            _inflight.pop(key, None)
        ev.set()
