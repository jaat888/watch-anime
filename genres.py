#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Genre system + Jikan (MyAnimeList) client.

Why this file exists
--------------------
TMDB and Jikan name genres differently ("Action & Adventure" vs "Action",
"Sci-Fi & Fantasy" vs "Sci-Fi" ...).  Everything is funnelled through ONE
canonical list defined here, so the website's genre filter shows a clean,
consistent set no matter which API the data came from.

To change genres, edit ONLY this file:
  * ALIASES  - source name  -> canonical name(s)   ([] = drop it)
  * THEMES   - Jikan "themes" worth showing as genres (School, Isekai ...)
"""
import difflib
import re
import threading
import time

import requests

JIKAN_URL = "https://api.jikan.moe/v4"
JIKAN_GAP = 1.1          # seconds between calls (Jikan limit: 3/s, 60/min)
MAX_GENRES = 8

# source genre (lower-case) -> list of canonical genres.  [] means "drop".
ALIASES = {
    # --- TMDB combined / odd names -------------------------------------
    "action & adventure": ["Action", "Adventure"],
    "sci-fi & fantasy": ["Fantasy"],        # TMDB lumps isekai/fantasy in here; real Sci-Fi comes from MAL/keywords
    "war & politics": ["War"],
    "science fiction": ["Sci-Fi"],
    "animation": [],                 # everything here is animation
    "tv movie": [],
    "soap": ["Drama"],
    "talk": [],
    "news": [],
    "reality": [],
    "documentary": [],
    # --- Jikan / MAL ----------------------------------------------------
    "suspense": ["Thriller"],
    "gourmet": ["Food"],
    "avant garde": [],
    "award winning": [],
    "erotica": [],
    "hentai": [],
    "ecchi": [],
    "boys love": [],
    "girls love": [],
    "sci-fi": ["Sci-Fi"],
    "slice of life": ["Slice of Life"],
    "supernatural": ["Supernatural"],
}

# Jikan "themes" that are useful as browsable genres.
THEMES = {
    "school": "School", "isekai": "Isekai", "mecha": "Mecha",
    "martial arts": "Martial Arts", "music": "Music",
    "psychological": "Psychological", "military": "Military",
    "historical": "Historical", "super power": "Super Power",
    "samurai": "Samurai", "vampire": "Vampire", "space": "Space",
    "time travel": "Time Travel", "magical sex shift": None,
    "detective": "Detective", "survival": "Survival",
    "reincarnation": "Reincarnation", "idols (female)": "Idols",
    "idols (male)": "Idols", "anthropomorphic": "Anthropomorphic",
    "mythology": "Mythology", "gag humor": None, "harem": None,
    "mahou shoujo": "Magical Girl", "team sports": "Sports", "combat sports": "Sports",
    "racing": "Sports", "strategy game": "Strategy", "video game": "Game",
    "high stakes game": "Game", "medical": "Medical", "workplace": "Workplace",
    "delinquents": "Delinquents", "parody": "Parody", "pets": "Pets",
    "iyashikei": "Healing", "organized crime": "Crime", "showbiz": "Showbiz",
    "performing arts": "Performing Arts", "otaku culture": "Otaku", "childcare": "Family",
    "love polygon": "Romance", "romantic subtext": "Romance", "adult cast": None,
    "cgdct": None, "crossdressing": None, "gore": None, "reverse harem": None,
    "visual arts": "Art", "educational": "Educational",
}

# Jikan demographics (Shounen, Seinen ...) are good browse tags too.
DEMOS = {"shounen": "Shounen", "seinen": "Seinen", "shoujo": "Shoujo", "josei": "Josei"}

# keyword -> genre, used on the synopsis to reach 6-8 accurate genres.
KEYWORDS = [
    (r"reincarnat", "Reincarnation"),
    (r"reincarnat|another world|new world|isekai|summoned to|transported to", "Isekai"),
    (r"\bmagic|wizard|sorcer|\bspells?\b|witch|mage\b", "Magic"),
    (r"\bschool|academy|\bstudents?\b|classmate", "School"),
    (r"romanc|romantic|falls? in love|fell in love|love interest|crush on", "Romance"),
    (r"comed|hilarious|\bgags?\b|laugh|humou?r", "Comedy"),
    (r"mystery|mysterious|detective|murder|investigat", "Mystery"),
    (r"demon|ghost|spirit|\bcurse|supernatural|undead|monster|yokai", "Supernatural"),
    (r"survival|survive", "Survival"),
    (r"\barmy\b|soldier|military|\bwar\b|battlefield", "Military"),
    (r"super ?powers?|special abilit|superhuman|superhero", "Super Power"),
    (r"\bspace\b|galaxy|spaceship|alien|planet", "Space"),
    (r"mecha|giant robot", "Mecha"),
    (r"post-apocalyp|apocalypse|zombie", "Post-Apocalyptic"),
    (r"adventure|journey|quest|explor", "Adventure"),
    (r"fight|battle|combat|martial|swordsm|duel|warrior", "Action"),
    (r"kingdom|\bking\b|\bprince|princess|knight|dragon|\belf\b|\belves\b|dungeon", "Fantasy"),
    (r"family|friendship|\bfriends\b", "Drama"),
    (r"cyber|android|\brobots?\b|artificial intelligence|futuristic|\bfuture\b", "Sci-Fi"),
]
_SCIFI_OK = re.compile(r"cyber|android|\brobots?\b|artificial intelligence|futur|\bspace|galaxy|alien|"
                       r"planet|time travel|mecha|scientist|technolog|laborator|dystop|apocalyp", re.I)


def finalize(genres, desc="", source=""):
    """Clean + top up a stored genre list: drop a TMDB-only 'Sci-Fi' that the
    synopsis does not support, then add keyword genres until there are
    MAX_GENRES (never invents anything the text does not mention)."""
    out = list(genres or [])
    text = desc or ""
    if source != "mal" and "Sci-Fi" in out and not _SCIFI_OK.search(text):
        out.remove("Sci-Fi")
    if len(out) < MAX_GENRES and text:
        low = text.lower()
        for pat, gname in KEYWORDS:
            if len(out) >= MAX_GENRES:
                break
            if gname not in out and re.search(pat, low):
                out.append(gname)
    return out[:MAX_GENRES]


def normalize(*name_lists, cap=MAX_GENRES):
    """Merge any number of raw genre-name lists into the canonical list
    (ordered, de-duplicated, capped)."""
    out = []
    for names in name_lists:
        for n in names or []:
            key = (n or "").strip().lower()
            if not key:
                continue
            if key in ALIASES:
                mapped = ALIASES[key]
            else:
                mapped = [n.strip()]
            for g in mapped:
                if g and g not in out:
                    out.append(g)
    return out[:cap]


# ------------------------------------------------------------------ Jikan --
_lock = threading.Lock()
_last = [0.0]


def _jikan_get(path, **params):
    """Rate-limited GET.  Raises on network/API failure."""
    for attempt in (1, 2):
        with _lock:
            wait = JIKAN_GAP - (time.time() - _last[0])
            if wait > 0:
                time.sleep(wait)
            _last[0] = time.time()
        r = requests.get(JIKAN_URL + path, params=params, timeout=12,
                         headers={"User-Agent": "watch-anime/1.0"})
        if r.status_code == 429 and attempt == 1:
            time.sleep(2.5)
            continue
        r.raise_for_status()
        return r.json()


def _norm(s):
    s = re.sub(r"[^a-z0-9 ]+", " ", (s or "").lower())
    return re.sub(r"\s+", " ", s).strip()


def _titles(item):
    ts = [item.get("title"), item.get("title_english"),
          item.get("title_japanese")]
    ts += [t.get("title") for t in item.get("titles") or []]
    return [_norm(t) for t in ts if t]


def _score_match(query, item):
    q = _norm(query)
    return max((difflib.SequenceMatcher(None, q, t).ratio()
                for t in _titles(item)), default=0.0)


def jikan_lookup(query, is_movie=False, min_match=0.6):
    """Search MyAnimeList through Jikan.

    Returns None when nothing matches well enough, else
      {"score": float|None, "votes": int, "genres": [raw names],
       "synopsis": str, "mal_id": int}
    RAISES on network/API failure (caller decides what to cache)."""
    params = {"q": query, "limit": 8, "sfw": "true"}
    if is_movie:
        params["type"] = "movie"
    items = _jikan_get("/anime", **params).get("data") or []
    if not is_movie:                       # series: skip movies/music/etc.
        tv = [i for i in items if (i.get("type") or "").lower()
              in ("tv", "ova", "ona", "special", "")]
        items = tv or items
    best, best_s = None, 0.0
    for it in items:
        s = _score_match(query, it)
        # tiny bonus for well-scored entries so a popular match wins ties
        s += min((it.get("scored_by") or 0) / 5_000_000, 0.02)
        if s > best_s:
            best, best_s = it, s
    if not best or best_s < min_match:
        return None
    raw = [g.get("name") for g in best.get("genres") or []]
    for t in best.get("themes") or []:
        mapped = THEMES.get((t.get("name") or "").lower())
        if mapped:
            raw.append(mapped)
    for d in best.get("demographics") or []:
        mapped = DEMOS.get((d.get("name") or "").lower())
        if mapped:
            raw.append(mapped)
    syn = re.sub(r"\s*\[Written by MAL Rewrite\]\s*", "",
                 best.get("synopsis") or "").strip()
    return {"score": best.get("score"),
            "votes": int(best.get("scored_by") or 0),
            "genres": raw, "synopsis": syn, "mal_id": best.get("mal_id")}
