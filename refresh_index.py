#!/usr/bin/env python3
"""Incremental RareToons index refresh — add new shows + recent updates.

The addon serves from the pre-crawled index (episodes_index.jsonl +
streams.json), so shows uploaded to rareanimes.mov AFTER the last crawl are
invisible in Stremio (no meta match -> empty episode list). This script:

  1. collects the newest hub pages: the WordPress RSS feed (/feed/?paged=N)
     plus every /hindi/ link on /home/ and the current month archives,
  2. keeps those not already in streams.json (new shows) plus everything
     from the feed window (refresh: new episodes on updated pages),
  3. (re)crawls them with crawler.parse_hub_page + parse_hubs.parse_html
     and their store.animetoonhindi.com watch pages,
  4. merges everything into streams.json + episodes_index.jsonl.

Run from the repo root:   python3 refresh_index.py [feed_pages]

Usage notes:
  * needs `pip install requests beautifulsoup4 lxml`
  * idempotent: re-running replaces the same hubs' rows, keeps the rest
  * commit + push afterwards; the Render service redeploys with the new data
"""
import json
import re
import sys
import time
from pathlib import Path
from urllib.parse import unquote, urlparse

ROOT = Path(__file__).parent
sys.path.insert(0, str(ROOT))
import crawler as C          # noqa: E402
import parse_hubs as P       # noqa: E402

def _get(url, timeout=30):
    """GET through the crawler's browser-impersonating session (Cloudflare)."""
    return C.get_session().get(url, headers=UA, timeout=timeout)


def _cf(r):
    t = (r.text or "")[:3000].lower()
    return "just a moment" in t or "cf-chl" in t


SITE = "https://www.rareanimes.mov"
UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"}


def strong(u):
    p = urlparse(u.split("#")[0])
    path = re.sub(r"/comment-page-\d+$", "", unquote(p.path).lower().rstrip("/"))
    return path


# site's own index / utility pages: they LIST shows, they are not shows
_NOT_HUBS = {"all-anime-cartoon-movies-list", "all-anime-cartoon-series-list",
             "hindi-cartoon-series", "hindi-me-toons", "cartoontechkidctk",
             "desitvforum", "cookie-policy", "contact-us", "dmca", "disclaimer"}
_LIST_PAGES = ("/all-anime-cartoon-series-list/", "/all-anime-cartoon-movies-list/",
               "/hindi-cartoon-series/", "/hindi-me-toons/")


def is_real_hub(u):
    p = strong(u)
    if "?" in u or "comment-page" in u or "/page/" in p or "/category/" in p or "/tag/" in p or "replytocom" in u or p.endswith("/feed") or "/feed/" in p:
        return False
    segs = [x for x in p.split("/") if x]
    if not segs or segs[0] in C.STATIC_SKIP or segs[0] in _NOT_HUBS:
        return False
    if segs[0] == "hindi":
        return len(segs) > 1
    # root-level / other-category hubs (/disney-xd/..., /hindi-dub/..., /<slug>/)
    return True


def _hub_links(text):
    """every on-site content link (any category), not only /hindi/."""
    out = set()
    for m in re.findall(r'href=["\'](?:https?://(?:www\.)?rareanimes\.(?:mov|com))?(/[^"\'#?]+?)/?["\']', text):
        if is_real_hub(SITE + m):
            out.add(m)
    return out


_SITEMAPS = ("/sitemap_index.xml", "/wp-sitemap.xml", "/sitemap.xml",
             "/post-sitemap.xml", "/page-sitemap.xml")
_SAME_HOSTS = ("www.rareanimes.mov", "rareanimes.mov", "www.rareanimes.com", "rareanimes.com")


def _sitemap_links(max_files=80):
    """EVERY post url the site lists in its WordPress sitemap(s) - finds old
    shows that live outside /hindi/ and never appeared in the feed/archive
    walk.  Never raises; returns {"/path", ...}."""
    out, seen, todo = set(), set(), [SITE + p for p in _SITEMAPS]
    while todo and len(seen) < max_files:
        u = todo.pop(0)
        if u in seen:
            continue
        seen.add(u)
        try:
            r = _get(u)
        except Exception as e:
            print(f"[index] sitemap {u} failed: {e!r}", flush=True)
            continue
        if r.status_code != 200 or _cf(r):
            continue
        for loc in re.findall(r"<loc>\s*(.*?)\s*</loc>", r.text or "", re.S):
            loc = loc.replace("&amp;", "&")
            pu = urlparse(loc)
            if pu.netloc and pu.netloc.lower() not in _SAME_HOSTS:
                continue
            if pu.path.lower().endswith(".xml"):
                todo.append(SITE + pu.path + (f"?{pu.query}" if pu.query else ""))
            else:
                path = pu.path.rstrip("/")
                if path and is_real_hub(SITE + path):
                    out.add(path)
        time.sleep(0.2)
    print(f"[index] sitemap: {len(out)} candidate pages from {len(seen)} files",
          flush=True)
    return out


def collect_targets(feed_pages, full=False, max_pages=400):
    """full=False (default): recent window only -> RSS feed + /home/ +
    current/last month archive. Misses shows that are older than the feed
    window and never got crawled in the first place.
    full=True: ALSO walks the site's /hindi/page/N/ archive listing from
    page 1 until an empty page, so older shows that were never crawled at
    all get picked up too (one-time/periodic backfill, slower)."""
    cand, feed = set(), []
    for page in range(1, feed_pages + 1):
        r = _get(f"{SITE}/feed/?paged={page}")
        items = re.findall(r"<item>(.*?)</item>", r.text, re.S)
        if not items:
            print(f"[index] RSS feed page {page}: no items (HTTP {r.status_code}"
                  f"{', Cloudflare challenge' if _cf(r) else ''})", flush=True)
            break
        for it in items:
            l = re.search(r"<link>(.*?)</link>", it, re.S)
            if l:
                feed.append(l.group(1).strip())
        time.sleep(0.2)
    _t = time.gmtime()
    _py, _pm = (_t.tm_year, _t.tm_mon - 1) if _t.tm_mon > 1 else (_t.tm_year - 1, 12)
    for listing in ("/home/", f"/{_py}/{_pm:02d}/", time.strftime("/%Y/%m/")):
        try:
            r = _get(SITE + listing)
            cand |= _hub_links(r.text)
        except Exception as e:
            print(f"[index] listing {listing} failed: {e!r}", flush=True)
    if full:
        for page in range(1, max_pages + 1):
            url = f"{SITE}/hindi/" if page == 1 else f"{SITE}/hindi/page/{page}/"
            try:
                r = _get(url)
            except Exception as e:
                print(f"[index] archive page {page} failed: {e!r}", flush=True)
                break
            if r.status_code == 404:
                break
            found = _hub_links(r.text)
            found.discard("/hindi")
            if not found:
                break
            cand |= found
            time.sleep(0.2)
    if full:
        for lp in _LIST_PAGES:
            try:
                r = _get(SITE + lp)
                got = _hub_links(r.text) if r.status_code == 200 else set()
                print(f"[index] list page {lp}: HTTP {r.status_code}, "
                      f"{len(got)} show links", flush=True)
                cand |= got
            except Exception as e:
                print(f"[index] list page {lp} failed: {e!r}", flush=True)
        try:
            cand |= _sitemap_links()
        except Exception as e:
            print(f"[index] sitemap walk failed: {e!r}", flush=True)
    cand = {SITE + c for c in cand}
    cand |= set(feed)
    return cand, feed


def run(feed_pages=12, quiet=False, full=False):
    """Refresh the index; returns a summary dict. Never raises for network
    problems (they are reported as 'fails'). full=True also walks the whole
    /hindi/ archive to backfill older shows the feed-only crawl never saw."""
    def log(*a):
        if not quiet:
            print(*a, flush=True)

    cand, feed = collect_targets(feed_pages, full=full)

    # streams.json is NOT in the repo zip -> start empty instead of crashing
    # (this crash silently disabled new-show discovery completely)
    try:
        streams = json.loads((ROOT / "streams.json").read_text())
    except (FileNotFoundError, ValueError):
        streams = {"hub_pages": [], "episode_streams": []}
    streams.setdefault("hub_pages", [])
    streams.setdefault("episode_streams", [])
    try:
        _idx_lines = (ROOT / "episodes_index.jsonl").read_text().splitlines()
    except FileNotFoundError:
        _idx_lines = []
    # a hub already present in the episode index is KNOWN, even if
    # streams.json does not list it
    hub_keys = {strong(h["url"]) for h in streams["hub_pages"]}
    for _l in _idx_lines:
        try:
            _u = json.loads(_l).get("hub_url") if _l.strip() else ""
        except ValueError:
            _u = ""
        if _u:
            hub_keys.add(strong(_u))
    targets = sorted({u for u in cand if is_real_hub(u)}
                     - {u for u in cand if strong(u) in hub_keys}) \
        + sorted({u for u in feed if is_real_hub(u) and strong(u) in hub_keys})
    targets = list(dict.fromkeys(targets))
    log(f"[targets] {len(targets)} hub pages to (re)crawl "
        f"(new + feed-window refresh)")

    hub_by_key = {strong(h["url"]): h for h in streams["hub_pages"]}
    ep_seen = {e["stream"] for e in streams["episode_streams"]}
    old_idx = [json.loads(l) for l in _idx_lines if l.strip()]
    target_keys = {strong(t) for t in targets}

    new_hubs, new_rows, new_store_rows, fails = [], [], [], []
    t0 = time.time()
    for i, url in enumerate(targets):
        html, _ = C.fetch(url)
        if html is None:
            fails.append(url)
            continue
        rec = C.parse_hub_page(url, html)
        new_hubs.append(rec)
        season_hint = None
        info = rec.get("info") or {}
        m = re.search(r"\d+", str(info.get("season") or ""))
        if m:
            season_hint = int(m.group())
        else:
            m2 = P.SEASON_RE.search(rec.get("title", ""))
            if m2:
                season_hint = int(m2.group(1))
        new_rows.extend(P.parse_html(html, rec["url"], rec.get("title", ""),
                                      season_hint))
        for w in rec.get("watch_pages", []):
            shtml, _ = C.fetch(w)
            if shtml is None:
                time.sleep(2)
                shtml, _ = C.fetch(w)
            if shtml is None:
                fails.append("STORE " + w)
                continue
            pt, srows = C.parse_store_page(w, shtml)
            for r in srows:
                if r["stream"] not in ep_seen:
                    ep_seen.add(r["stream"])
                    new_store_rows.append({"source": w, "page": pt,
                                           "episode": r["episode"],
                                           "stream": r["stream"]})
        if (i + 1) % 20 == 0:
            log(f"  [{i+1}/{len(targets)}] hubs={len(new_hubs)} "
                f"ep-rows={len(new_rows)} store={len(new_store_rows)} "
                f"fails={len(fails)} {time.time()-t0:.0f}s")

    for rec in new_hubs:
        hub_by_key[strong(rec["url"])] = rec
    streams["hub_pages"] = sorted(hub_by_key.values(), key=lambda r: r["url"])
    streams["episode_streams"] = streams["episode_streams"] + new_store_rows
    streams["stats"] = {
        "hub_pages": len(streams["hub_pages"]),
        "hub_stream_links": sum(r.get("stream_count", 0)
                                for r in streams["hub_pages"]),
        "store_pages_crawled": len({e.get("source")
                                    for e in streams["episode_streams"]}),
        "episode_streams_from_store": len(streams["episode_streams"]),
        "errors": len(fails),
    }
    streams["generated_at"] = time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime())

    kept = [r for r in old_idx if strong(r.get("hub_url", "")) not in target_keys]
    final = kept + new_rows
    (ROOT / "streams.json").write_text(
        json.dumps(streams, ensure_ascii=False, indent=1))
    with open(ROOT / "episodes_index.jsonl", "w", encoding="utf-8") as f:
        for r in final:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")

    print(f"[index] hubs={len(new_hubs)} ep-rows={len(new_rows)} "
          f"store-rows={len(new_store_rows)} fails={len(fails)} "
          f"({time.time()-t0:.0f}s)", flush=True)
    for f_ in fails[:10]:
        print("[index] FAIL:", f_, flush=True)
    log(f"[merge] hub_pages={len(streams['hub_pages'])} "
        f"episode_streams={len(streams['episode_streams'])}")
    log(f"[merge] index rows {len(old_idx)} -> {len(final)} "
        f"(kept {len(kept)}, fresh {len(new_rows)})")
    log(f"[merge] shows {len({r['show'] for r in old_idx})} -> "
        f"{len({r['show'] for r in final})}")
    return {"targets": len(targets), "new_hubs": len(new_hubs),
            "new_rows": len(new_rows),
            "new_store_rows": len(new_store_rows),
            "fails": len(fails),
            "shows": len({r["show"] for r in final})}


def main():
    args = sys.argv[1:]
    full = "--full" in args
    if full:
        args.remove("--full")
    feed_pages = int(args[0]) if args else 12
    run(feed_pages, full=full)


if __name__ == "__main__":
    main()
