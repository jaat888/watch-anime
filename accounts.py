"""Accounts, sessions and watch progress.

Storage: the Blitz SQL project if SQL_URL is set (permanent), otherwise a local
SQLite file (for testing only; may be wiped on redeploy).
Kept small: sessions expire after 1 year, 40 history rows max per user.
"""
import hashlib, hmac, json, os, re, secrets, sqlite3, threading, time
import urllib.error
import urllib.request

# Cloudflare (workers.dev) blocks the default "Python-urllib" User-Agent with 403 -> send a normal one
_HDR = {"Content-Type": "application/json",
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36",
        "Accept": "application/json"}

SQL_URL = os.environ.get("SQL_URL", "").rstrip("/")
if SQL_URL and not SQL_URL.endswith("/sql"):
    SQL_URL += "/sql"
DB_PATH = os.environ.get("DB_PATH", "data.db")
SESSION_DAYS = 365
_lock = threading.Lock()
_local = None

SCHEMA = [
 "CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, username TEXT UNIQUE, salt TEXT, pw TEXT, created REAL)",
 "CREATE TABLE IF NOT EXISTS sessions(token TEXT PRIMARY KEY, user_id INTEGER, seen REAL)",
 "CREATE TABLE IF NOT EXISTS progress(user_id INTEGER, slug TEXT, season INTEGER, episode INTEGER, pos REAL, dur REAL, updated REAL, PRIMARY KEY(user_id, slug))",
 "CREATE TABLE IF NOT EXISTS kv(k TEXT PRIMARY KEY, v TEXT)",
 "CREATE TABLE IF NOT EXISTS favs(user_id INTEGER, slug TEXT, added REAL, PRIMARY KEY(user_id, slug))",
 "CREATE TABLE IF NOT EXISTS seen(user_id INTEGER, slug TEXT, eps TEXT, PRIMARY KEY(user_id, slug))",
 "CREATE TABLE IF NOT EXISTS tmdb(slug TEXT PRIMARY KEY, v TEXT)",
 "CREATE TABLE IF NOT EXISTS logs(id INTEGER PRIMARY KEY, ts REAL, lvl TEXT, src TEXT, msg TEXT)",
]

# ---------------------------------------------------------------------------
# SQL transport for the tgstore Cloudflare Worker  (POST <worker>/p/<KEY>/sql)
#
#   request : {"sql": "...", "params": [...]}  |  {"batch": [{sql, params}, ...]}  |  {"script": "..."}
#   reply   : {"columns": [...], "rows": [[...], ...], "rowcount": n, "last_id": n}
#             batch -> {"results": [ {columns, rows, ...}, ... ]}
#   503 {"retry": true}  = the Worker ran out of Telegram calls for this request; send the same query again
#   400 "database disk image is malformed" = the database file inside the Worker is damaged (needs a repair,
#             see db_admin() below) -> retrying is useless, so we stop hammering it (circuit breaker)
# ---------------------------------------------------------------------------
SQL_TIMEOUT = float(os.environ.get("SQL_TIMEOUT") or 90)    # the Worker may re-run a big query for up to ~85 s
SQL_TRIES = int(os.environ.get("SQL_TRIES") or 4)
SQL_BASE = SQL_URL[:-4] if SQL_URL.endswith("/sql") else SQL_URL   # https://worker/p/KEY


class SQLDown(RuntimeError):
    """The SQL service is known to be broken right now; nothing was sent."""


def _body(e):
    try:
        return e.read().decode("utf-8", "replace")[:300]
    except Exception:
        return ""


def _err_text(body):
    """{"error": "..."} -> the message only."""
    try:
        j = json.loads(body)
        if isinstance(j, dict) and j.get("error"):
            return str(j["error"])
    except Exception:
        pass
    return body


def _is_corrupt(msg):
    m = (msg or "").lower()
    return "malformed" in m or "not a database" in m or "database corruption" in m or "file is encrypted" in m


# ---- circuit breaker: after a hard failure stop sending queries for a while ----
_brk_lock = threading.Lock()
_brk = {"fails": 0, "until": 0.0, "why": "", "corrupt": False, "since": 0.0}
_warned = {}


def _warn_once(key, ttl, text):
    now = time.time()
    if now - _warned.get(key, 0) >= ttl:
        _warned[key] = now
        print("[accounts] " + text, flush=True)


def _brk_open_check():
    if _brk["until"] > time.time():
        raise SQLDown("SQL paused for %ds after: %s" % (_brk["until"] - time.time(), _brk["why"]))


def _brk_fail(why, corrupt):
    with _brk_lock:
        _brk["fails"] += 1
        _brk["why"] = why[:200]
        _brk["corrupt"] = corrupt
        if not _brk["since"]:
            _brk["since"] = time.time()
        # corrupt database: probe again after 1, 2, 4 ... max 10 min.  Other errors: 5 s ... max 2 min
        base, cap = (60, 600) if corrupt else (5, 120)
        _brk["until"] = time.time() + min(base * 2 ** min(_brk["fails"] - 1, 8), cap)
    _warn_once("brk", 300, "SQL error: %s - pausing queries (%s)" % ("DATABASE DAMAGED (use Reload from Telegram in admin)" if corrupt else "unavailable", why[:160]))


def _brk_ok():
    if _brk["fails"]:
        print("[accounts] SQL is back after %d failed tries" % _brk["fails"], flush=True)
    with _brk_lock:
        _brk.update(fails=0, until=0.0, why="", corrupt=False, since=0.0)


def sql_state():
    """For the admin panel."""
    return {"url_set": bool(SQL_URL), "ok": _brk["fails"] == 0, "fails": _brk["fails"], "why": _brk["why"],
            "corrupt": _brk["corrupt"], "retry_in": max(0, int(_brk["until"] - time.time())),
            "tmdb_queued": len(_tq)}


def _http(url, payload=None, method="POST", timeout=None):
    """One HTTP call with retries.  -> parsed JSON.  Raises RuntimeError("SQL HTTP code: msg")."""
    data = json.dumps(payload).encode() if payload is not None else None
    last = None
    for attempt in range(max(1, SQL_TRIES)):
        req = urllib.request.Request(url, data, _HDR, method=method)
        try:
            with urllib.request.urlopen(req, timeout=timeout or SQL_TIMEOUT) as r:
                return json.loads(r.read() or b"{}")
        except urllib.error.HTTPError as e:
            msg = _err_text(_body(e))
            last = RuntimeError("SQL HTTP %s: %s" % (e.code, msg))
            last.code, last.corrupt = e.code, _is_corrupt(msg)
            if last.corrupt or e.code in (400, 401, 403, 404, 413, 501):
                raise last from None               # retrying cannot help
        except Exception as e:                     # timeout, DNS, connection reset ...
            last = RuntimeError("SQL network error: %r" % (e,))
            last.code, last.corrupt = 0, False
        if attempt + 1 < SQL_TRIES:
            time.sleep(min(1.5 * 2 ** attempt, 8))
    raise last


def _call(payload, timeout=None):
    """Breaker + retries around one /sql request."""
    _brk_open_check()
    try:
        res = _http(SQL_URL, payload, timeout=timeout)
    except RuntimeError as e:
        if getattr(e, "corrupt", False):
            _brk_fail(str(e), True)
        elif getattr(e, "code", 0) in (0, 429, 500, 502, 503, 504, 530):
            _brk_fail(str(e), False)
        raise
    _brk_ok()
    return res


def _rows(resp):
    """Accept the common response shapes: {rows:[[..]]} or {rows:[{..}]}."""
    if isinstance(resp, dict):
        for k in ("rows", "results", "result", "data"):
            if k in resp:
                resp = resp[k]; break
        else:
            return []
    if isinstance(resp, dict):
        resp = resp.get("rows", [])
    out = []
    for r in resp or []:
        out.append(tuple(r.values()) if isinstance(r, dict) else tuple(r))
    return out


def q(sql, params=()):
    """Run one statement, return list of row tuples."""
    global _local
    if SQL_URL:
        _ready.wait(30)
        return _rows(_call({"sql": sql, "params": list(params)}))
    with _lock:
        if _local is None:
            _local = sqlite3.connect(DB_PATH, check_same_thread=False)
        cur = _local.execute(sql, params)
        _local.commit()
        return cur.fetchall() if cur.description else []


def qb(stmts):
    """Several write statements in ONE request / one transaction (all or nothing).
    stmts = [(sql, params), ...]"""
    global _local
    stmts = [(s, list(p)) for s, p in stmts]
    if not stmts:
        return
    if SQL_URL:
        _ready.wait(30)
        _call({"batch": [{"sql": s, "params": p} for s, p in stmts]})
        return
    with _lock:
        if _local is None:
            _local = sqlite3.connect(DB_PATH, check_same_thread=False)
        try:
            for s, p in stmts:
                _local.execute(s, p)
            _local.commit()
        except Exception:
            _local.rollback()
            raise


def init():
    if SQL_URL:
        try:
            _call({"script": ";\n".join(SCHEMA)})
        except Exception as e:
            if isinstance(e, SQLDown) or getattr(e, "corrupt", False) or getattr(e, "code", 0) != 400:
                raise                  # service down / damaged: trying table by table would only add noise
            print("[accounts] schema script failed (%s) - creating tables one by one" % e, flush=True)
            bad = []
            for st in SCHEMA:                      # one broken statement must not block the rest
                try:
                    _call({"sql": st, "params": []})
                except Exception as e2:
                    bad.append(st[:60] + " -> " + str(e2))
            if bad:
                raise RuntimeError("; ".join(bad))
    else:
        for s in SCHEMA:
            q(s)
_ready = threading.Event()   # set when the first schema attempt is finished

def _init_bg():
    delay = 5
    first = True
    while True:
        try:
            init()
            if not first:
                print("[accounts] init ok on retry", flush=True)
            return _ready.set()
        except Exception as e:
            print("[accounts] init failed: %s" % e, flush=True)
            _ready.set()                 # do not keep requests waiting; they fail fast through the breaker
            first = False
            if not SQL_URL:
                return
            time.sleep(delay)            # the SQL service may be waking up / being repaired: keep trying
            delay = min(delay * 2, 300)

if SQL_URL:
    # remote SQL can be slow/cold: do it in the background so the server opens its port at once;
    # q() waits for it (max 30 s) before the first query
    threading.Thread(target=_init_bg, daemon=True).start()
else:
    _init_bg()

# ---- admin: look at / repair the database that lives inside the Worker --------------------------
def db_admin(action):
    """action: info | check | sync | discard.   Uses the same project link as SQL_URL.
    discard = throw away the Worker's live copy and reload the last backup from Telegram (this is the usual
    cure for 'database disk image is malformed')."""
    if not SQL_URL:
        return {"error": "SQL_URL is not set (local SQLite is in use)"}
    try:
        if action == "info":
            return {"info": _http(SQL_BASE + "/db", None, "GET", 30), "state": sql_state()}
        if action == "check":
            res = _http(SQL_URL, {"sql": "PRAGMA integrity_check", "params": []}, "POST", 120)
            return {"integrity": [r[0] for r in _rows(res)][:20], "state": sql_state()}
        if action == "sync":
            return {"sync": _http(SQL_BASE + "/db/sync", {}, "POST", 120)}
        if action == "discard":
            res = _http(SQL_BASE + "/db/discard", {}, "POST", 120)
            with _brk_lock:
                _brk.update(fails=0, until=0.0, why="", corrupt=False, since=0.0)   # try again at once
            threading.Thread(target=_init_bg, daemon=True).start()
            return {"discard": res}
    except Exception as e:
        return {"error": str(e)}
    return {"error": "unknown action"}


def _hash(pw, salt):
    return hashlib.pbkdf2_hmac("sha256", pw.encode(), bytes.fromhex(salt), 200_000).hex()

def _th(tok):  # only a hash of the token is stored
    return hashlib.sha256(tok.encode()).hexdigest()

def _session(uid):
    tok = secrets.token_urlsafe(32)
    q("INSERT INTO sessions VALUES(?,?,?)", (_th(tok), uid, time.time()))
    return tok

def signup(username, password):
    if not re.fullmatch(r"[A-Za-z0-9_]{3,20}", username or ""):
        return None, "Username must be 3-20 letters, numbers or underscores."
    if len(password or "") < 6:
        return None, "Password must be at least 6 characters."
    username = username.lower()
    if q("SELECT 1 FROM users WHERE username=?", (username,)):
        return None, "That username is already taken."
    salt = secrets.token_hex(16)
    try:
        q("INSERT INTO users(username,salt,pw,created) VALUES(?,?,?,?)", (username, salt, _hash(password, salt), time.time()))
    except Exception:
        return None, "That username is already taken."
    rows = q("SELECT id FROM users WHERE username=?", (username,))
    return _session(rows[0][0]), None

def login(username, password):
    rows = q("SELECT id,salt,pw FROM users WHERE username=?", ((username or "").lower(),))
    if not rows or not hmac.compare_digest(str(rows[0][2]), _hash(password or "", rows[0][1])):
        return None, "Wrong username or password."
    return _session(rows[0][0]), None

_ucache = {}   # token hash -> (expires, user): saves one database round trip per request

def user_for(token):
    if not token:
        return None
    hit = _ucache.get(_th(token))
    if hit and hit[0] > time.time():
        return hit[1]
    rows = q("SELECT u.id,u.username,s.seen FROM sessions s JOIN users u ON u.id=s.user_id WHERE s.token=?", (_th(token),))
    if not rows:
        return None
    uid, name, seen = rows[0]
    now = time.time()
    if now - float(seen) > SESSION_DAYS * 86400:
        q("DELETE FROM sessions WHERE token=?", (_th(token),))
        return None
    if now - float(seen) > 86400:  # sliding expiry: active users stay signed in
        q("UPDATE sessions SET seen=? WHERE token=?", (now, _th(token)))
    user = {"id": int(uid), "username": name}
    if len(_ucache) > 2000:
        _ucache.clear()
    _ucache[_th(token)] = (now + 120, user)
    return user

def logout(token):
    _ucache.clear()
    q("DELETE FROM sessions WHERE token=?", (_th(token),))

def save_progress(uid, slug, season, episode, pos, dur):
    qb([("INSERT OR REPLACE INTO progress VALUES(?,?,?,?,?,?,?)",
         (uid, slug, int(season or 0), int(episode or 0), float(pos or 0), float(dur or 0), time.time())),
        ("DELETE FROM progress WHERE user_id=? AND slug NOT IN (SELECT slug FROM progress WHERE user_id=? ORDER BY updated DESC LIMIT 40)", (uid, uid))])

def get_progress(uid):
    return [dict(slug=r[0], season=int(r[1]), episode=int(r[2]), pos=float(r[3]), dur=float(r[4]))
            for r in q("SELECT slug,season,episode,pos,dur FROM progress WHERE user_id=? ORDER BY updated DESC LIMIT 40", (uid,))]

# ---- admin helpers ----
def admin_stats():
    n = q("SELECT COUNT(*) FROM users")[0][0]
    rows = q("SELECT u.username,u.created,(SELECT MAX(seen) FROM sessions WHERE user_id=u.id),"
             "(SELECT COUNT(*) FROM progress WHERE user_id=u.id) FROM users u ORDER BY u.created DESC LIMIT 500")
    return {"total": int(n), "users": [dict(username=r[0], created=r[1], last_seen=r[2], history=int(r[3])) for r in rows]}

def _uid(username):
    r = q("SELECT id FROM users WHERE username=?", ((username or "").lower(),))
    return r[0][0] if r else None

def admin_set_password(username, new_pw):
    if len(new_pw or "") < 6:
        return "Password must be at least 6 characters."
    uid = _uid(username)
    if uid is None:
        return "User not found."
    salt = secrets.token_hex(16)
    _ucache.clear()
    q("UPDATE users SET salt=?, pw=? WHERE id=?", (salt, _hash(new_pw, salt), uid))
    q("DELETE FROM sessions WHERE user_id=?", (uid,))  # sign the user out everywhere
    return None

def admin_delete(username):
    uid = _uid(username)
    if uid is None:
        return "User not found."
    _ucache.clear()
    for t in ("sessions", "progress"):
        q("DELETE FROM %s WHERE user_id=?" % t, (uid,))
    q("DELETE FROM users WHERE id=?", (uid,))
    return None

def kv_get(k):
    r = q("SELECT v FROM kv WHERE k=?", (k,))
    return r[0][0] if r else None

def kv_set(k, v):
    q("INSERT OR REPLACE INTO kv VALUES(?,?)", (k, v))

# ---- TMDB info cache (genres + description), kept in SQL so restarts keep it ----
def tmdb_all():
    """Whole cache, read in pages of 300 rows (one huge answer would be slow/risky through the Worker)."""
    out, last = {}, ""
    while True:
        rows = q("SELECT slug, v FROM tmdb WHERE slug>? ORDER BY slug LIMIT 300", (last,))
        for slug, v in rows:
            try:
                out[slug] = json.loads(v)
            except Exception:
                pass
        if len(rows) < 300:
            return out
        last = rows[-1][0]

# Saving is write-behind when SQL is remote: the lookup result is already in the app's memory cache, so the
# row only needs to reach SQL "soon".  Rows are collected and sent 40 at a time in ONE request, and nothing is
# sent while the breaker says SQL is down (they stay queued and go out when it is back).
_tq = {}                       # slug -> json text
_tq_lock = threading.Lock()
_tq_wake = threading.Event()
_tq_started = False
TQ_MAX = 5000

def _tq_loop():
    while True:
        _tq_wake.wait(30)
        _tq_wake.clear()
        time.sleep(3)                                  # let more rows pile up -> fewer requests
        while True:
            with _tq_lock:
                items = list(_tq.items())[:40]
            if not items:
                break
            try:
                qb([("INSERT OR REPLACE INTO tmdb VALUES(?,?)", (k, v)) for k, v in items])
            except Exception as e:
                _warn_once("tmdbq", 300, "tmdb save failed (%d rows waiting, will retry): %s" % (len(_tq), e))
                time.sleep(15)
                break
            with _tq_lock:
                for k, v in items:
                    if _tq.get(k) == v:                # not replaced by a newer value meanwhile
                        del _tq[k]

def tmdb_set(slug, obj):
    global _tq_started
    val = json.dumps(obj, separators=(",", ":"))
    if not SQL_URL:
        return q("INSERT OR REPLACE INTO tmdb VALUES(?,?)", (slug, val))
    with _tq_lock:
        if len(_tq) >= TQ_MAX and slug not in _tq:
            _tq.pop(next(iter(_tq)))                   # drop the oldest: it is still in memory and gets re-fetched
        _tq[slug] = val
        if not _tq_started:
            _tq_started = True
            threading.Thread(target=_tq_loop, daemon=True, name="tmdb-save").start()
    _tq_wake.set()

# ---- favourites, watched episodes, password change, popularity ----
def set_fav(uid, slug, on):
    if on:
        qb([("INSERT OR REPLACE INTO favs VALUES(?,?,?)", (uid, slug, time.time())),
            ("DELETE FROM favs WHERE user_id=? AND slug NOT IN (SELECT slug FROM favs WHERE user_id=? ORDER BY added DESC LIMIT 300)", (uid, uid))])
    else:
        q("DELETE FROM favs WHERE user_id=? AND slug=?", (uid, slug))

def get_favs(uid):
    return [r[0] for r in q("SELECT slug FROM favs WHERE user_id=? ORDER BY added DESC LIMIT 300", (uid,))]

def get_seen(uid, slug):
    r = q("SELECT eps FROM seen WHERE user_id=? AND slug=?", (uid, slug))
    return [x for x in (r[0][0] or "").split(",") if x] if r else []

def mark_seen(uid, slug, season, episode):
    key = "%d:%d" % (int(season or 0), int(episode or 0))
    cur = get_seen(uid, slug)
    if key not in cur:
        q("INSERT OR REPLACE INTO seen VALUES(?,?,?)", (uid, slug, ",".join(cur + [key])[-6000:]))

def change_password(uid, token, old, new):
    if len(new or "") < 6:
        return "New password must be at least 6 characters."
    r = q("SELECT salt,pw FROM users WHERE id=?", (uid,))
    if not r or not hmac.compare_digest(str(r[0][1]), _hash(old or "", r[0][0])):
        return "Current password is wrong."
    salt = secrets.token_hex(16)
    _ucache.clear()
    q("UPDATE users SET salt=?, pw=? WHERE id=?", (salt, _hash(new, salt), uid))
    q("DELETE FROM sessions WHERE user_id=? AND token<>?", (uid, _th(token)))  # sign out other devices
    return None

def recent_watch(since, limit=300):
    """slug -> number of distinct users who watched it since `since` (unix time)."""
    return {r[0]: int(r[1]) for r in q(
        "SELECT slug, COUNT(DISTINCT user_id) FROM progress WHERE updated>? "
        "GROUP BY slug ORDER BY 2 DESC LIMIT ?", (float(since), int(limit)))}

def popular(limit=20):
    return [r[0] for r in q("SELECT slug FROM progress GROUP BY slug ORDER BY COUNT(*) DESC, MAX(updated) DESC LIMIT ?", (limit,))]
