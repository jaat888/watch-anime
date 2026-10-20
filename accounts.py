"""Accounts, sessions and watch progress.

Storage: the Blitz SQL project if SQL_URL is set (permanent), otherwise a local
SQLite file (for testing only; may be wiped on redeploy).
Kept small: sessions expire after 1 year, 40 history rows max per user.
"""
import hashlib, hmac, json, os, re, secrets, sqlite3, threading, time
import urllib.request

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
]

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
        req = urllib.request.Request(SQL_URL, json.dumps({"sql": sql, "params": list(params)}).encode(),
                                     {"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=15) as r:
            return _rows(json.loads(r.read() or b"{}"))
    with _lock:
        if _local is None:
            _local = sqlite3.connect(DB_PATH, check_same_thread=False)
        cur = _local.execute(sql, params)
        _local.commit()
        return cur.fetchall() if cur.description else []

def init():
    if SQL_URL:
        body = json.dumps({"script": ";\n".join(SCHEMA)}).encode()
        urllib.request.urlopen(urllib.request.Request(SQL_URL, body, {"Content-Type": "application/json"}), timeout=15).read()
    else:
        for s in SCHEMA:
            q(s)
try:
    init()
except Exception as e:
    print("[accounts] init failed:", e, flush=True)

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
    q("INSERT OR REPLACE INTO progress VALUES(?,?,?,?,?,?,?)",
      (uid, slug, int(season or 0), int(episode or 0), float(pos or 0), float(dur or 0), time.time()))
    q("DELETE FROM progress WHERE user_id=? AND slug NOT IN (SELECT slug FROM progress WHERE user_id=? ORDER BY updated DESC LIMIT 40)", (uid, uid))

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

# ---- favourites, watched episodes, password change, popularity ----
def set_fav(uid, slug, on):
    if on:
        q("INSERT OR REPLACE INTO favs VALUES(?,?,?)", (uid, slug, time.time()))
        q("DELETE FROM favs WHERE user_id=? AND slug NOT IN (SELECT slug FROM favs WHERE user_id=? ORDER BY added DESC LIMIT 300)", (uid, uid))
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

def popular(limit=20):
    return [r[0] for r in q("SELECT slug FROM progress GROUP BY slug ORDER BY COUNT(*) DESC, MAX(updated) DESC LIMIT ?", (limit,))]
