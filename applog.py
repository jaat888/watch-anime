#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Persistent application log.

Every line the server prints (plus explicit applog.info/warn/error calls and
uncaught exceptions) is kept in a small in-memory ring AND written in batches
to the `logs` table of the SQL database (accounts.q) - the same "datacenter"
database as users/progress.  So the log survives restarts, redeploys and
resets, as long as SQL_URL is set (a local SQLite file is only a fallback and
is wiped on most free hosts).

The admin panel reads it through /api/admin/logs.

Design rules:
  * logging must NEVER raise or block the server -> everything is try/except,
    DB writes happen in one background thread, in batches;
  * logging must never recurse -> internal problems go to the ORIGINAL stderr
    (sys.__stderr__), never through print();
  * retention is bounded (LOG_KEEP rows, default 5000) so the table stays tiny.
"""
import atexit
import collections
import os
import re
import sys
import threading
import time
import traceback

KEEP_ROWS = int(os.environ.get("LOG_KEEP") or 5000)
MAX_MSG = 700
FLUSH_EVERY = 10.0
BATCH_ROWS = 50          # 4 bound params per row -> 200 params per statement (real SQLite in the Worker allows far more)
MAX_PENDING = 3000
PRUNE_EVERY = 600.0

_lock = threading.Lock()
_flush_lock = threading.Lock()
_ring = collections.deque(maxlen=1000)      # newest last: (ts, lvl, src, msg)
_pending = []                               # rows not yet saved in SQL
_once = {}                                  # key -> last time (rate limit)
_stats = {"queued": 0, "saved": 0, "dropped": 0, "db_errors": 0,
          "last_db_error": "", "last_flush": 0.0, "last_prune": 0.0}
_installed = False
_ORIG_OUT = sys.__stdout__
_ORIG_ERR = sys.__stderr__


def _raw(text):
    """Write straight to the real stderr (never through the Tee)."""
    try:
        _ORIG_ERR.write(text + "\n")
        _ORIG_ERR.flush()
    except Exception:
        pass


def _console(lvl, src, msg):
    try:
        _ORIG_OUT.write(f"[{src}] {msg}\n" if lvl == "info" else f"[{src}] {lvl.upper()}: {msg}\n")
        _ORIG_OUT.flush()
    except Exception:
        pass


def log(lvl, src, msg, console=True):
    """Queue one line.  lvl: info | warn | error."""
    try:
        lvl = lvl if lvl in ("info", "warn", "error") else "info"
        msg = str(msg).replace("\r", "").strip()
        if not msg:
            return
        if len(msg) > MAX_MSG:
            msg = msg[:MAX_MSG] + "…"
        row = (time.time(), lvl, str(src)[:24], msg)
        with _lock:
            _ring.append(row)
            if len(_pending) >= MAX_PENDING:          # DB down for ages: drop oldest
                cut = MAX_PENDING // 4
                del _pending[:cut]
                _stats["dropped"] += cut
            _pending.append(row)
            _stats["queued"] += 1
        if console:
            _console(lvl, src, msg)
    except Exception:
        pass


def info(src, msg, **kw):
    log("info", src, msg, **kw)


def warn(src, msg, **kw):
    log("warn", src, msg, **kw)


def error(src, msg, **kw):
    log("error", src, msg, **kw)


def log_once(key, ttl, lvl, src, msg):
    """Same as log() but at most once per `ttl` seconds for this key
    (keeps repeated upstream failures from flooding the table)."""
    try:
        now = time.time()
        with _lock:
            last = _once.get(key, 0)
            if now - last < ttl:
                return False
            if len(_once) > 2000:
                _once.clear()
            _once[key] = now
        log(lvl, src, msg)
        return True
    except Exception:
        return False


# ------------------------------------------------------------ SQL side ----
def flush(max_rows=200):
    """Write queued rows to SQL.  Returns how many were saved."""
    if not _flush_lock.acquire(blocking=False):
        return 0
    saved = 0
    try:
        with _lock:
            batch = _pending[:max_rows]
            del _pending[:len(batch)]
        if not batch:
            return 0
        import accounts
        try:
            stmts = []
            for i in range(0, len(batch), BATCH_ROWS):
                part = batch[i:i + BATCH_ROWS]
                sql = ("INSERT INTO logs(ts,lvl,src,msg) VALUES "
                       + ",".join(["(?,?,?,?)"] * len(part)))
                stmts.append((sql, [v for row in part for v in row]))
            accounts.qb(stmts)                         # ONE request / one transaction for the whole batch
            saved = len(batch)
        except Exception as e:
            with _lock:                                # put the unsaved rows back
                _pending[:0] = batch[saved:]
                _stats["db_errors"] += 1
                _stats["last_db_error"] = f"{type(e).__name__}: {str(e)[:160]}"
            _raw(f"[applog] DB write failed: {_stats['last_db_error']}")
            return saved
        with _lock:
            _stats["saved"] += saved
            _stats["last_flush"] = time.time()
            _stats["last_db_error"] = ""
        _maybe_prune()
    except Exception as e:
        _raw(f"[applog] flush error: {e!r}")
    finally:
        _flush_lock.release()
    return saved


def _maybe_prune(force=False):
    now = time.time()
    if not force and now - _stats["last_prune"] < PRUNE_EVERY:
        return
    _stats["last_prune"] = now
    try:
        import accounts
        accounts.q("DELETE FROM logs WHERE id <= (SELECT MAX(id) FROM logs) - ?", (KEEP_ROWS,))
    except Exception as e:
        _raw(f"[applog] prune failed: {e!r}")


def _loop():
    time.sleep(2)
    while True:
        try:
            n = flush()
            wait = FLUSH_EVERY if _stats["last_db_error"] == "" else 60.0
            if n >= 200:                # backlog: go again quickly
                wait = 0.5
        except Exception:
            wait = 10.0
        time.sleep(wait)


def query(limit=200, level="all", src="", text="", before=0):
    """-> (rows, origin).  rows newest first; origin 'db' or 'memory'."""
    flush(1000)
    limit = int(max(1, min(int(limit or 200), 1000)))
    where, params = [], []
    if level == "error":
        where.append("lvl='error'")
    elif level == "warn":
        where.append("lvl IN ('warn','error')")
    if src:
        where.append("src=?")
        params.append(src)
    if text:
        where.append("msg LIKE ?")
        params.append("%" + text + "%")
    if before:
        where.append("id<?")
        params.append(int(before))
    sql = ("SELECT id,ts,lvl,src,msg FROM logs"
           + (" WHERE " + " AND ".join(where) if where else "")
           + " ORDER BY id DESC LIMIT ?")
    try:
        import accounts
        rows = accounts.q(sql, params + [limit])
        return [dict(id=int(r[0]), ts=float(r[1]), lvl=r[2], src=r[3], msg=r[4])
                for r in rows], "db"
    except Exception as e:
        _raw(f"[applog] query failed, serving memory: {e!r}")
        with _lock:
            mem = list(_ring)
        out = []
        for i, (ts, lvl, s, msg) in enumerate(reversed(mem)):
            if level == "error" and lvl != "error":
                continue
            if level == "warn" and lvl == "info":
                continue
            if src and s != src:
                continue
            if text and text.lower() not in msg.lower():
                continue
            out.append(dict(id=0, ts=ts, lvl=lvl, src=s, msg=msg))
            if len(out) >= limit:
                break
        return out, "memory"


def sources():
    try:
        import accounts
        return [r[0] for r in accounts.q("SELECT DISTINCT src FROM logs ORDER BY src")]
    except Exception:
        with _lock:
            return sorted({r[2] for r in _ring})


def clear():
    with _lock:
        _ring.clear()
        _pending.clear()
    import accounts
    accounts.q("DELETE FROM logs")


def stats():
    with _lock:
        s = dict(_stats)
        s["pending"] = len(_pending)
        s["memory"] = len(_ring)
    s["keep_rows"] = KEEP_ROWS
    return s


# ------------------------------------------- stdout / stderr capture ------
_ERR_RE = re.compile(r"fail|error|exception|traceback|crash|refused|denied|unavailable", re.I)
_WARN_RE = re.compile(r"warn|timeout|timed out|retry|blocked|expired|challenge|\b(?:403|429|503)\b", re.I)
_SRC_RE = re.compile(r"^\[([A-Za-z0-9_\-]+)\]\s*(.*)$")


_ACCESS_RE = re.compile(r'^"?(GET|POST|HEAD|PUT|DELETE|OPTIONS|PATCH) (\S+) HTTP/[\d.]+"? (\d{3})\b')
# lines we do not store in SQL at all: they are only traffic noise (every poster, every admin refresh)
_NOISY_PATH = re.compile(r"^/(img/|app\.webmanifest|favicon|sw\.js|api/admin/(stats|logs)\b)")


def _from_stream(line, default_lvl):
    line = line.strip()
    if not line or re.fullmatch(r"-{10,}", line):
        return
    m = _SRC_RE.match(line)
    src, msg = (m.group(1), m.group(2)) if m else ("app", line)
    if src == "rt2":
        src = "app"
    a = _ACCESS_RE.match(msg)
    if a:                                   # http.server access line -> its own source, level from the status code
        path, code = a.group(2), int(a.group(3))
        if code < 400 and _NOISY_PATH.match(path):
            return
        if code < 400 and path in ("/", "/healthz", "/health") and code == 200:
            return                          # uptime pings
        log("error" if code >= 500 else "warn" if code >= 400 else "info", "http", msg, console=False)
        return
    lvl = "error" if _ERR_RE.search(msg) else ("warn" if _WARN_RE.search(msg) else default_lvl)
    log(lvl, src, msg, console=False)       # already printed by the real stream


class _Tee:
    """Wraps sys.stdout / sys.stderr: output still appears in the host's
    console, and each complete line is also kept in the persistent log."""

    def __init__(self, stream, default_lvl):
        self._s = stream
        self._lvl = default_lvl
        self._buf = ""
        self._lk = threading.Lock()

    def write(self, text):
        try:
            n = self._s.write(text)
        except Exception:
            n = len(text or "")
        try:
            with self._lk:
                self._buf += text
                while "\n" in self._buf:
                    line, self._buf = self._buf.split("\n", 1)
                    _from_stream(line, self._lvl)
                if len(self._buf) > 8000:
                    self._buf = ""
        except Exception:
            pass
        return n

    def flush(self):
        try:
            self._s.flush()
        except Exception:
            pass

    def __getattr__(self, name):
        return getattr(self._s, name)


def _thread_hook(args):
    if args.exc_type is SystemExit:
        return
    tb = "".join(traceback.format_exception(args.exc_type, args.exc_value, args.exc_traceback))
    log("error", "thread", f"uncaught exception in {getattr(args.thread, 'name', '?')}: {tb[-600:]}",
        console=False)
    _raw(tb)


def _sys_hook(tp, val, tb):
    text = "".join(traceback.format_exception(tp, val, tb))
    log("error", "crash", f"uncaught exception: {text[-600:]}", console=False)
    _raw(text)


def install():
    """Start capturing + saving.  Safe to call more than once."""
    global _installed
    if _installed:
        return
    _installed = True
    sys.stdout = _Tee(sys.stdout, "info")
    sys.stderr = _Tee(sys.stderr, "warn")
    threading.excepthook = _thread_hook
    sys.excepthook = _sys_hook
    atexit.register(lambda: flush(1000))
    threading.Thread(target=_loop, daemon=True, name="applog").start()
