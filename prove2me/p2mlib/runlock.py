"""One live run per carve: a script takes an exclusive flock named by what it writes, or exits 3
naming the run that holds it. The kernel drops a flock when its holder dies, so a lock is never
stale. (2026-10-23: a resumed agent restarted a PosteriorReplicas pipeline it had already started an
hour before, and two builds wrote the same .olean files.)

A holder that is told to stop (SIGTERM, SIGHUP, SIGINT) first stops every process it started, so its
lock is never free while its lake/lean children still compile. (2026-10-26, oaiq-003 and oaiq-012:
killing carve_pipeline left the old lean writing the .olean the restarted run was building.) Only
kill -9 still orphans them.

Locks live in $P2M_LOCK_DIR, default /tmp/p2m-locks-<uid>; each holds a JSON line saying who has it."""
import fcntl
import hashlib
import json
import os
import signal
import sys
import threading
import time

_held = {}            # key -> open file; kept for the life of the process
last_refusal = None   # the message of the last refusal (for tests)


def lock_dir():
    return os.environ.get('P2M_LOCK_DIR') or '/tmp/p2m-locks-%d' % os.getuid()


def dir_key(kind, path):
    """The key of a run of KIND over the carve that PATH (its config file or directory) belongs to."""
    p = os.path.realpath(path)
    return '%s|%s' % (kind, os.path.dirname(p) if os.path.isfile(p) or p.endswith('.json') else p)


def build_key(ws, folder):
    """The key of a module build of Solutions/FOLDER in workspace WS."""
    return 'build|%s|%s' % (os.path.realpath(ws), folder)


def _path(key):
    return os.path.join(lock_dir(), hashlib.sha1(key.encode()).hexdigest()[:16] + '.lock')


def cmdline(pid):
    """The command line of a live process, or ''."""
    try:
        return ' '.join(open('/proc/%d/cmdline' % int(pid), 'rb').read().decode(errors='replace').split('\0')).strip()
    except (OSError, ValueError, TypeError):
        return ''


def describe(h):
    """'pid N (WHAT), started T; command: CMD' for a holder record."""
    cmd = cmdline(h.get('pid'))
    return 'pid %s (%s), started %s%s' % (h.get('pid', '?'), h.get('what', '?'), h.get('started', '?'),
                                          '; command: ' + cmd if cmd else '')


def held_by(key):
    """The holder's record if a live process holds KEY, else None."""
    p = _path(key)
    if not os.path.exists(p):
        return None
    with open(p, 'r+') as f:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            try:
                return json.loads(f.read() or '{}')
            except ValueError:
                return {}
        fcntl.flock(f, fcntl.LOCK_UN)
    return None


def hold(key, what=''):
    """Hold KEY until this process exits; if another live process holds it, print who and exit 3."""
    global last_refusal
    if key in _held:
        return
    os.makedirs(lock_dir(), exist_ok=True)
    f = open(_path(key), 'a+')
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        f.seek(0)
        try:
            h = json.loads(f.read() or '{}')
        except ValueError:
            h = {}
        f.close()
        last_refusal = ('%s is already running on %s: %s. Wait for it or stop it; '
                        'do not start a second copy.' % (what or 'this step', key.split('|', 1)[1], describe(h)))
        print(last_refusal, file=sys.stderr)
        sys.exit(3)
    f.seek(0)
    f.truncate()
    f.write(json.dumps({'pid': os.getpid(), 'what': what, 'key': key,
                        'started': time.strftime('%Y-%m-%d %H:%M:%S %Z')}))
    f.flush()
    _held[key] = f
    _stop_tree_on_signals()


def _descendants(root):
    """The pids of root's descendants, from /proc."""
    kids = {}
    for d in os.listdir('/proc'):
        if d.isdigit():
            try:
                kids.setdefault(int(open('/proc/%s/stat' % d).read().rsplit(')', 1)[1].split()[1]), []).append(int(d))
            except (OSError, ValueError, IndexError):
                continue
    out, todo = [], [root]
    while todo:
        for k in kids.get(todo.pop(), []):
            out.append(k)
            todo.append(k)
    return out


def _running(pid):
    try:
        return open('/proc/%d/stat' % pid).read().rsplit(')', 1)[1].split()[0] != 'Z'
    except (OSError, IndexError):
        return False


def _send(pid, sig):
    try:
        os.kill(pid, sig)
    except OSError:
        pass


def stop_tree(root=None, grace=5.0):
    """Stops every descendant of root (default: this process). Freezes them first, so none can start
    another or leave the tree when its parent dies; then SIGTERM and SIGCONT; SIGKILL what is left
    after `grace` seconds."""
    root, frozen = root or os.getpid(), []
    for _ in range(50):
        new = [p for p in _descendants(root) if p not in frozen]
        if not new:
            break
        for p in new:
            _send(p, signal.SIGSTOP)
        frozen += new
    for sig in (signal.SIGTERM, signal.SIGCONT):
        for p in frozen:
            _send(p, sig)
    deadline = time.time() + grace
    while time.time() < deadline and any(_running(p) for p in frozen):
        time.sleep(0.05)
    for p in frozen:
        if _running(p):
            _send(p, signal.SIGKILL)


_on_stop = []        # callables(signum) run when a signal stops this process, after its children stopped


def at_stop(fn):
    """Run fn(signum) when SIGTERM, SIGHUP or SIGINT stops this process (after its children are stopped);
    a failing fn is ignored. carve_pipeline marks its monitoring-page section failed this way."""
    _on_stop.append(fn)


def peek(key, needle):
    """The holder record of KEY when its recorded pid is alive and its command line contains `needle`,
    else None. Takes no lock (held_by takes the flock for an instant, which a starting run could hit):
    for readers that poll, such as the monitoring-page reporter."""
    try:
        h = json.loads(open(_path(key)).read() or '{}')
    except (OSError, ValueError):
        return None
    pid = h.get('pid') if isinstance(h, dict) else None
    return h if pid and needle in cmdline(pid) else None


def _stop_and_exit(signum, frame):
    stop_tree()
    for fn in list(_on_stop):
        try:
            fn(signum)
        except Exception:
            pass
    if signum == signal.SIGINT:
        raise KeyboardInterrupt     # as before: finally blocks run, and the exit status says SIGINT
    signal.signal(signum, signal.SIG_DFL)
    os.kill(os.getpid(), signum)


def _stop_tree_on_signals():
    if threading.current_thread() is not threading.main_thread():
        return
    for s in (signal.SIGTERM, signal.SIGHUP, signal.SIGINT):
        if signal.getsignal(s) != signal.SIG_IGN:   # a nohup run's ignored hangup stays ignored
            signal.signal(s, _stop_and_exit)
