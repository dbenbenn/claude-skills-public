"""One live run per carve: a script takes an exclusive flock named by what it writes, or exits 3
naming the run that holds it. The kernel drops a flock when its holder dies, so a lock is never
stale. (2026-10-23: a resumed agent restarted a PosteriorReplicas pipeline it had already started an
hour before, and two builds wrote the same .olean files.)

Locks live in $P2M_LOCK_DIR, default /tmp/p2m-locks-<uid>; each holds a JSON line saying who has it."""
import fcntl
import hashlib
import json
import os
import sys
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
        last_refusal = ('%s is already running on %s: pid %s (%s), started %s. Wait for it or stop it; '
                        'do not start a second copy.' % (what or 'this step', key.split('|', 1)[1],
                                                          h.get('pid', '?'), h.get('what', '?'),
                                                          h.get('started', '?')))
        print(last_refusal, file=sys.stderr)
        sys.exit(3)
    f.seek(0)
    f.truncate()
    f.write(json.dumps({'pid': os.getpid(), 'what': what, 'key': key,
                        'started': time.strftime('%Y-%m-%d %H:%M:%S %Z')}))
    f.flush()
    _held[key] = f
