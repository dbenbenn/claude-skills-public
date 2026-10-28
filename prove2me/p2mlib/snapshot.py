"""An immutable copy of the skill at one commit, for a run that must not see later edits.

A carve is dozens of separate tool processes (carve.py, carve_measure.py, ...). A skill fix pushed
mid-run made one carve use old and new code together (2026-10-25). `snapshot()` extracts the skill
with `git archive` into CACHE/<sha>/ (CACHE defaults to ~/.cache/p2m/skill), makes it read-only and
reuses it; with a dirty working tree it snapshots HEAD and prints which uncommitted files it left out,
unless `allow_dirty`, which snapshots the tracked and untracked-but-not-ignored files under
CACHE/<sha>-dirty-<content hash>/."""
import hashlib
import os
import sys
import shutil
import subprocess
import tarfile
import tempfile
import time

DEFAULT_CACHE = '~/.cache/p2m/skill'


class DirtyTree(Exception):
    pass


def default_repo():
    """The skills repository this library lives in (…/skills/prove2me/p2mlib/snapshot.py)."""
    here = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    if os.path.dirname(here) == cache_dir():       # inside a snapshot: the repo is the live one (oaiq-059)
        return os.path.expanduser('~/.claude/skills')
    return here


def cache_dir(cache=None):
    return os.path.abspath(os.path.expanduser(cache or os.environ.get('P2M_SNAPSHOT_CACHE') or DEFAULT_CACHE))


def _git(repo, *args, text=True):
    r = subprocess.run(['git', '-C', repo, *args], capture_output=True, text=text)
    if r.returncode:
        raise RuntimeError('git %s failed: %s' % (' '.join(args), (r.stderr if text else r.stderr.decode()).strip()))
    return r.stdout


def _freeze(path):
    for d, dirs, files in os.walk(path):
        for f in files:
            p = os.path.join(d, f)
            if not os.path.islink(p):
                os.chmod(p, os.stat(p).st_mode & ~0o222)
    for d, dirs, files in os.walk(path, topdown=False):
        os.chmod(d, os.stat(d).st_mode & ~0o222)


def _rmtree(path):
    for d, dirs, files in os.walk(path):
        os.chmod(d, os.stat(d).st_mode | 0o700)
    shutil.rmtree(path)


def _dirty_files(repo):
    out = _git(repo, 'ls-files', '-z', '--cached', '--others', '--exclude-standard')
    return sorted(f for f in out.split('\0') if f and os.path.lexists(os.path.join(repo, f)))


def _publish(cache, name, fill):
    """Build into a temp dir beside the target, freeze, and rename into place (atomic)."""
    os.makedirs(cache, exist_ok=True)
    final = os.path.join(cache, name)
    tmp = tempfile.mkdtemp(prefix='.tmp-' + name[:12] + '-', dir=cache)
    try:
        fill(tmp)
        _freeze(tmp)
        try:
            os.rename(tmp, final)
        except OSError:                       # another process built it first
            _rmtree(tmp)
    except BaseException:
        if os.path.exists(tmp):
            _rmtree(tmp)
        raise
    return final


def snapshot(repo=None, rev=None, cache=None, allow_dirty=False):
    """The path of a read-only copy of REPO at REV (default HEAD), built if absent."""
    repo = os.path.abspath(os.path.expanduser(repo or os.environ.get('P2M_SKILL_REPO') or default_repo()))
    cache = cache_dir(cache)
    if rev is None:
        status = _git(repo, 'status', '--porcelain', '--untracked-files=normal')
        dirty = status.strip()
        if dirty and not allow_dirty:
            # agents share one checkout, so it is often dirty with someone else's work in progress:
            # snapshot the committed HEAD and say what is left out (refusing blocked every carve, and
            # --allow-dirty then snapshotted half-done code; oaiq-055, 2026-10-28)
            sys.stderr.write('note: uncommitted changes in %s are not in this snapshot (HEAD): %s. Commit them '
                             'to use them, or pass --allow-dirty to snapshot the working tree.\n'
                             % (repo, ', '.join(l[3:] for l in status.splitlines()[:8] if l.strip())
                                + (' ...' if len(dirty.splitlines()) > 8 else '')))
        elif dirty:
            files = _dirty_files(repo)
            h = hashlib.sha256()
            for f in files:
                p = os.path.join(repo, f)
                h.update(f.encode() + b'\0')
                h.update(os.readlink(p).encode() if os.path.islink(p) else open(p, 'rb').read())
                h.update(b'\0')
            name = '%s-dirty-%s' % (_git(repo, 'rev-parse', 'HEAD').strip(), h.hexdigest()[:12])

            def fill(tmp):
                for f in files:
                    dst = os.path.join(tmp, f)
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    shutil.copy2(os.path.join(repo, f), dst, follow_symlinks=False)
            return _use(cache, name, fill)
    sha = _git(repo, 'rev-parse', '--verify', (rev or 'HEAD') + '^{commit}').strip()

    def fill(tmp):
        data = _git(repo, 'archive', '--format=tar', sha, text=False)
        with tarfile.open(fileobj=__import__('io').BytesIO(data)) as t:
            t.extractall(tmp, filter='fully_trusted') if hasattr(tarfile, 'data_filter') else t.extractall(tmp)
    return _use(cache, sha, fill)


def _use(cache, name, fill):
    final = os.path.join(cache, name)
    if os.path.isdir(final):
        os.utime(final)                       # in use: pruning goes by last use
        return final
    return _publish(cache, name, fill)


def snapshot_root_of(path, cache=None):
    """The snapshot directory holding PATH, or None when PATH is not inside the cache."""
    cache = cache_dir(cache)
    p = os.path.abspath(path)
    if not p.startswith(cache + os.sep):
        return None
    return os.path.join(cache, p[len(cache) + 1:].split(os.sep)[0])


def prune(cache=None, max_age_days=30):
    """Remove snapshots not used for MAX_AGE_DAYS; returns the removed paths."""
    cache = cache_dir(cache)
    if not os.path.isdir(cache):
        return []
    limit = time.time() - max_age_days * 86400
    gone = []
    for n in sorted(os.listdir(cache)):
        p = os.path.join(cache, n)
        if os.path.isdir(p) and os.stat(p).st_mtime < limit:
            _rmtree(p)
            gone.append(p)
    return gone
