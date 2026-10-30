#!/usr/bin/env python3
"""Commit and push records from the shared p2m-standalone checkout onto origin/main without touching anyone else's state.

usage: push_records.py PATH... (-m MESSAGE [-m MORE]... | -F FILE) [--repo DIR] [--delete]
                       [--allow-lean] [--max-files N] [--dry-run]

About ten headless workers share ONE checkout (~/claude/p2m-standalone, the default --repo), each
writing its own records folder. `git pull --rebase --autostash` there trips over the others'
uncommitted files, and one interrupted rebase left the checkout stuck for 11 hours (2026-10-29,
lessons oaiq-112, -113, -123). This script is the only way records get committed there:

1. Fetch origin/main (under a lock in .git, so concurrent runs do not collide on the ref).
2. Build the commit in a PRIVATE index (a temp file, GIT_INDEX_FILE): read origin/main's tree, then
   `git add` exactly PATH... from the shared working tree, honouring .gitignore. The shared index,
   HEAD, stash and every other file are never read into the commit or modified. (Plumbing rather
   than a temp worktree: no checkout of the ~21k-file tree per push and nothing to clean up if the
   run is killed; the only temp file is the index, removed in all cases.)
3. Refuse before committing: a path outside the repo or the whole repo; added or modified *.lean
   under openai-ports/ (records hold no OpenAI Lean; --allow-lean overrides); an embedded git repo;
   more than --max-files changes (default 1000: a records folder may hold a 100k-file carve tree);
   a file over 50 MB.
4. Commit onto origin/main (author and committer from the repo's git config; the message is used
   as given, so the caller adds the Co-Authored-By line) and push it. If origin moved meanwhile
   (non-fast-forward), fetch and rebuild the same paths from the working tree onto the new tip, up
   to 5 attempts with backoff. The working tree is the truth for the given paths: a newer origin
   version of one of them is replaced, with a warning naming it.
5. Without --delete a file deleted locally stays on origin (the run says so); with --delete,
   tracked files under PATH that no longer exist locally are removed.
6. Bring the shared checkout's `main` up to origin/main, index only: only when HEAD is on main, no
   rebase/merge/cherry-pick/revert/bisect is in progress, no index.lock is held, and main is an
   ancestor of origin/main (a local commit not on origin is never dropped). The index moves by a
   two-tree `read-tree -m -i` (staged entries of others are carried over; a clash leaves everything
   as it was), then `main` by a compare-and-swap update-ref. The working tree is never written:
   files that origin changed but whose local copy differs (pushed from elsewhere) are listed, not
   overwritten or restored. Otherwise the run reports why it did not move the branch.

--dry-run checks the repo and origin (ls-remote), shows the changes and what would happen to the
shared checkout, and writes nothing (new blobs go to a temp object directory).
Exit status: 0 pushed or nothing to push; 1 refused or failed; 2 usage.
"""
import argparse
import contextlib
import errno
import fcntl
import os
import shutil
import sys
import tempfile
import time
import subprocess

REMOTE, BRANCH = 'origin', 'main'
TRACKING = 'refs/remotes/%s/%s' % (REMOTE, BRANCH)
ATTEMPTS = 5
BACKOFF = 2.0                    # seconds before the second attempt, doubled after each failure
LOCK_WAIT = 600                  # seconds to wait for another run's lock
LEAN_ROOT = 'openai-ports/'
MAX_FILE_BYTES = 50 * 1024 * 1024
DEFAULT_REPO = '~/claude/p2m-standalone'
IN_PROGRESS = (('rebase-merge', 'a rebase'), ('rebase-apply', 'a rebase or am'),
               ('MERGE_HEAD', 'a merge'), ('CHERRY_PICK_HEAD', 'a cherry-pick'),
               ('REVERT_HEAD', 'a revert'), ('sequencer', 'a cherry-pick/revert sequence'),
               ('BISECT_LOG', 'a bisect'))
SHOW = 20                        # changed paths listed before "... and N more"


class Refused(Exception):
    pass


def git(top, *args, env=None, input=None, check=True):
    full = dict(os.environ, GIT_TERMINAL_PROMPT='0', GIT_LITERAL_PATHSPECS='1', LC_ALL='C')
    full.update(env or {})
    r = subprocess.run(['git', '-C', top] + list(args), capture_output=True, text=True, env=full,
                       input=input)
    if check and r.returncode:
        raise Refused('git %s failed: %s' % (args[0], (r.stderr or r.stdout).strip()))
    return r


def out(top, *args, **kw):
    return git(top, *args, **kw).stdout.strip()


# ---- paths and locks ---------------------------------------------------------------------------

def repo_dirs(repo):
    top = os.path.realpath(os.path.expanduser(repo))
    if not os.path.isdir(top):
        raise Refused('no such repo: %s' % repo)
    r = git(top, 'rev-parse', '--path-format=absolute', '--show-toplevel', '--absolute-git-dir',
            '--git-common-dir', '--git-path', 'index', check=False)
    if r.returncode:
        raise Refused('not a git checkout: %s' % repo)
    top, gitdir, common, index = r.stdout.split('\n')[:4]
    return os.path.realpath(top), gitdir, common, index


def resolve(top, raw):
    """Repo-relative path for PATH (absolute, or relative to the repo root)."""
    p = os.path.normpath(raw if os.path.isabs(raw) else os.path.join(top, raw))
    real = os.path.join(os.path.realpath(os.path.dirname(p)), os.path.basename(p))
    rel = os.path.relpath(real, top)
    if rel == '.' or rel == '..' or rel.startswith('..' + os.sep):
        raise Refused('%r: not a path inside %s (the whole repo is never pushed)' % (raw, top))
    if rel.split(os.sep)[0] == '.git':
        raise Refused('%r: inside .git' % raw)
    return rel.replace(os.sep, '/')


@contextlib.contextmanager
def locked(common):
    """flock on .git/push_records.lock: one run at a time fetches or moves the shared refs."""
    with open(os.path.join(common, 'push_records.lock'), 'a') as f:
        deadline = time.time() + LOCK_WAIT
        while True:
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except OSError as e:
                if e.errno not in (errno.EAGAIN, errno.EACCES) or time.time() > deadline:
                    raise Refused('could not take %s within %d s' % (f.name, LOCK_WAIT))
                time.sleep(0.5)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


# ---- remote ------------------------------------------------------------------------------------

def fetch(top):
    """Fetch origin's main into refs/remotes/origin/main; return its sha. Call under the lock."""
    err = ''
    for i in range(3):
        r = git(top, '-c', 'gc.auto=0', '-c', 'maintenance.auto=false', 'fetch', '-q',
                '--no-write-fetch-head', REMOTE, '+refs/heads/%s:%s' % (BRANCH, TRACKING), check=False)
        if r.returncode == 0:
            return out(top, 'rev-parse', TRACKING)
        err = r.stderr.strip()
        time.sleep(1 + i)
    raise Refused('fetch from %s failed: %s' % (REMOTE, err))


def push(top, sha):
    """Push sha to origin main by URL, so git does not touch refs/remotes/origin/main outside the
    lock; record_pushed() moves that ref afterwards."""
    url = out(top, 'remote', 'get-url', '--push', REMOTE)
    return git(top, 'push', '-q', url, '%s:refs/heads/%s' % (sha, BRANCH), check=False)


def record_pushed(top, sha):
    """After a push: refs/remotes/origin/main := sha when that is a fast-forward of it."""
    cur = out(top, 'rev-parse', '-q', '--verify', TRACKING, check=False)
    if not cur or git(top, 'merge-base', '--is-ancestor', cur, sha, check=False).returncode == 0:
        git(top, 'update-ref', TRACKING, sha, check=False)


# ---- building the commit -----------------------------------------------------------------------

def parse_raw(text):
    """[(status, new_mode, new_sha, path)] from `diff-index --raw -z`."""
    parts, res = text.split('\0'), []
    i = 0
    while i + 1 < len(parts) and parts[i].startswith(':'):
        _om, nm, _os, ns, st = parts[i][1:].split(' ')
        res.append((st[0], nm, ns, parts[i + 1]))
        i += 2
    return res


def is_openai_lean(path):
    return path.startswith(LEAN_ROOT) and path.endswith('.lean')


def build(top, base, paths, opts, env):
    """Stage PATHS from the working tree onto base's tree in the private index env['GIT_INDEX_FILE'].
    Returns (tree or None if nothing changes, changes, notes)."""
    notes = []
    git(top, 'read-tree', base, env=env)
    present = []
    for p in paths:
        if os.path.lexists(os.path.join(top, p)):
            present.append(p)
        elif not out(top, 'ls-tree', '-r', '--name-only', base, '--', p):
            raise Refused('%s: no such file or directory, locally or on origin' % p)
        elif opts.delete:
            present.append(p)                        # `add -A` records the removal
        else:
            notes.append('%s is gone locally but stays on origin (pass --delete to remove it)' % p)
    if not present:
        return None, [], notes
    # cheap pre-check on the untracked files before hashing anything (a carve tree is 100k files)
    new = [f for f in out(top, 'ls-files', '-z', '-o', '--exclude-standard', '--', *present,
                          env=env).split('\0') if f]
    check_files([('A', f) for f in new], opts)
    git(top, 'add', '-A' if opts.delete else '--ignore-removal', '--', *present, env=env)
    if not opts.delete:
        gone = [f for f in out(top, 'ls-files', '-z', '--deleted', '--', *present, env=env).split('\0') if f]
        if gone:
            notes.append('%d file(s) under %s are gone locally but stay on origin (pass --delete to '
                         'remove them): %s' % (len(gone), ', '.join(present), ', '.join(gone[:5])))
    changes = parse_raw(out(top, 'diff-index', '--cached', '--raw', '-z', '--no-renames', base, env=env))
    if not changes:
        return None, [], notes
    check_files([(st, p) for st, _m, _s, p in changes], opts)
    bad = [p for st, m, _s, p in changes if st != 'D' and m == '160000']
    if bad:
        raise Refused('embedded git repositories are not records: %s' % ', '.join(bad))
    blobs = [(s, p) for st, _m, s, p in changes if st != 'D']
    if blobs:
        sizes = out(top, 'cat-file', '--batch-check=%(objectsize)', env=env,
                    input=''.join(s + '\n' for s, _p in blobs)).split('\n')
        big = [p for (_s, p), n in zip(blobs, sizes) if n.isdigit() and int(n) > MAX_FILE_BYTES]
        if big:
            raise Refused('files over %d MB: %s' % (MAX_FILE_BYTES >> 20, ', '.join(big)))
    return out(top, 'write-tree', env=env), [(st, p) for st, _m, _s, p in changes], notes


def check_files(changes, opts):
    if len(changes) > opts.max_files:
        raise Refused('%d files to commit, more than --max-files %d (a carve tree in the records '
                      'folder? pass narrower paths, ignore it in .gitignore, or raise --max-files): %s'
                      % (len(changes), opts.max_files, ', '.join(p for _s, p in changes[:5])))
    lean = [p for st, p in changes if st != 'D' and is_openai_lean(p)]
    if lean and not opts.allow_lean:
        raise Refused('refusing OpenAI Lean under %s (records hold no OpenAI Lean; --allow-lean if '
                      'this is our own): %s' % (LEAN_ROOT, ', '.join(lean[:10])))


def newer_on_origin(top, base, changes):
    """Our changed paths that origin changed since the shared checkout's HEAD."""
    head = out(top, 'rev-parse', '-q', '--verify', 'HEAD^{commit}', check=False)
    if not head or head == base:
        return []
    ours = [p for _st, p in changes]
    theirs = set(f for f in out(top, 'diff-tree', '-r', '-z', '--name-only', '--no-renames', head, base,
                                '--', *ours, check=False).split('\0') if f)
    return [p for p in ours if p in theirs]


def show_changes(changes):
    lines = ['  %s %s' % (st, p) for st, p in changes[:SHOW]]
    if len(changes) > SHOW:
        lines.append('  ... and %d more' % (len(changes) - SHOW))
    return '\n'.join(lines)


# ---- the shared checkout -----------------------------------------------------------------------

def advance_shared(top, gitdir, index, dry_run=False):
    """Move the shared checkout's main to origin/main, index only, when that is safe; return a line."""
    say = 'shared checkout: '
    for marker, what in IN_PROGRESS:
        if os.path.exists(os.path.join(gitdir, marker)):
            return say + '%s is in progress there (.git/%s); main not moved' % (what, marker)
    ref = out(top, 'symbolic-ref', '-q', 'HEAD', check=False)
    if ref != 'refs/heads/' + BRANCH:
        return say + 'HEAD is %s, not %s; not moved' % (ref or 'detached', BRANCH)
    m = out(top, 'rev-parse', 'refs/heads/' + BRANCH)
    o = out(top, 'rev-parse', TRACKING)
    if m == o:
        return say + '%s already at %s/%s' % (BRANCH, REMOTE, BRANCH)
    if git(top, 'merge-base', '--is-ancestor', m, o, check=False).returncode:
        n = out(top, 'rev-list', '--count', '%s..%s' % (o, m))
        return say + ('%s has %s commit(s) not on origin (unpushed or diverged); not moved. Push or '
                      'rescue them by hand.' % (BRANCH, n))
    if dry_run:
        return say + 'would fast-forward %s %s..%s (index only)' % (BRANCH, m[:8], o[:8])
    lock = index + '.lock'
    try:
        fd = os.open(lock, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o666)
    except FileExistsError:
        return say + '%s exists (a git command is running there); not moved' % lock
    tmpd, done = tempfile.mkdtemp(prefix='push_records.'), False
    try:
        tmp_index = os.path.join(tmpd, 'index')
        if os.path.exists(index):
            shutil.copyfile(index, tmp_index)
        r = git(top, 'read-tree', '-m', '-i', m, o, env={'GIT_INDEX_FILE': tmp_index}, check=False)
        if r.returncode:
            return say + ('staged changes there clash with origin; not moved (%s)'
                          % r.stderr.strip().split('\n')[0])
        r = git(top, 'update-ref', '-m', 'push_records: fast-forward to %s/%s' % (REMOTE, BRANCH),
                'refs/heads/' + BRANCH, o, m, check=False)
        if r.returncode:
            return say + '%s moved meanwhile; not moved' % BRANCH
        with open(tmp_index, 'rb') as f:
            os.write(fd, f.read())
        os.fsync(fd)
        os.close(fd)
        fd = None
        os.rename(lock, index)
        done = True
    finally:
        if fd is not None:
            os.close(fd)
        if not done and os.path.exists(lock):
            os.unlink(lock)
        shutil.rmtree(tmpd, ignore_errors=True)
    line = say + '%s fast-forwarded %s..%s (index only; working tree untouched)' % (BRANCH, m[:8], o[:8])
    stale = differing_locally(top, m, o)
    if stale:
        line += ('\n  %d file(s) origin changed differ in the working tree, left as they are: %s'
                 % (len(stale), ', '.join(stale[:5]) + (' ...' if len(stale) > 5 else '')))
    return line


def differing_locally(top, m, o):
    """Paths changed m..o whose working-tree copy is not o's version (missing, or another content)."""
    changed = parse_tree_diff(out(top, 'diff-tree', '-r', '-z', '--no-renames', m, o))
    res, check = [], []
    for st, sha, p in changed:
        here = os.path.lexists(os.path.join(top, p))
        if st == 'D':
            if here:
                res.append(p)
        elif not here:
            res.append(p)
        elif os.path.isfile(os.path.join(top, p)) and not os.path.islink(os.path.join(top, p)):
            check.append((sha, p))
    if check:
        hashes = out(top, 'hash-object', '--stdin-paths', input=''.join(p + '\n' for _s, p in check)).split('\n')
        res += [p for (sha, p), h in zip(check, hashes) if h != sha]
    return sorted(res)


def parse_tree_diff(text):
    return [(st, ns, p) for st, _nm, ns, p in parse_raw(text)]


# ---- main --------------------------------------------------------------------------------------

def message_of(a):
    if a.file:
        with open(a.file) as f:
            msg = f.read()
    else:
        msg = '\n\n'.join(a.message)
    msg = msg.strip()
    if not msg:
        raise Refused('empty commit message')
    return msg + '\n'


def parse_args(argv):
    ap = argparse.ArgumentParser(prog='push_records.py', description=__doc__.split('\n')[0])
    ap.add_argument('paths', nargs='+', metavar='PATH', help='files or folders, absolute or relative to the repo root')
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument('-m', dest='message', action='append', help='message paragraph (repeatable)')
    g.add_argument('-F', dest='file', help='read the message from FILE')
    ap.add_argument('--repo', default=DEFAULT_REPO)
    ap.add_argument('--delete', action='store_true', help='remove tracked files under PATH missing locally')
    ap.add_argument('--allow-lean', action='store_true', help='allow *.lean under openai-ports/')
    ap.add_argument('--max-files', type=int, default=1000)
    ap.add_argument('--dry-run', action='store_true')
    return ap.parse_args(argv)


def run(a):
    top, gitdir, common, index = repo_dirs(a.repo)
    paths = [resolve(top, p) for p in a.paths]
    msg = message_of(a)
    tmpd = tempfile.mkdtemp(prefix='push_records.')
    try:
        env = {'GIT_INDEX_FILE': os.path.join(tmpd, 'index')}
        if a.dry_run:
            return dry_run(top, gitdir, common, index, paths, a, env, tmpd)
        with locked(common):
            base = fetch(top)
        for attempt in range(1, ATTEMPTS + 1):
            tree, changes, notes = build(top, base, paths, a, env)
            for n in notes:
                print('note: ' + n)
            if tree is None:
                print('nothing to push: %s match %s/%s' % (', '.join(paths), REMOTE, BRANCH))
                break
            if attempt == 1:
                newer = newer_on_origin(top, base, changes)
                if newer:
                    print('warning: origin changed these since the shared checkout\'s HEAD, and the local '
                          'copy replaces them (the old version stays in history): ' + ', '.join(newer))
            sha = out(top, 'commit-tree', tree, '-p', base, input=msg)
            r = push(top, sha)
            if r.returncode == 0:
                with locked(common):
                    record_pushed(top, sha)
                print('pushed %s to %s/%s (%d change(s), %d attempt%s):\n%s'
                      % (sha[:8], REMOTE, BRANCH, len(changes), attempt, 's' if attempt > 1 else '',
                         show_changes(changes)))
                break
            err = (r.stderr or r.stdout).strip()
            if attempt == ATTEMPTS:
                raise Refused('push failed %d times; last error:\n%s' % (ATTEMPTS, err))
            print('push attempt %d failed (%s); fetching and rebuilding' % (attempt, err.split('\n')[-1]))
            time.sleep(BACKOFF * 2 ** (attempt - 1))
            with locked(common):
                base = fetch(top)
        with locked(common):
            print(advance_shared(top, gitdir, index))
        return 0
    finally:
        shutil.rmtree(tmpd, ignore_errors=True)


def dry_run(top, gitdir, common, index, paths, a, env, tmpd):
    r = git(top, 'ls-remote', '--exit-code', REMOTE, 'refs/heads/' + BRANCH, check=False)
    if r.returncode:
        raise Refused('cannot read %s/%s: %s' % (REMOTE, BRANCH, r.stderr.strip()))
    remote = r.stdout.split()[0]
    print('repo %s, %s/%s at %s' % (top, REMOTE, BRANCH, remote[:8]))
    base = out(top, 'rev-parse', TRACKING)
    if base != remote:
        print('note: the local %s is at %s; a real run fetches first' % (TRACKING, base[:8]))
    objects = os.path.join(tmpd, 'objects')
    os.mkdir(objects)
    env = dict(env, GIT_OBJECT_DIRECTORY=objects,
               GIT_ALTERNATE_OBJECT_DIRECTORIES=os.path.join(common, 'objects'))
    tree, changes, notes = build(top, base, paths, a, env)
    for n in notes:
        print('note: ' + n)
    if tree is None:
        print('dry run: nothing to push')
    else:
        print('dry run: would commit %d change(s) onto %s:\n%s' % (len(changes), base[:8], show_changes(changes)))
    print(advance_shared(top, gitdir, index, dry_run=True))
    return 0


def main(argv=None):
    a = parse_args(argv)
    try:
        return run(a)
    except Refused as e:
        print('push_records: %s' % e)
        return 1


if __name__ == '__main__':
    sys.exit(main())
