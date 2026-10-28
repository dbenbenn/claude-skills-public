#!/usr/bin/env python3
"""Which untracked files in the prove2me workspace exist nowhere we keep work.

usage: workspace_audit.py [--min-age DAYS] [--near FRACTION] [--list KINDS] [--json PATH] [--quiet]

The workspace is a clone of the platform's repo, so everything we put there is untracked; its
`git status` cannot say whether a file was ever copied back to a mission repo. This sorts every
untracked file into one kind:

  active      modified within --min-age days (default 2): another session may be using it; not judged
  backed      byte-identical to a blob reachable from a remote-tracking branch of one of our
              GitHub repos (an unpushed commit does not count)
  draft-stub  a statement stub stubs.py recorded in Theorems/.drafts.json (its mission dir has it)
  mirror      any other Theorems/ or Definitions/ file: the published-statement mirror that
              fetch_theorems and the staging scripts write (NOT checked against the platform)
  near-copy   a .lean file at least --near (default 0.9) of whose substantive lines occur in some
              file in that GitHub history: an earlier or later draft of committed work
  unbacked    everything else: read it before deleting it

Read-only: no Lean, no platform calls, nothing written outside the index cache
(~/.cache/p2m/workspace_audit, keyed by each repo's remote-tracking refs). sync_workspace.py runs
it with --quiet at session start. It replaces the one-off triage of 2026-10-06 (3,054 files, 1,671
archived to ~/claude/archive/workspace-scratch-2026-10-06.tar.gz).

Content is compared, never parsed: a declaration-name test would need Lean on both sides
(LeanInfo costs ~10 s a file), and a regex one could call new work superseded.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from collections import Counter
from dataclasses import dataclass, field

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib.workspace import workspace, DRAFTS  # noqa: E402

CACHE = os.path.expanduser('~/.cache/p2m/workspace_audit')
ROOTS = ('~/claude', '~')
SKIP_DIRS = ('.lake', '.claude', 'node_modules', 'archive')
TOOLING = (DRAFTS, DRAFTS + '.lock')
KINDS = ('active', 'backed', 'draft-stub', 'mirror', 'near-copy', 'unbacked')
TRIVIAL = ('import', '--', 'open', 'namespace', 'end', 'variable', 'section', 'set_option')


def git(cwd, *args, inp=None):
    r = subprocess.run(['git', '-C', cwd] + list(args), capture_output=True, input=inp)
    return r.stdout


def line_keys(text):
    """Hashes of the lines that say something: long enough to be specific, not boilerplate."""
    out = set()
    for raw in text.splitlines():
        s = raw.strip()
        if len(s) > 25 and not s.startswith(TRIVIAL):
            out.add(int.from_bytes(hashlib.blake2b(s.encode(), digest_size=8).digest(), 'big'))
    return out


def github(url):
    return 'github.com' in url


def find_repos(roots=ROOTS):
    """Git repos up to three levels under each root, skipping build trees, worktrees and archives."""
    seen = []
    for root in roots:
        root = os.path.expanduser(root)
        base = root.count(os.sep)
        for d, subdirs, _ in os.walk(root):
            if '.git' in subdirs or os.path.isfile(os.path.join(d, '.git')):
                if os.path.realpath(d) not in seen:
                    seen.append(os.path.realpath(d))
            subdirs[:] = [s for s in subdirs if s not in SKIP_DIRS + ('.git',) and not s.startswith('.')
                          and d.count(os.sep) - base < 2]
    return seen


@dataclass
class Index:
    blobs: set = field(default_factory=set)      # blob ids reachable from remote-tracking refs
    lines: set = field(default_factory=set)      # line_keys of every .lean blob among them
    repos: list = field(default_factory=list)    # (repo, url) indexed

    @classmethod
    def build(cls, repos, backed=github, cache_dir=CACHE):
        idx = cls()
        for repo in repos:
            url = git(repo, 'remote', 'get-url', 'origin').decode().strip()
            if not url or not backed(url):
                continue
            # a partial clone (the blobless openai/math one) would fetch every missing blob, one by one,
            # in rev-list --objects: sync_workspace hung (2026-10-28); none of ours is partial
            if git(repo, 'config', '--get', 'remote.origin.promisor').strip() == b'true':
                continue
            refs = git(repo, 'for-each-ref', '--format=%(objectname) %(refname)', 'refs/remotes').decode().split('\n')
            refs = sorted(r for r in refs if r and not r.endswith('/HEAD'))
            if not refs:
                continue
            blobs, lines = cls._repo(repo, refs, cache_dir)
            idx.blobs |= blobs
            idx.lines |= lines
            idx.repos.append((repo, url))
        return idx

    @staticmethod
    def _repo(repo, refs, cache_dir):
        key = hashlib.sha1(('\n'.join([repo] + refs)).encode()).hexdigest()
        cf = os.path.join(cache_dir, key + '.json') if cache_dir else None
        if cf and os.path.exists(cf):
            d = json.load(open(cf))
            return set(d['blobs']), set(d['lines'])
        objs = git(repo, 'rev-list', '--objects', *[r.split(' ', 1)[0] for r in refs]).decode().split('\n')
        named = {}
        for o in objs:
            if o:
                sha, _, path = o.partition(' ')
                named.setdefault(sha, path)
        types = git(repo, 'cat-file', '--batch-check=%(objectname) %(objecttype)',
                    inp='\n'.join(named).encode()).decode().split('\n')
        blobs = {t.split()[0] for t in types if t.endswith(' blob')}
        lean = [b for b in blobs if named.get(b, '').endswith('.lean')]
        lines = set()
        if lean:
            out = git(repo, 'cat-file', '--batch', inp='\n'.join(lean).encode())
            i = 0
            while i < len(out):
                j = out.index(b'\n', i)
                size = int(out[i:j].split()[2])
                lines |= line_keys(out[j + 1:j + 1 + size].decode('utf-8', 'replace'))
                i = j + 1 + size + 1
        if cf:
            os.makedirs(cache_dir, exist_ok=True)
            json.dump({'blobs': sorted(blobs), 'lines': sorted(lines)}, open(cf, 'w'))
        return blobs, lines


@dataclass
class Record:
    path: str
    kind: str
    size: int
    mtime: float
    coverage: float = None


def untracked(ws):
    out = git(ws, 'status', '--porcelain=v1', '-z', '-uall').decode('utf-8', 'surrogateescape')
    return [e[3:] for e in out.split('\0') if e.startswith('?? ') and e[3:] not in TOOLING]


def audit(ws, idx, min_age_days=2, near=0.9, now=None):
    now = now or time.time()
    paths = untracked(ws)
    if not paths:
        return []
    hashes = git(ws, 'hash-object', '--stdin-paths', inp='\n'.join(paths).encode()).decode().split()
    drafts = {}
    p = os.path.join(ws, DRAFTS)
    if os.path.exists(p):
        drafts = json.load(open(p))
    out = []
    for path, h in zip(paths, hashes):
        full = os.path.join(ws, path)
        st = os.stat(full)
        rec = Record(path, '', st.st_size, st.st_mtime)
        top = path.split('/', 1)[0]
        if st.st_mtime > now - min_age_days * 86400:
            rec.kind = 'active'
        elif h in idx.blobs:
            rec.kind = 'backed'
        elif top in ('Theorems', 'Definitions') and path.endswith('.lean'):
            rec.kind = 'draft-stub' if path[:-5].replace('/', '.') in drafts else 'mirror'
        elif path.endswith('.lean'):
            keys = line_keys(open(full, encoding='utf-8', errors='replace').read())
            rec.coverage = len(keys & idx.lines) / len(keys) if keys else 0.0
            rec.kind = 'near-copy' if keys and rec.coverage >= near else 'unbacked'
        else:
            rec.kind = 'unbacked'
        out.append(rec)
    return out


def summary(records):
    c = Counter(r.kind for r in records)
    return 'workspace audit: %d untracked -- %s' % (len(records), ', '.join('%s %d' % (k, c[k]) for k in KINDS if c[k]))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--min-age', type=float, default=2, help='days; newer files are "active" (default 2)')
    ap.add_argument('--near', type=float, default=0.9, help='line coverage for near-copy (default 0.9)')
    ap.add_argument('--list', default='unbacked', help='kinds to list file by file (comma-separated, or "none")')
    ap.add_argument('--json', help='write every record here')
    ap.add_argument('--quiet', action='store_true', help='summary plus the unbacked count by directory')
    a = ap.parse_args(argv)
    ws = workspace()
    idx = Index.build(find_repos(), backed=github, cache_dir=CACHE)
    recs = audit(ws, idx, a.min_age, a.near)
    print(summary(recs) + ' (index: %d GitHub repos)' % len(idx.repos))
    if a.json:
        json.dump([r.__dict__ for r in recs], open(a.json, 'w'), indent=0)
    unb = [r for r in recs if r.kind == 'unbacked']
    if a.quiet:
        if unb:
            by = Counter('/'.join(r.path.split('/')[:2]) if r.path.count('/') > 1 else os.path.dirname(r.path) or '.'
                         for r in unb)
            print('  unbacked by directory: ' + ', '.join('%s %d' % kv for kv in by.most_common(8)))
            print('  run scripts/workspace_audit.py for the file list before deleting anything there')
        return
    kinds = [] if a.list == 'none' else a.list.split(',')
    for r in sorted((r for r in recs if r.kind in kinds), key=lambda r: (r.kind, r.path)):
        cov = '' if r.coverage is None else ' %3d%%' % round(100 * r.coverage)
        print('%-10s %s %7d%s  %s' % (r.kind, time.strftime('%Y-%m-%d', time.localtime(r.mtime)), r.size, cov, r.path))


if __name__ == '__main__':
    main()
