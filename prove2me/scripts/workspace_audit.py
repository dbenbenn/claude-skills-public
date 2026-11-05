#!/usr/bin/env python3
"""Which untracked files in the prove2me workspace exist nowhere we keep work.

usage: workspace_audit.py [--min-age DAYS] [--near FRACTION] [--list KINDS] [--json PATH] [--quiet]
                          [--include-oai]
       workspace_audit.py --folder NAME [--folder NAME ...]

Before calling any prover Part lost, run:  workspace_audit.py --folder <FOLDER>
(FOLDER as in `import Solutions.<FOLDER>.Blueprint`). It takes about a second: no git index, no
Lean; it lists every .lean file under Solutions/<FOLDER>/ (tracked or not, any age) as `copy`, with
the path of a byte-identical file under some mission repo's proofs/, or `no-copy`. A `no-copy`
file may be the only copy of finished work: read it before re-proving anything (q157, 2026-11-03:
a sorry-free Solutions/JM31/PartC.lean was declared lost after a look at jm-mission/proofs/ only).

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

A second report, "no copy under a mission repo's proofs/", takes every .lean file under each
Solutions/<FOLDER>/ (ports excluded unless --include-oai: Solutions/OAI* and any folder holding a
carve's CARVE_OWNER file, whose only source tree is the carve directory) and lists the ones with
no byte-identical file in a proofs/ directory, at any depth, of a git repo directly under ~/claude
(the mission repos and p2m-standalone; not the workspace itself). It reads working trees, so an uncommitted copy counts here: the question is where a copy
can be found, while `backed` above asks whether it is pushed. Files directly in Solutions/ are not
in a folder and are left to the first report. --quiet prints the count by folder.

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
from p2mlib.workspace import workspace, DRAFTS, CARVE_OWNER  # noqa: E402

CACHE = os.path.expanduser('~/.cache/p2m/workspace_audit')
MISSION_ROOT = '~/claude'
PRUNE = ('.lake', '.git', 'node_modules')   # never walked by the copies report
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
    return [e[3:] for e in out.split('\0') if e.startswith('?? ') and e[3:] not in TOOLING
            and os.path.basename(e[3:]) != CARVE_OWNER and not is_temp(e[3:])]


# Scratch files other workers' tools create and delete beside their output (assemble_blueprint,
# prune_solution); one vanished between listing and stat and crashed the audit (q167, 2026-11-04).
TEMP_PREFIXES = ('.assemble_', '.pruned_')


def is_temp(path):
    return os.path.basename(path).startswith(TEMP_PREFIXES)


def audit(ws, idx, min_age_days=2, near=0.9, now=None):
    now = now or time.time()
    # another worker may delete a listed file at any moment: drop what is gone before hashing, and
    # skip what vanishes after
    paths = [p for p in untracked(ws) if os.path.exists(os.path.join(ws, p))]
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
        try:
            st = os.stat(full)
        except FileNotFoundError:
            continue
        rec = Record(path, '', st.st_size, st.st_mtime)
        top = path.split('/', 1)[0]
        if st.st_mtime > now - min_age_days * 86400:
            rec.kind = 'active'
        elif h in idx.blobs:
            rec.kind = 'backed'
        elif top in ('Theorems', 'Definitions') and path.endswith('.lean'):
            rec.kind = 'draft-stub' if path[:-5].replace('/', '.') in drafts else 'mirror'
        elif path.endswith('.lean'):
            try:
                keys = line_keys(open(full, encoding='utf-8', errors='replace').read())
            except FileNotFoundError:
                continue
            rec.coverage = len(keys & idx.lines) / len(keys) if keys else 0.0
            rec.kind = 'near-copy' if keys and rec.coverage >= near else 'unbacked'
        else:
            rec.kind = 'unbacked'
        out.append(rec)
    return out


def mission_repos(root=None, exclude=()):
    """Git repos directly under root (default MISSION_ROOT), minus the excluded paths (the workspace)."""
    root = os.path.expanduser(root or MISSION_ROOT)
    skip = {os.path.realpath(e) for e in exclude}
    out = []
    for name in sorted(os.listdir(root)):
        d = os.path.join(root, name)
        if os.path.isdir(d) and os.path.exists(os.path.join(d, '.git')) and os.path.realpath(d) not in skip:
            out.append(d)
    return out


def lean_files(top):
    """Every .lean file under top, not descending into PRUNE directories."""
    for d, subdirs, files in os.walk(top):
        subdirs[:] = sorted(s for s in subdirs if s not in PRUNE)
        for f in sorted(files):
            if f.endswith('.lean'):
                yield os.path.join(d, f)


def digest(path):
    with open(path, 'rb') as f:
        return hashlib.sha1(f.read()).hexdigest()


@dataclass
class Copy:
    path: str          # relative to the workspace
    size: int
    mtime: float
    copy: str = None   # absolute path of a byte-identical file under some repo's proofs/, else None


def solution_folders(ws, folders=None, include_oai=False):
    """The Solutions/<FOLDER> names to check: the given ones (checked to exist), else every folder.
    Ports (Solutions/OAI*, and any folder a carve owns through CARVE_OWNER, e.g. Q146_CD) are left
    out unless include_oai: their source tree is the carve directory, never a proofs/."""
    sol = os.path.join(ws, 'Solutions')
    if folders:
        names = [f.strip('/')[len('Solutions/'):] if f.strip('/').startswith('Solutions/') else f.strip('/')
                 for f in folders]
        missing = [n for n in names if not os.path.isdir(os.path.join(sol, n))]
        if missing:
            raise SystemExit('no such workspace folder: ' + ', '.join('Solutions/' + n for n in missing))
        return names
    return [n for n in sorted(os.listdir(sol)) if os.path.isdir(os.path.join(sol, n))
            and n not in PRUNE and (include_oai or not (n.startswith('OAI')
                                                         or os.path.exists(os.path.join(sol, n, CARVE_OWNER))))]


def folder_copies(ws, repos, folders=None, include_oai=False):
    """A Copy for every .lean file under the chosen Solutions/<FOLDER>s. Repo files are hashed only
    when their size matches a workspace file's, so one folder costs a directory walk, not a read of
    every proof."""
    out = []
    for name in solution_folders(ws, folders, include_oai):
        for full in lean_files(os.path.join(ws, 'Solutions', name)):
            if is_temp(full):
                continue
            try:
                st = os.stat(full)
            except FileNotFoundError:
                continue
            out.append(Copy(os.path.relpath(full, ws), st.st_size, st.st_mtime))
    sizes = {c.size for c in out}
    found = {}
    for repo in repos:
        for d, subdirs, files in os.walk(repo):
            subdirs[:] = sorted(s for s in subdirs if s not in PRUNE)
            if 'proofs' not in os.path.relpath(d, repo).split(os.sep):
                continue
            for f in sorted(files):
                p = os.path.join(d, f)
                if f.endswith('.lean') and os.path.getsize(p) in sizes:
                    found.setdefault(digest(p), p)
    kept = []
    for c in out:
        try:
            c.copy = found.get(digest(os.path.join(ws, c.path)))
        except FileNotFoundError:
            continue
        kept.append(c)
    return kept


def copies_report(copies, verbose=False):
    """Lines for the no-copy report; verbose (the --folder form) also lists the copies and where they are."""
    lines = []
    for c in sorted(copies, key=lambda c: c.copy is not None):     # no-copy first, otherwise in walk order
        day = time.strftime('%Y-%m-%d', time.localtime(c.mtime))
        if c.copy is None:
            lines.append('no-copy %s %7d  %s' % (day, c.size, c.path))
        elif verbose:
            lines.append('copy    %s %7d  %s = %s' % (day, c.size, c.path, c.copy))
    return lines


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
    ap.add_argument('--folder', action='append', metavar='NAME',
                    help='only the copies report, for Solutions/NAME (repeatable); fast: no git index')
    ap.add_argument('--include-oai', action='store_true',
                    help='copies report: also the port folders (Solutions/OAI*, carve-owned ones)')
    a = ap.parse_args(argv)
    ws = workspace()
    repos = mission_repos(exclude=(ws,))
    if a.folder:
        cs = folder_copies(ws, repos, folders=a.folder)
        for name in solution_folders(ws, a.folder):
            mine = [c for c in cs if c.path.startswith('Solutions/%s/' % name)]
            print('Solutions/%s: %d .lean files, %d with no copy under a mission repo\'s proofs/ (%d repos searched)'
                  % (name, len(mine), sum(c.copy is None for c in mine), len(repos)))
            for line in copies_report(mine, verbose=True):
                print('  ' + line)
        return
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
    nocopy = [c for c in folder_copies(ws, repos, include_oai=a.include_oai) if c.copy is None]
    if a.quiet:
        if nocopy:
            by = Counter(c.path.split('/')[1] for c in nocopy)
            print('  no copy under a mission repo\'s proofs/: %d .lean files in %d Solutions folders (%s)'
                  % (len(nocopy), len(by), ', '.join('%s %d' % kv for kv in by.most_common(8))))
            print('  run scripts/workspace_audit.py --folder NAME before calling any work there lost')
        return
    kinds = [] if a.list == 'none' else a.list.split(',')
    for r in sorted((r for r in recs if r.kind in kinds), key=lambda r: (r.kind, r.path)):
        cov = '' if r.coverage is None else ' %3d%%' % round(100 * r.coverage)
        print('%-10s %s %7d%s  %s' % (r.kind, time.strftime('%Y-%m-%d', time.localtime(r.mtime)), r.size, cov, r.path))
    print('no copy under a mission repo\'s proofs/ (%d repos searched%s): %d .lean files'
          % (len(repos), '' if a.include_oai else '; OAI and carve port folders excluded', len(nocopy)))
    for line in copies_report(nocopy):
        print(line)


if __name__ == '__main__':
    main()
