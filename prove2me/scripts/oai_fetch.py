#!/usr/bin/env python3
"""Fetch an openai/math module's OAI.* import closure at a commit, into DEST/lean/... (files already
there are reused). Only the closure: never copy a whole tree into DEST (oaiq-038/040: a 1.4 GB
`lean/OAI` under src made the port step port all 121,736 OpenAI modules).

usage: oai_fetch.py DEST ROOT_MODULE [--commit SHA] [--git REPO | --no-git] [--foreign DIR ...] [EXTRA_PATH ...]
  EXTRA_PATH is relative to lean/. Default commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a (the
  release the published OAI goals were generated from).
  --git REPO  a local clone of openai/math (default: $P2M_OAI_GIT, else ~/claude/openai-math); each
              file is read from it at the commit (`git cat-file`; a partial clone fetches a missing
              blob over git itself). Only what the clone cannot give comes from
              raw.githubusercontent.com, which answers HTTP 429 when many agents fetch at once
              (eleven worker lessons, oaiq-032..049): those reads back off, honouring Retry-After,
              for up to about 20 minutes per file.
  --no-git    network only.
  --foreign DIR  (repeatable) a local checkout of a foreign package, at the commit openai/math pins
              (lean/lakefile, lake-manifest): DIR/<Root>/ or DIR/<Root>.lean. The foreign modules the
              closure imports and their import closure inside the checkout's roots are copied into
              DEST/lean verbatim (the port makes module-system files plain: oaiport.demodule); a file
              already there is kept. A module the checkout lacks is named, not fatal (oaiq-093: OpenAI's
              GromovGrowthBridge imports a Gromov.PolynomialGrowth absent at the pin: patch the import).
              LeanArchitect annotations are not stripped: an `import Architect` shows as a missing root.

Prints how many files came from DEST already, from the clone and from the network. Exits 1 when the
closure imports a package that is neither OpenAI's nor in our toolchain (PrimeNumberTheoremAnd,
StrongPNT: oaiq-083) and DEST/lean lacks it: put its sources beside OAI/ (references/openai-ports.md,
"Foreign packages") and run again; the port takes them as OpenAI's."""
import collections
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

COMMIT = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
CANDIDATES = ('~/claude/openai-math',)
RAW_TRIES = 9          # waits 15, 30, 60, ... capped at 300 s: about 20 minutes in all


def default_git_repo():
    for p in [os.environ.get('P2M_OAI_GIT')] + list(CANDIDATES):
        if p and os.path.isdir(os.path.join(os.path.expanduser(p), '.git')):
            return os.path.expanduser(p)
    return None


class GitSource:
    """Files of one commit of a local clone, through one `git cat-file --batch` process."""

    def __init__(self, repo, commit):
        self.commit = commit
        self.p = subprocess.Popen(['git', '-C', repo, 'cat-file', '--batch'], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE)

    def get(self, rel):
        self.p.stdin.write(('%s:lean/%s\n' % (self.commit, rel)).encode())
        self.p.stdin.flush()
        head = self.p.stdout.readline().decode().split()
        if len(head) != 3 or head[1] != 'blob':
            return None                      # "<rev> missing" (or not a file)
        data = self.p.stdout.read(int(head[2]))
        self.p.stdout.read(1)                # the newline after the object
        return data.decode('utf-8')

    def close(self):
        self.p.stdin.close()
        self.p.wait()


def raw_get(commit, rel):
    url = 'https://raw.githubusercontent.com/openai/math/%s/lean/%s' % (commit, rel)
    wait = 15
    for i in range(RAW_TRIES):
        after = None
        try:
            with urllib.request.urlopen(url, timeout=60) as r:
                return r.read().decode('utf-8')
        except urllib.error.HTTPError as e:
            if e.code == 404:
                raise SystemExit('fetch failed %s: 404 (not at this commit)' % url)
            err = e.code
            after = e.headers.get('Retry-After') if e.headers else None
        except Exception as e:  # noqa: BLE001  (DNS, timeouts, resets)
            err = e
        if i == RAW_TRIES - 1:
            raise SystemExit('fetch failed %s after %d tries: %s' % (url, RAW_TRIES, err))
        time.sleep(max(wait, int(after)) if after and str(after).isdigit() else wait)
        wait = min(wait * 2, 300)


# import roots our Mathlib workspace provides; any other non-OpenAI root is a foreign package
TOOLCHAIN = {'Mathlib', 'Batteries', 'Aesop', 'Std', 'Lean', 'Init', 'Lake', 'Qq', 'Plausible', 'ProofWidgets',
             'ImportGraph', 'LeanSearchClient'}
OPENAI = ('OAI', 'ComparatorChallenges')


def missing_packages(foreign, dest):
    """{root: importing modules} of the foreign roots with neither DEST/lean/ROOT/ nor ROOT.lean."""
    lean = os.path.join(dest, 'lean')
    return {k: v for k, v in sorted(foreign.items())
            if not os.path.isdir(os.path.join(lean, k)) and not os.path.exists(os.path.join(lean, k + '.lean'))}


def fetch(dest, root, commit=COMMIT, extra=(), git_repo='default', foreign=None, foreign_mods=None):
    """Fetch root's closure into dest; returns (modules, bytes, {source: files}). `foreign`, a dict,
    collects {import root: [modules importing it]} for roots neither OpenAI's nor in TOOLCHAIN;
    `foreign_mods`, a dict, likewise {imported module: [modules importing it]}."""
    if git_repo == 'default':
        git_repo = default_git_repo()
    gs = GitSource(git_repo, commit) if git_repo else None
    src = collections.Counter()

    def get(rel):
        p = os.path.join(dest, 'lean', rel)
        if os.path.exists(p):
            src['local'] += 1
            return open(p, encoding='utf-8').read()
        t = gs.get(rel) if gs else None
        if t is not None:
            src['git'] += 1
        else:
            t = raw_get(commit, rel)
            src['network'] += 1
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'w', encoding='utf-8') as f:
            f.write(t)
        return t
    try:
        seen, todo, total = set(), [root], 0
        while todo:
            m = todo.pop()
            if m in seen:
                continue
            seen.add(m)
            t = get(m.replace('.', '/') + '.lean')
            total += len(t.encode())
            for imp in re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)', t, re.M):
                top = imp.split('.')[0]
                if top in OPENAI:
                    todo.append(imp)
                elif top not in TOOLCHAIN:
                    if foreign is not None:
                        foreign.setdefault(top, []).append(m)
                    if foreign_mods is not None:
                        foreign_mods.setdefault(imp, []).append(m)
        for rel in extra:
            get(rel)
    finally:
        if gs:
            gs.close()
    return len(seen), total, dict(src)


IMPORT = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)', re.M)


def copy_foreign(dest, mods, dirs):
    """Copy the foreign modules `mods` ({module: [importers]}) and their import closure inside the roots
    the checkouts `dirs` hold into DEST/lean, verbatim; files already there are kept (prep_rk.py oaiq-091,
    prep_gromov.py oaiq-093). Returns ({dir: files copied}, {root: [importers]} of roots no checkout
    holds, {module: [importers]} a holding checkout lacks)."""
    def holder(root):
        for d in dirs:
            if os.path.isdir(os.path.join(d, root)) or os.path.exists(os.path.join(d, root + '.lean')):
                return d
        return None
    copied, unheld, absent = collections.Counter(), {}, {}
    todo = [(m, imp) for m, imps in sorted(mods.items()) for imp in imps]
    seen = set()
    while todo:
        m, by = todo.pop()
        top = m.split('.')[0]
        if top in TOOLCHAIN or top in OPENAI:
            continue
        d = holder(top)
        if d is None:
            unheld.setdefault(top, []).append(by)
            continue
        if m in seen:
            continue
        seen.add(m)
        rel = os.path.join(*m.split('.')) + '.lean'
        dst = os.path.join(dest, 'lean', rel)
        if os.path.exists(dst):
            t = open(dst, encoding='utf-8').read()
        elif os.path.exists(os.path.join(d, rel)):
            t = open(os.path.join(d, rel), encoding='utf-8').read()
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            with open(dst, 'w', encoding='utf-8') as f:
                f.write(t)
            copied[d] += 1
        else:
            absent.setdefault(m, []).append(by)
            continue
        todo += [(i, m) for i in IMPORT.findall(t)]
    return dict(copied), unheld, absent


def main(argv):
    args = [a for a in argv]
    commit, repo = COMMIT, 'default'
    if '--commit' in args:
        i = args.index('--commit')
        commit = args[i + 1]
        del args[i:i + 2]
    if '--git' in args:
        i = args.index('--git')
        repo = os.path.expanduser(args[i + 1])
        del args[i:i + 2]
    dirs = []
    while '--foreign' in args:
        i = args.index('--foreign')
        dirs.append(os.path.abspath(os.path.expanduser(args[i + 1])))
        del args[i:i + 2]
    if '--no-git' in args:
        args.remove('--no-git')
        repo = None
    if len(args) < 2:
        sys.exit(__doc__)
    foreign, foreign_mods = {}, {}
    n, total, src = fetch(args[0], args[1], commit, args[2:], repo, foreign, foreign_mods)
    print('%d modules, %d bytes (%s)' % (n, total, ', '.join('%d %s' % (v, k) for k, v in sorted(src.items())) or 'none'))
    if dirs:
        copied, unheld, absent = copy_foreign(args[0], foreign_mods, dirs)
        for d in dirs:
            print('%d foreign modules from %s' % (copied.get(d, 0), d))
        for m, by in sorted(absent.items()):
            print('not in its checkout: %s (imported by %s): patch the import away' % (m, ', '.join(sorted(set(by)))))
        for k, v in unheld.items():
            foreign.setdefault(k, []).extend(v)

    missing = missing_packages(foreign, args[0])
    if missing:
        sys.exit('foreign packages in the closure, not in %s: %s. openai/math does not contain them: put their '
                 'sources beside OAI/ there (the pinned upstream from its lake-manifest, LeanArchitect annotations '
                 'stripped; references/openai-ports.md "Foreign packages") and run again (oaiq-083)'
                 % (os.path.join(args[0], 'lean'), '; '.join('%s (imported by %s)' % (k, ', '.join(sorted(set(v))[:5]))
                                                             for k, v in missing.items())))


if __name__ == '__main__':
    main(sys.argv[1:])
