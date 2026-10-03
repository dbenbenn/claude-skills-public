#!/usr/bin/env python3
"""Install a mission's draft statements in the workspace as the modules the platform will publish.

usage: stubs.py MISSION_DIR [--check] [--no-build]

Each statement of mission.py becomes Theorems/Thm_<NS>_<name>.lean in the workspace: its preamble
and formal_statement with proof `sorry`, byte for byte the module the platform publishes at Submit
(one writer, p2mlib.workspace.statement_text, shared with fetch_theorems.py). A milestone's proof
can then `import Theorems.Thm_<NS>_<sibling>` from the start, exactly as its submission will: the
dependency edges are written, not recovered by rewire.py from copies afterwards. A proof that
imports an unproved sibling is a reduction, as on the platform; the development is complete when
every milestone's proof compiles and every sibling it imports has one too.

The stubs are listed in Theorems/.drafts.json. published() ignores them (a submission importing a
statement the platform does not have yet fails), and fetch_theorems.py retires each one when the
platform publishes it, reporting any difference. The stub of a milestone renamed or dropped from
mission.py is removed. A name already published is never overwritten: it is compared, and a
difference reported, since a published statement is immutable.

Run it whenever a statement changes, before compiling proofs against it; `draft.py upload --go`
runs it and `draft.py verify` checks it. --check reports missing or stale stubs and writes nothing.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))  # p2mlib
from p2mlib.mission import load  # noqa: E402
from p2mlib.workspace import workspace, statement_module, statement_text, drafts, update_drafts  # noqa: E402


def wanted(mdir):
    """{module: (path relative to the workspace, text)} for the mission's statements."""
    M = load(mdir)
    pay = M.payloads()
    out = {}
    for T in M.THEOREMS:
        mod, rel = statement_module(T.get('namespace', M.NAMESPACE) + '.' + T['name'])
        out[mod] = (rel, statement_text(*pay[T['name']]))
    return out


def sync(mdir, ws=None, check=False):
    """(problems, written modules). Writes and records the stubs unless `check`."""
    ws = ws or workspace()
    mdir = os.path.abspath(mdir)
    want, dr = wanted(mdir), drafts(ws)
    problems, written, removed = [], [], []
    for mod, (rel, text) in sorted(want.items()):
        p = os.path.join(ws, rel)
        cur = open(p, encoding='utf-8').read() if os.path.exists(p) else None
        if cur is not None and mod not in dr:
            if cur.rstrip() != text.rstrip():
                problems.append('PUBLISHED-DIFFERS %s: the platform has another statement under this name' % mod)
            continue
        if cur is not None and dr[mod] != mdir:
            problems.append('OTHER-DRAFT %s is a stub of %s' % (mod, dr[mod]))
            continue
        if cur == text:
            continue
        if check:
            problems.append('%s %s' % ('MISSING' if cur is None else 'STALE', mod))
            continue
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'w', encoding='utf-8').write(text)
        dr[mod] = mdir
        written.append(mod)
    for mod in sorted(m for m, d in dr.items() if d == mdir and m not in want):
        if check:
            problems.append('LEFTOVER %s: no longer a statement of the mission' % mod)
            continue
        p = os.path.join(ws, *mod.split('.')) + '.lean'
        if os.path.exists(p):
            os.remove(p)
        del dr[mod]
        removed.append(mod)
        print('   removed the stub of %s (no longer a statement)' % mod)
    if not check and (written or removed):
        update_drafts(add={m: mdir for m in written}, remove=removed, ws=ws)
    return problems, written


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    if len(args) != 1:
        sys.exit(__doc__)
    check, ws = '--check' in sys.argv, workspace()
    problems, written = sync(args[0], ws, check)
    for p in problems:
        print('   ' + p)
    print('%d stub(s) written; %d problem(s)' % (len(written), len(problems)))
    if written and '--no-build' not in sys.argv:
        r = subprocess.run(['lake', 'build'] + written, cwd=ws, capture_output=True, text=True)
        print('build:', 'ok' if r.returncode == 0 else 'FAILED')
        for l in [l for l in (r.stdout + r.stderr).split('\n') if 'error' in l.lower()][:8]:
            print('   ' + l[:200])
        if r.returncode:
            sys.exit(1)
    sys.exit(1 if problems else 0)


if __name__ == '__main__':
    main()
