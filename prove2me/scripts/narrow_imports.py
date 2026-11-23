#!/usr/bin/env python3
"""Narrow each statement's `import Mathlib` to the Mathlib modules the statement uses, before it publishes.

usage: narrow_imports.py DIR [--write] [--only=NAME[,NAME...]]

DIR is a mission or a p2m-standalone folder (its mission.py payloads(): statements/, lib/Thm_*.lean, or
draft.extract_payloads). For every statement whose preamble has a bare `import Mathlib`, Mathlib's
`#min_imports in` proposes the modules, and the narrowed statement is accepted only if it compiles and
elaborates to the same `pp.all` term as with all of Mathlib (p2mlib.narrow). Each is printed as
`NAME: import Mathlib -> <modules>` (or `no Mathlib needed`), or `NAME: KEEP <why>`.

--write records the result:
- a statement in its own file (statements/Thm_*.lean, lib/Thm_<name>.lean): the `import Mathlib` line in
  that file is replaced by the modules (or deleted);
- otherwise (draft.extract_payloads' one file of statements): DIR/imports.json {name: [modules]}, which
  extract_payloads reads.

Why: a published preamble is frozen, and every proof that imports the statement pays for its imports.
`import Mathlib` alone peaks at ~6.4 GB of the verifier's 7150 MiB; the x25519-dalek contracts needed
no Mathlib at all, yet their reductions were split for memory because of that line (2026-11-23).
draft.py verify flags a Draft statement that still imports all of Mathlib, and publish_standalone.py
refuses one; mission.py WHOLE_MATHLIB {name: reason} keeps one on purpose.

Each probe compiles in the prove2me workspace through lean-cap (one at a time; a few seconds each once
Mathlib is in the page cache). The bundles and sibling statements a preamble imports must be built.
"""
import json
import os
import re
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.dirname(HERE)]
from p2mlib import narrow as N  # noqa: E402
from p2mlib.workspace import workspace  # noqa: E402


def lean_in(ws):
    from try_module import compile_
    def lean(text):
        fd, path = tempfile.mkstemp(prefix='.narrow_', suffix='.lean', dir=ws)
        try:
            with os.fdopen(fd, 'w', encoding='utf-8') as f:
                f.write(text)
            return compile_(path, ws)
        finally:
            os.remove(path)
    return lean


def own_file(mdir, name):
    """The statement file holding only `name`, with a bare `import Mathlib` line, if there is one."""
    for sub in ('statements', 'lib'):
        d = os.path.join(mdir, sub)
        if not os.path.isdir(d):
            continue
        for f in sorted(os.listdir(d)):
            if not (f.startswith('Thm_') and f.endswith('.lean')):
                continue
            text = open(os.path.join(d, f), encoding='utf-8').read()
            decls = re.findall(r'^theorem\s+(\S+)', text, re.M)
            if len(decls) == 1 and decls[0].rsplit('.', 1)[-1] == name and N.whole_mathlib(text):
                return os.path.join(d, f)
    return None


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    if len(args) != 1:
        sys.exit(__doc__)
    mdir = os.path.abspath(args[0])
    only = {n for a in sys.argv[1:] if a.startswith('--only=') for n in a[len('--only='):].split(',') if n}
    write = '--write' in sys.argv[1:]
    from p2mlib.mission import load
    M = load(mdir)
    todo = [(k, pre, fs) for k, (pre, fs) in sorted(M.payloads().items())
            if N.whole_mathlib(pre) and (not only or k in only)]
    if not todo:
        print('no statement imports all of Mathlib')
        return
    lean = lean_in(workspace())
    nj = os.path.join(mdir, 'imports.json')
    record = json.load(open(nj, encoding='utf-8')) if os.path.exists(nj) else {}
    kept = 0
    for k, pre, fs in todo:
        try:
            new = N.narrow(pre, fs, lean)
        except N.NarrowError as e:
            kept += 1
            print('%s: KEEP %s' % (k, e))
            continue
        mods = [l.split()[1] for l in new.split('\n')
                if l.startswith('import ') and l.split()[1].split('.')[0] in N.ROOTS
                and l not in pre.split('\n')]
        print('%s: import Mathlib -> %s' % (k, ', '.join(mods) or 'no Mathlib needed'))
        if write:
            f = own_file(mdir, k)
            if f:
                N.rewrite_file(f, new)
                print('   wrote ' + os.path.relpath(f, mdir))
            else:
                record[k] = mods
                json.dump(record, open(nj, 'w', encoding='utf-8'), indent=1, sort_keys=True)
                print('   recorded in imports.json')
    print('%d narrowed, %d kept%s' % (len(todo) - kept, kept, '' if write else ' (dry run: --write to record)'))


if __name__ == '__main__':
    main()
