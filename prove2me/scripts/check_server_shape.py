#!/usr/bin/env python3
"""Compile every statement of a mission in server shape: its preamble + formal_statement, alone.

usage: check_server_shape.py MISSION_DIR [NAME ...]

The platform elaborates each statement by itself, after its own computed imports. A statements
file compiled as a whole hides two kinds of failure: an `open X` at the top of the file that the
extracted statement does not carry (Lodha–Moore, 2026-10-01: bare `op`/`unop` from `open
MulOpposite` failed in three statements, caught only by a read-back auditor), and an import that
the file has but the computed preamble lacks. Files go to $P2M_WORKSPACE/Solutions/_srv/<mission>/.
Generalized from moore-mission/scripts/check_server_shape.py.
"""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import draft  # noqa: E402
from prune_solution import _workspace  # noqa: E402


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    mdir = os.path.abspath(sys.argv[1])
    names = sys.argv[2:]
    M = draft.load(mdir)
    ws = _workspace()
    out = os.path.join(ws, 'Solutions', '_srv', os.path.basename(mdir))
    os.makedirs(out, exist_ok=True)
    items = sorted((n, p) for n, p in M.payloads().items() if not names or n in names)

    def check(item):
        name, (pre, st) = item
        path = os.path.join(out, name + '.lean')
        open(path, 'w', encoding='utf-8').write(pre + '\n\n' + st + '\n')
        p = subprocess.run(['lake', 'env', 'lean', path], cwd=ws, capture_output=True, text=True, timeout=1200)
        return name, [l for l in (p.stdout + p.stderr).splitlines() if 'error' in l]

    bad = 0
    with ThreadPoolExecutor(6) as ex:
        for name, errs in ex.map(check, items):
            print(('OK   ' if not errs else 'FAIL ') + name, flush=True)
            for e in errs[:3]:
                print('     ', e)
            bad += bool(errs)
    print('FAILED', bad)
    sys.exit(bad != 0)


if __name__ == '__main__':
    main()
