"""Apply the 'restore' lists of work/false_edges.json: each false import is replaced by the imports
it stood in for, by editing the generated files (run it on out/lib and stage/Definitions, never
after a `carve.py gen`, which regenerates them), then measure again.

Prefer `carve_measure.py --measure-flag=--drop-false-edges` (9d7c60a2): it does the bundle-for-bundle
swap itself, as a recorded repair cut that survives `gen`. This tool remains for what that flag
leaves to a person: a false STATEMENT import whose restore list names bundles (check that the
file needs only the bundle, then swap)."""
import json
import os
import sys


def apply(false_edges_path, dirs):
    n = 0
    for e in json.load(open(false_edges_path)).get('false_edges', []):
        if not e.get('restore') or not e.get('file'):
            continue
        for d in dirs:
            p = os.path.join(d, e['file'])
            if not os.path.exists(p):
                continue
            lines = open(p).read().split('\n')
            bad = 'import ' + e['import']
            if bad not in lines:
                continue
            i = lines.index(bad)
            have = set(lines)
            new = ['import ' + m for m in e['restore'] if 'import ' + m not in have]
            lines[i:i + 1] = new
            open(p, 'w').write('\n'.join(lines))
            n += 1
    return n


if __name__ == '__main__':
    if len(sys.argv) < 3:
        sys.exit('usage: restore_edges.py WORK/false_edges.json DIR [DIR ...]')
    print('swapped', apply(sys.argv[1], sys.argv[2:]), 'imports')
