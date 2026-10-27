"""Apply the 'restore' lists of work/false_edges.json: each false bundle import is replaced by the
imports it stood in for. carve_measure's --drop-false-edges only cuts imports that need no
replacement; this does the swap in the generated files (run it on out/lib and stage/Definitions,
never after a `carve.py gen`, which regenerates them), then measure again."""
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
