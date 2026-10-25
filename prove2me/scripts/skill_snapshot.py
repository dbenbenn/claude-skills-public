#!/usr/bin/env python3
"""Materialise the skill at a commit as a read-only snapshot and print its path.

usage: skill_snapshot.py [--rev REV] [--allow-dirty] [--repo DIR] [--cache DIR] [--prune DAYS]

Default: HEAD of ~/.claude/skills into ~/.cache/p2m/skill/<sha>/ (git archive, read-only, reused if
present). A dirty skills tree is refused unless --allow-dirty, which snapshots the working tree
under <sha>-dirty-<content hash>. --prune DAYS first removes snapshots unused for DAYS days. Run a
long job from the printed path (scripts/carve_pipeline.py does this itself), so a skill edit or push
mid-run cannot mix old and new code in one run (p2mlib.snapshot)."""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from p2mlib import snapshot


def main(argv=None):
    ap = argparse.ArgumentParser(usage='skill_snapshot.py [--rev REV] [--allow-dirty] [--repo DIR] [--cache DIR] [--prune DAYS]')
    ap.add_argument('--rev')
    ap.add_argument('--allow-dirty', action='store_true')
    ap.add_argument('--repo')
    ap.add_argument('--cache')
    ap.add_argument('--prune', type=float, metavar='DAYS')
    a = ap.parse_args(argv)
    if a.prune is not None:
        for p in snapshot.prune(a.cache, a.prune):
            print('pruned', p, file=sys.stderr)
    try:
        print(snapshot.snapshot(a.repo, a.rev, a.cache, a.allow_dirty))
    except snapshot.DirtyTree as e:
        sys.exit(str(e))


if __name__ == '__main__':
    main()
