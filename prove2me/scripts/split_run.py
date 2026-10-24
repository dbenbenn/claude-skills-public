#!/usr/bin/env python3
"""Publish a carved split in waves (p2mlib.splitrun). A dry run unless --go.

usage: split_run.py RUN.json [--go] [--reset ITEM ...] [--max-hours H] [--offline]

RUN.json: {"plan", "out", "prose", "explanations", "state", "log", "source", "tags", "jobs"}
(paths may start with ~). Without --go it looks the plan's bundles and statements up on the
platform (reads only) and prints what a run would adopt as already live, any live name whose text
differs from ours (a run refuses to post anything then), what it would send first and what is
blocked; it writes neither the platform nor the state file. --offline skips the lookups."""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from p2mlib import splitrun as R


def load(path):
    cfg = json.load(open(path, encoding='utf-8'))
    for k in ('plan', 'out', 'prose', 'explanations', 'state', 'log'):
        cfg[k] = os.path.expanduser(cfg[k])
    return cfg


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    go = '--go' in argv
    resets, hours, rest = [], None, []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == '--reset':
            resets.append(argv[i + 1])
            i += 2
        elif a == '--max-hours':
            hours = float(argv[i + 1])
            i += 2
        elif a not in ('--go', '--offline'):
            rest.append(a)
            i += 1
        else:
            i += 1
    cfg = load(rest[0])
    if not go:
        offline = '--offline' in argv
        d = R.Runner(cfg, None if offline else R.ReadOnly(R.LiveApi())).dry_run(read=not offline)
        print('DRY RUN (add --go to publish): %d items, %d live' % (d['items'], d['live']))
        if d['adopt']:
            print('would adopt (%d): %s' % (len(d['adopt']), ', '.join(
                '%s %s' % (x, i) for x, i in sorted(d['adopt'].items()))))
        for x, rows in sorted(d['proved_elsewhere'].items()):
            print('already proved by another live proof (a run stops it for a person): %s: %s' % (x, ', '.join(rows)))
        if d['mismatch']:
            print('REFUSES TO RUN: ' + R.mismatch_message(d['mismatch']))
        print('would send now (%d): %s' % (len(d['ready']), ' '.join(d['ready'][:40])))
        for x, why in sorted(d['blocked'].items()):
            print('blocked %s: %s' % (x, why))
        return d
    r = R.Runner(cfg, R.LiveApi())
    for x in resets:
        r.reset(x)
    try:
        s = r.run(max_hours=hours)
    except R.LiveMismatch as e:
        sys.exit(str(e))
    print(json.dumps(s, indent=1))
    return s


if __name__ == '__main__':
    main()
