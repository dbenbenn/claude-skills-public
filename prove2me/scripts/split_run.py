#!/usr/bin/env python3
"""Publish a carved split in waves (p2mlib.splitrun). A dry run unless --go.

usage: split_run.py RUN.json [--go] [--reset ITEM ...] [--max-hours H]

RUN.json: {"plan", "out", "prose", "explanations", "state", "log", "source", "tags", "jobs"}
(paths may start with ~). Without --go it prints what would be sent first and what is blocked,
and touches neither the platform nor the state file."""
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
        elif a != '--go':
            rest.append(a)
            i += 1
        else:
            i += 1
    cfg = load(rest[0])
    if not go:
        class NoApi:
            def __getattr__(self, k):
                raise RuntimeError('dry run: no platform access')
        d = R.Runner(cfg, NoApi()).dry_run()
        print('DRY RUN (add --go to publish): %d items, %d live' % (d['items'], d['live']))
        print('would send now (%d): %s' % (len(d['ready']), ' '.join(d['ready'][:40])))
        for x, why in sorted(d['blocked'].items()):
            print('blocked %s: %s' % (x, why))
        return d
    r = R.Runner(cfg, R.LiveApi())
    for x in resets:
        r.reset(x)
    s = r.run(max_hours=hours)
    print(json.dumps(s, indent=1))
    return s


if __name__ == '__main__':
    main()
