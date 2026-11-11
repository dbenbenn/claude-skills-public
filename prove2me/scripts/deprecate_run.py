#!/usr/bin/env python3
"""Deprecate everything one carve run published: its live bundles and statements (PATCH /theorems/:id,
`deprecated` + `reason`; reversible with `deprecated: false`).

usage: deprecate_run.py RUN_STATE.json --reason FILE [--keep-id TID ...] [--go]     (dry run without --go)

RUN_STATE.json is a carve's publish/run_state.json (keys `bundle:*`, `statement:*`, `piece:*`). Only
`bundle:` and `statement:` entries in state `live` are retired; a piece's id is its statement's theorem,
so retiring the statement hides its proof too, and the goal (never a run's own statement) is untouched.
`--keep-id` names theorems that must survive: if any is among the run's items the whole run is refused.
The reason (a file, never an inline string) should say what replaced the items. Already-deprecated
items are skipped. Written for q238 (2026-11-11: 630 items built against the wrong definitions bundle);
the Erdős 3 v1 split had a one-off script for the same job.
"""
import argparse, json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import call


def run_items(state):
    """[(key, theorem id)] of the run's live bundles and statements, deduplicated by id."""
    out, seen = [], set()
    for k, v in sorted(state.items()):
        if k.split(':', 1)[0] in ('bundle', 'statement') and v.get('state') == 'live' and v.get('id'):
            if v['id'] not in seen:
                seen.add(v['id'])
                out.append((k, v['id']))
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('run_state')
    ap.add_argument('--reason', required=True)
    ap.add_argument('--keep-id', action='append', default=[])
    ap.add_argument('--go', action='store_true')
    a = ap.parse_args(argv)
    reason = open(a.reason).read().strip()
    if not reason:
        sys.exit('refusing: empty reason')
    items = run_items(json.load(open(a.run_state)))
    clash = [k for k, tid in items if tid in a.keep_id]
    if clash:
        sys.exit('refusing: kept theorem(s) among the run items: %s' % ', '.join(clash))
    print('%d live items (%d bundles); reason: %s' % (
        len(items), sum(k.startswith('bundle:') for k, _ in items), reason[:100]))
    done = skipped = 0
    failed = []
    for k, tid in items:
        t = call('GET', '/theorems/' + tid)
        if isinstance(t, dict) and t.get('__error'):
            failed.append((k, t['__error']))
            continue
        if t.get('theorem', t).get('deprecated_at'):
            skipped += 1
            continue
        if a.go:
            r = call('PATCH', '/theorems/' + tid, {'deprecated': True, 'reason': reason})
            if isinstance(r, dict) and r.get('__error'):
                failed.append((k, r['__error']))
                continue
            time.sleep(0.2)
        done += 1
    print('%s %d, already deprecated %d, failed %d' % ('deprecated' if a.go else 'would deprecate', done, skipped, len(failed)))
    for k, e in failed:
        print('FAILED', k, e)
    if not a.go:
        print('dry run -- pass --go to apply')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
