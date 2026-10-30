#!/usr/bin/env python3
"""Publish a carved split in waves (p2mlib.splitrun). A dry run unless --go.

usage: split_run.py RUN.json [--go] [--reset ITEM ...] [--max-hours H] [--offline]

RUN.json: {"plan", "out", "prose", "explanations", "state", "log", "source", "tags", "jobs"}
(paths may start with ~). Without --go it looks the plan's bundles and statements up on the
platform (reads only) and prints what a run would adopt as already live, any live name whose text
differs from ours (a run refuses to post anything then), what it would send first and what is
blocked; it writes neither the platform nor the state file. --offline skips the lookups. It exits 1
when any item still to send (in any wave) has a missing file or one that fails a check, listing them.

A piece whose theorem has someone else's live proof is refused (submit_verify's guard) and waits.
Read that proof, then write `comparisons/<slug>.md` beside `explanations/` (or RUN.json "comparisons"):
"Different from <id>: ..." sends ours with it as the reason on the next run; "Same as <id>: ..."
settles the item unsent (submit_all.py's convention; oaiq-068).

--go holds the carve's publish lock (one per publish/ directory, run.json and run_early.json alike): a
second publisher on the same run state exits 3 naming the first (carve_pipeline's overlap mode runs one
in the background while pieces are measured). RUN.json "release" gates the pieces (p2mlib.splitrun).

When RUN.json lies in a carve directory, --go keeps that carve's monitoring-page section current while no driver
runs on it (p2mlib.carvemonitor), so a background publisher that outlives its driver still shows its counts."""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from p2mlib import splitrun as R


def load(path):
    cfg = json.load(open(path, encoding='utf-8'))
    for k in ('plan', 'out', 'prose', 'explanations', 'state', 'log'):
        cfg[k] = os.path.expanduser(cfg[k])
    if cfg.get('release'):
        cfg['release'] = os.path.expanduser(cfg['release'])
    return cfg


def publisher_monitor(run_json):
    """When RUN.json lies in a carve: its monitoring-page section kept current while no driver runs
    (p2mlib.carvemonitor, role publisher: overlap mode's background publisher outlives a stopped driver).
    None otherwise or on any failure."""
    try:
        from p2mlib import carvemonitor
        return carvemonitor.publisher_reporter(run_json)
    except Exception:
        return None


def end_monitor(mon, state, why):
    try:
        if mon is not None:
            mon.finish(state, why)
    except Exception:
        pass


def main(argv=None):
    # line-buffered even when redirected to a file: a long --go run prints its progress as it goes
    # (oaiq-045 saw nothing until it exited)
    sys.stdout.reconfigure(line_buffering=True)
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
        if d.get('held'):
            print('%d pieces held until their release (RUN.json "release")' % d['held'])
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
        if d['unsendable']:
            # any wave, not only what would go now: a live run would block on each (oaiq-047)
            print('CANNOT BE SENT (%d; a live run would block on each; write or fix them first):' % len(d['unsendable']))
            for x, why in sorted(d['unsendable'].items()):
                print('  %s: %s' % (x, why))
            sys.exit(1)
        return d
    from p2mlib import runlock
    runlock.hold(runlock.dir_key('publish', os.path.abspath(rest[0])), 'split_run.py --go ' + rest[0])
    mon = publisher_monitor(rest[0])
    try:
        r = R.Runner(cfg, R.LiveApi())
        for x in resets:
            r.reset(x)
        try:
            s = r.run(max_hours=hours)
        except R.LiveMismatch as e:
            sys.exit(str(e))
    except BaseException as e:
        end_monitor(mon, 'failed', 'publisher stopped: %s' % (str(e).splitlines() or [type(e).__name__])[0][:300])
        raise
    end_monitor(mon, 'done', 'ended: %d live of %d, %d stopped' % (s['live'], s['total'], len(s['stopped'])))
    print(json.dumps(s, indent=1))
    return s


if __name__ == '__main__':
    main()
