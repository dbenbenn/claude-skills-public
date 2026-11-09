"""The module-route carve as one resumable pipeline (scripts/carve_pipeline.py).

Replaces the per-job bash drivers (plain_carve.sh, plain_pipeline*.sh, ext_publish.sh ...): one
tracked implementation, every step idempotent and logged, state in DIR/pipeline_state.json, every
sub-tool called from one skill snapshot (p2mlib.snapshot) so editing or pushing the live skill
cannot reach a running carve."""
import ast
import fcntl
import hashlib
import json
import math
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
import uuid

from . import leantext, runlock, snapshot, workspace as wslib

STEPS = ['fetch', 'inputs', 'filter_patches', 'port', 'build', 'wsbuild', 'config', 'graph', 'extdefs', 'plan', 'gen', 'names',
         'order', 'measure', 'calibrate', 'publish_prep', 'prose', 'check_text', 'dryrun', 'publish_early',
         'measure_pieces', 'calibrate_pieces', 'pieces_prep', 'publish']
# Overlap mode (pipeline.json `overlap`, on for carves created since 2026-10-29; dbenbenn: "a slow proof
# really shouldn't need to block submitting definition bundles"): `measure`, `calibrate` and the gates
# up to `dryrun` cover the bundles and statements only (the part that freezes at publish);
# `publish_early` (with --publish) publishes them from a background publisher while these steps
# measure, calibrate and check the pieces, which `publish` then releases.
OVERLAP_ONLY = ('publish_early', 'measure_pieces', 'calibrate_pieces', 'pieces_prep')
DEFAULT_LEAN_CAP = '~/claude/claude-private/tools/lean-cap'
PARAM_KEYS = ['folder', 'root_module', 'targets', 'bundle_prefix', 'defs', 'forced', 'patches', 'compat_imports',
              'stdsimplex', 'budget', 'lean_src', 'commit', 'fetch', 'config_set', 'measure_flags', 'meta', 'tags',
              'overlap', 'unif_integrable', 'stream_bundles', 'stream_pieces', 'accept_orphans',
              'try_over_memory', 'piece_rss_limit']


LIMIT_FACTOR = 1.6      # a measured item this many times the budget is too slow for the verifier
MAX_REPLANS = 2
MAX_SCALE = 8.0


class StepFailed(Exception):
    pass


ACCEPT_CAP = 200        # an accept_over item is excused only below this many seconds
UNIFORM_MIN, UNIFORM_RATIO = 3, 2.5   # pieces over plan by a similar factor >= this: re-plan (oaiq-073)
SYSTEMATIC_FRACTION = 0.25   # bundles over the limit: a systematic cost-model error when at least
                             # UNIFORM_MIN of them and this share of the measured bundles (Batch 3,
                             # 2026-10-25: QuarticPowerFree, KirchbergRordam, nearly every bundle 85-128 s
                             # against 55 s); fewer are split alone (oaiq-081: 3 of 194 bundles)
MAX_BUNDLE_SPLITS = 3   # rounds of splitting single slow bundles before a person looks
MAX_PIECE_SPLITS = 2    # local splits of one piece (carve.py split-piece) before a person looks
STREAM_BATCH = 64       # items measured per carve_measure run while streaming them to the publisher
STREAM_SAMPLE = 20      # bundles measured before the first bundle or statement is released (the systematic check)
IMPORT_LIMIT = 160e6    # .olean bytes an item may import (its measured closure_bytes). q153 (2026-11-06): all 609
                        # accepted proofs imported <= 148 MB; above, the verifier's workers ran out of memory ("Lean
                        # exited with code 137"; ~55% of first tries passed at 300-600 MB, retries 1 in 5), and
                        # bundles importing 584 MB took 17 tries. The proofs used ~2% of what they imported: the
                        # schedule chunker's top bundles mixed unrelated declarations (chunker `closure` groups by need)
STATEMENT_SHARE = 0.5   # a slow piece whose statement alone compiles in this share of its time is slow
                        # by its type (oaiq-075: 316 s of 328 in .olean serialization): no split helps
BUNDLE_OWN_LIMIT = 80   # s local: an unpublished bundle over this is split (or excused), even under budget x 1.6.
                        # q154/q172 (2026-11-04): data bundles (numeric literals, typeclass-bound) measured 83.3,
                        # 87.7 and 88.6 s against the 88 s limit hit the server's own "Compilation timed out after
                        # 300s" 2, 3 and 1 times; E011 stopped for a person with 24 bundles behind it
ACCEPT_BUSY = 5         # accept_over on a bundle this many items import gets a warning: E001 (88.6 s) took 6 tries
PIECE_RSS_LIMIT = 7150  # MiB: a piece whose verifier-form file peaks over this locally (carve_measure rss_mib) is split
                        # before it is sent; one at or under it is tried once (dbenbenn 2026-11-09: "if a piece is
                        # borderline (memory <7100MiB say) try submitting it once before splitting"; was 7050), and a
                        # memory kill splits it (verdicts PIECE_OOM_CAP 0). 7150 since 2026-11-09 (dbenbenn: "nudge up"):
                        # q153's pieces sent at 7,051-7,100 MiB were 87 accepted first try, 2 after a failure, none lost.
                        # before it is sent. q153 (2026-11-08): 106 pieces stopped after four memory kills each
                        # (verdicts hidden/dependency_oom); accepted pieces peaked at <= 7,099 MiB (one 7,135), the
                        # stopped and timed-out ones at 7,113-7,250 (one 6,822), while `import Mathlib` alone peaks at
                        # 6,551: the workers' cap is about 7 GiB. Neither time (30-45 s pieces passed about half the
                        # time) nor the import closure (82 pieces importing >= 90 MB, under 20 s, all passed) separated them
PIECE_RSS_TARGET = 7050 # MiB: what a memory split sizes its parts to stay under (a margin below PIECE_RSS_LIMIT)
MAX_MEMORY_PARTS = 8    # most parts one memory split makes
MAX_MEMORY_ROUNDS = 2   # automatic memory splits of one piece before a person looks. q153 (2026-11-08): of the first 32
                        # halved pieces measured, 9 stayed just over (7,053-7,095 MiB): the proof's share does not halve exactly
STREAM_SPLIT_MINUTES = 60   # memory splits while the measure streams: the first at once, then at most this often
MEASURE_JOBS = 8        # pieces measured at once (carve_measure --jobs; pipeline.json measure_jobs); lean-cap queues them and
                        # starts each past its base 3 only while memory and load allow (dbenbenn 2026-11-09; was 3)
PIECE_CAP = 100         # a piece (resubmittable) is excused below this; dbenbenn 2026-11-08 (150, then 120 from
                        # 2026-10-29): verifier data: 94-103 s passed, 118-126 s timed out 3x (oaiq-078), whole-file
                        # 119 s and 126 s 2x (q209, q196), 192 s 3x (oaiq-031); 125 s and 162 s passed on a retry
                        # (oaiq-047, -085). Independent of PIECE_RSS_LIMIT: a piece over either is split


def fits_memory(rec, limit=PIECE_RSS_LIMIT):
    """Does a measured item fit the verifier's memory (PIECE_RSS_LIMIT)? A record from before carve_measure
    recorded peaks fits (carve_measure measures pieces of RSS_REMEASURE_SECS and more again)."""
    return not rec or not rec.get('rss_mib') or rec['rss_mib'] <= limit


def memory_parts(rss, base):
    """Parts to split a piece peaking at `rss` MiB into, its statement alone (its imports) peaking at `base`:
    the proof's own share (rss - base) shared out so each part's fits the room under PIECE_RSS_TARGET. None when
    the imports alone are over (no split helps); 2 when the statement's peak is unknown."""
    if base is None:
        return 2
    room = PIECE_RSS_TARGET - base
    if room <= 0:
        return None
    return min(MAX_MEMORY_PARTS, max(2, int(math.ceil((rss - base) / room))))


def calibration(plan, times, scale, budget, frozen=(), limit_factor=LIMIT_FACTOR, accepted=(), rss_limit=PIECE_RSS_LIMIT,
                bundle_limit=BUNDLE_OWN_LIMIT):
    """Does the cost model's `scale` (time_scale) fit this carve's measured times?
    Returns {'over': [(item, secs, cost)], 'ratio', 'new_scale', 'limit', 'bundle_limit', 'measured',
    'slowest', 'statements_over', 'excused': [(item, secs)] (accept_over), 'memory_over': [(piece, rss MiB,
    secs)] (over PIECE_RSS_LIMIT, unpublished; apart from `over`: memory says nothing of the cost model)}. A bundle is over at
    min(limit, `bundle_limit`) (BUNDLE_OWN_LIMIT).

    Batch 3 (2026-10-25): the first plans of QuarticPowerFree and KirchbergRordam were made with the
    default scale and measured at 85-128 s per bundle against a budget of 55 s; a 128 s bundle timed
    out three times at the verifier. Re-planned with time_scale 2.2 and 4.5, every item fitted. One
    sample of pieces cannot predict this (per-item error ran 0.3-1.4x at the final scale, so a
    small sample would have called Kirchberg's first plan fine), but the full measurement that
    precedes publishing already holds every item: an item measured over `limit_factor` x budget,
    that is not frozen (published), sets the scale to scale x (its measured seconds / its planned
    cost), the worst item deciding, so that its share is split next time. Items measured
    under the limit never lower the scale: a pessimistic estimate costs a few more bundles, a
    timeout costs three publish attempts."""
    limit = budget * limit_factor
    blimit = min(limit, bundle_limit or limit)
    over, measured, slowest, excused, memory_over = [], 0, None, [], []
    items = [('bundle:' + b['name'], b['name'], b.get('cost') or 0) for b in plan.get('bundles', [])]
    items += [('piece:' + n, n, p.get('cost') or 0) for n, p in (plan.get('pieces') or {}).items()]
    for key, name, cost in items:
        t = times.get(key) or (times.get(name) if key.startswith('bundle:') else None)
        if not t or not t.get('ok'):
            continue
        measured += 1
        if slowest is None or t['secs'] > slowest[1]:
            slowest = (key, t['secs'])
        if key.startswith('piece:') and not fits_memory(t, rss_limit) and name not in frozen:
            memory_over.append((key, t['rss_mib'], t['secs']))
            continue
        if key.startswith('piece:') and t['secs'] <= PIECE_CAP:
            # a piece is a proof: resubmittable, so submit as is and split only after two real
            # timeouts (oaiq-035/037: a 106 s piece cost two ~1 h re-plans); bundles and statements
            # freeze at publish
            continue
        if key in accepted and t['secs'] <= ACCEPT_CAP:
            if t['secs'] > (blimit if key.startswith('bundle:') else limit) and name not in frozen:
                excused.append((key, t['secs']))
            continue                                   # pipeline.json accept_over
        if t['secs'] > (blimit if key.startswith('bundle:') else limit) and name not in frozen:
            over.append((key, t['secs'], cost))
    # a statement over the limit publishes, but every verify that imports it compiles its module and
    # fails (opus-kadison, oaiq-039: 110 s and 176 s); re-planning cannot shrink it and accept_over does
    # not excuse it. Published (frozen) and external statements are someone's already.
    statements_over, ext = [], set(plan.get('external') or ())
    for n in plan.get('stubs') or {}:
        t = times.get('statement:' + n)
        if n in ext or n in frozen or not t or not t.get('ok'):
            continue
        measured += 1
        if t['secs'] > limit:
            statements_over.append(('statement:' + n, t['secs']))
    ratio = max((secs / max(cost, 1.0) for _, secs, cost in over), default=1.0)
    new_scale = round(min(MAX_SCALE, max(scale * 1.1, scale * ratio)), 1) if over else scale
    return {'over': over, 'ratio': ratio, 'new_scale': new_scale, 'limit': limit, 'bundle_limit': blimit,
            'measured': measured, 'slowest': slowest, 'statements_over': statements_over, 'excused': excused,
            'memory_over': memory_over}


def heavy_imports(plan, times, skip=(), kinds=('bundle', 'statement', 'piece')):
    """[(item, MB)] of the plan's items (not in `skip`: published) whose measured import closure is over IMPORT_LIMIT,
    heaviest first."""
    items = []
    if 'bundle' in kinds:
        items += [('bundle:' + b['name'], b['name']) for b in plan.get('bundles') or ()]
    if 'statement' in kinds:
        items += [('statement:' + n, n) for n in plan.get('stubs') or {} if n not in set(plan.get('external') or ())]
    if 'piece' in kinds:
        items += [('piece:' + n, n) for n in plan.get('pieces') or {}]
    out = [(key, (times.get(key) or {}).get('closure_bytes') or 0) for key, name in items if name not in skip]
    return sorted(((k, b / 1e6) for k, b in out if b > IMPORT_LIMIT), key=lambda x: -x[1])


def measured_chains(plan, times, skip=()):
    """[(secs, bundle, members, unmeasured)], heaviest first: for each bundle not in `skip` (published), the
    local -j1 times of times.json summed over its import chain (itself and every bundle it imports,
    transitively; published ones included, as a cold verifier worker builds them too). q154: the plan's
    heaviest chain was 369 s, measured 576 s; 29 of 196 chains were over 300 s."""
    from . import carve as CV
    out = []
    for n, chain in CV.bundle_chains(plan).items():
        if n in skip:
            continue
        secs, missing = 0.0, 0
        for x in chain:
            t = times.get('bundle:' + x) or times.get(x)
            if t and t.get('ok'):
                secs += t['secs']
            else:
                missing += 1
        out.append((round(secs, 1), n, len(chain), missing))
    return sorted(out, key=lambda r: (-r[0], r[1]))


def importers(plan, name):
    """(bundles, statements) of the plan whose import chain holds bundle `name` (itself not counted)."""
    from . import carve as CV
    chains = CV.bundle_chains(plan)
    nb = sum(1 for n, c in chains.items() if n != name and name in c)
    ns = sum(1 for st in (plan.get('stubs') or {}).values()
             if any(name in chains.get(b, ()) for b in st.get('bundles') or ()))
    return nb, ns


def chain_lines(plan, times, res, skip=(), top=5):
    """calibrate.log lines: the measured chain sums against the server's 300 s cold build (a warning over
    CHAIN_WARN, never a stop: q172's retries cleared chains up to ~340 s), and a warning for each bundle
    accept_over excuses that many items import."""
    from . import carve as CV
    rows = measured_chains(plan, times, skip)
    lines = []
    if rows:
        warn = [r for r in rows if r[0] > CV.CHAIN_WARN]
        cold = [r for r in rows if r[0] > CV.SERVER_COLD]
        lines.append('  chains (local -j1 times summed over each unpublished bundle\'s imports): heaviest %.0f s '
                     '(%s); %d of %d over %d s, %d over the server\'s %d s cold build' % (
                         rows[0][0], rows[0][1], len(warn), len(rows), CV.CHAIN_WARN, len(cold), CV.SERVER_COLD))
        for secs, n, k, missing in warn[:top]:
            lines.append('    %7.1f s  %s (%d bundles%s): %s' % (secs, n, k, ', %d unmeasured' % missing if missing else '',
                                                          CV.chain_verdict(secs)))
        if warn:
            lines.append('  WARNING: a cold verifier worker builds the whole chain inside the item\'s 300 s ("Module '
                         'compilation timed out"); retries cleared chains up to ~340 s local (q172). Over %d s, '
                         're-plan (chunker closure, a smaller bundle_budget) before publish_early if you can' % CV.CHAIN_WARN)
    for key, secs in res.get('excused') or ():
        if not key.startswith('bundle:'):
            continue
        nb, ns = importers(plan, key.split(':', 1)[1])
        if nb + ns >= ACCEPT_BUSY:
            lines.append('  WARNING: accept_over excuses %s (%.1f s, limit %.0f s) and %d bundle(s) and %d statement(s) '
                         'import it: an own-time timeout on the server stops all of them (q154 E001, 88.6 s: 6 tries); '
                         'prefer a split round while nothing is published' % (key, secs, res['bundle_limit'], nb, ns))
    return lines


def published_drift(lib, published_lib):
    """The .lean files of published_lib (bundles and statements published or being published) that
    lib lacks or holds with other bytes."""
    out = []
    if not os.path.isdir(published_lib):
        return out
    for f in sorted(os.listdir(published_lib)):
        if not f.endswith('.lean'):
            continue
        p = os.path.join(lib, f)
        if not os.path.exists(p) or open(p, 'rb').read() != open(os.path.join(published_lib, f), 'rb').read():
            out.append(f)
    return out


def plan_lib_files(plan):
    """The out/lib file names of a plan's bundles and statements (an external statement is someone else's)."""
    from . import carve as CV
    ext = set(plan.get('external') or ())
    return ({'Def_%s.lean' % b['name'] for b in plan.get('bundles') or ()}
            | {'Thm_%s.lean' % CV.slug(CV.statement_name(plan, n)) for n in plan.get('stubs') or {} if n not in ext})


def _load_json(path, default=None):
    try:
        return json.load(open(path))
    except (OSError, ValueError):
        return default


def run_state_files(d):
    """{out/lib file name: run-state record} of the bundles and statements in DIR/publish/run_state.json."""
    from . import carve as CV
    plan = _load_json(os.path.join(d, 'published', 'plan.json')) or \
        _load_json(os.path.join(d, 'publish', 'plan.json')) or {}
    out = {}
    for item, rec in (_load_json(os.path.join(d, 'publish', 'run_state.json')) or {}).items():
        kind, _, n = item.partition(':')
        if kind == 'bundle':
            out['Def_%s.lean' % n] = rec
        elif kind == 'statement':
            out['Thm_%s.lean' % CV.slug(CV.statement_name(plan, n))] = rec
    return out


def posted(rec):
    """Has the publisher posted this item (live, in flight, retried after a failure, or stopped)?"""
    return isinstance(rec, dict) and (rec.get('state', 'todo') != 'todo' or bool(rec.get('history')) or bool(rec.get('id')))


def live_pieces(d):
    """The nodes whose pieces carve DIR's publisher has sent and not handed to a person (publish/run_state.json
    `piece:NODE` live or in flight): the platform has, or is judging, their text, and split_run never sends
    a live one again without a comparison note."""
    rs = _load_json(os.path.join(d, 'publish', 'run_state.json')) or {}
    return {x.split(':', 1)[1] for x, v in rs.items()
            if x.startswith('piece:') and isinstance(v, dict) and v.get('state') in ('live', 'inflight')}


def protected_keeps(plans, live, slow):
    """config `no_promote` for a frozen re-plan of the `slow` pieces: every declaration the `live` pieces keep
    in any of `plans` (None skipped), less what the slow pieces keep and less the statements themselves.
    q160 (Kadison similarity, 2026-11-03): the automatic re-plan for one slow piece also re-shaped four
    accepted live pieces, wanting six new statements only they would import (Open orphans: a live piece
    is never sent again); confined to the slow piece it made 14, every one reached from it."""
    plans = [p for p in plans if p]
    keep = {x for p in plans for n in live for x in ((p.get('pieces') or {}).get(n) or {}).get('keep', ())}
    keep -= {x for p in plans for n in slow for x in ((p.get('pieces') or {}).get(n) or {}).get('keep', ())}
    return keep - {n for p in plans for n in p.get('pieces') or {}}


def live_piece_changes(ref, new, live, resent=()):
    """What plan `new` changes in the live pieces of plan `ref` (the one they were sent from):
    ({node: why} of live pieces re-shaped, {statement: [live importers]} of the orphans), an orphan being
    a statement new in `new` that no piece still to be sent (not live, or live and `resent`: its comparison
    note makes split_run send it again) or bundle imports, directly or through other new statements. A live
    piece folded on purpose (`new['folded']`) is not re-shaped. q160: a re-shaped live piece keeps its
    published proof, so the statements only it would import stay Open with nothing to prove them."""
    rp, np_ = ref.get('pieces') or {}, new.get('pieces') or {}
    fresh = set(np_) - set(rp) - set(new.get('external') or ())
    reshaped = {}
    for n in sorted(set(live) & set(rp)):
        if n not in np_:
            if n not in (new.get('folded') or ()):
                reshaped[n] = 'no longer a statement of the plan'
            continue
        lost = sorted(set(rp[n].get('keep', ())) - set(np_[n].get('keep', ())))
        if lost:
            to = sorted(set(np_[n].get('imports', ())) & fresh)
            reshaped[n] = '%d declaration(s) moved out (%s%s)%s' % (
                len(lost), ', '.join(lost[:5]), ', ...' if len(lost) > 5 else '',
                ' into new statement(s) %s' % ', '.join(to) if to else '')
    sent = [n for n in np_ if n not in fresh and (n not in live or n in resent)]
    todo = [x for n in sent for x in np_[n].get('imports', ())]
    todo += [x for b in new.get('bundles') or () for x in b.get('statements', ())]
    reached = set()
    while todo:
        x = todo.pop()
        if x in reached:
            continue
        reached.add(x)
        if x in fresh:
            todo += np_[x].get('imports', ())
    orphans = {s: sorted(n for n in live if s in (np_.get(n) or {}).get('imports', ())) for s in sorted(fresh - reached)}
    return reshaped, orphans


def locked_files(d, running=False):
    """The out/lib files of carve DIR that are published or being published, so that no step may change
    them: those publish_early froze (published/lib, as far as they are items of published/plan.json),
    those the publisher's run state shows posted, and while a publisher runs every bundle and statement
    of a plan it may be sending (published/plan.json, publish/plan.json). The rest of publish/out/lib and
    published/lib may change: oaiq-122 (2026-10-30), files of an automatic split's plan the publisher
    never sent (227 beside 74 published) made `check_published_unchanged` and `publish-prep --sync`
    refuse a re-plan that reused 9 of their names. So may an item the run state shows stopped (split_run's
    terminal states: posted, not live, waiting for a person, whose changed text split_run sends again):
    q128 (2026-10-30), a frozen bundle stopped on the verifier before it went live could not take the
    post-carve patch that fixed it."""
    from .splitrun import TERMINAL
    pub = os.path.join(d, 'published')
    frozen_plan = _load_json(os.path.join(pub, 'plan.json'))
    out = set()
    if frozen_plan and os.path.isdir(os.path.join(pub, 'lib')):
        out |= plan_lib_files(frozen_plan) & set(os.listdir(os.path.join(pub, 'lib')))
    rs = run_state_files(d)
    out |= {f for f, rec in rs.items() if posted(rec)}
    if running:
        out |= plan_lib_files(frozen_plan) if frozen_plan else set()
        out |= released_lib_files(d)
    else:
        # pipeline.json `thaw`: files a person thaws on purpose, honoured only for files never posted (q172: the
        # unsent importers of a bundle split by hand after publish_early kept their old imports)
        thaw = set((_load_json(os.path.join(d, 'pipeline.json')) or {}).get('thaw') or ())
        out -= {f for f in thaw if not posted(rs.get(f))}
    return out - {f for f, rec in rs.items() if isinstance(rec, dict) and rec.get('state') in TERMINAL}


def released_lib_files(d):
    """The out/lib files of publish/plan.json a running publisher may send: all of them, unless it is the
    streaming publisher (pipeline_state.json `publisher.gated`, publish/run_stream.json), which sends only
    the bundles and statements publish/release.json lists for that plan (none without one)."""
    path = os.path.join(d, 'publish', 'plan.json')
    plan = _load_json(path)
    if not plan:
        return set()
    files = plan_lib_files(plan)
    if not ((_load_json(os.path.join(d, 'pipeline_state.json')) or {}).get('publisher') or {}).get('gated'):
        return files
    rel = _load_json(os.path.join(d, 'publish', 'release.json'))
    if not isinstance(rel, dict) or rel.get('plan_sha') != hashlib.sha1(open(path, 'rb').read()).hexdigest():
        return set()
    if rel.get('items') == 'all':
        return files
    items = set(rel.get('items') or ())
    return plan_lib_files(dict(plan, bundles=[b for b in plan.get('bundles') or () if 'bundle:' + b['name'] in items],
                               stubs={n: v for n, v in (plan.get('stubs') or {}).items() if 'statement:' + n in items}))


def publisher_running_at(d, state=None):
    """Is a publisher running on carve DIR: a `split_run --go` holding its publish lock, or the background
    publisher pipeline_state.json records (its systemd unit active, or its pid a split_run)?"""
    if runlock.held_by(runlock.dir_key('publish', os.path.join(d, 'publish', 'run.json'))):
        return True
    if state is None:
        state = _load_json(os.path.join(d, 'pipeline_state.json')) or {}
    pub = state.get('publisher') or {}
    if pub.get('unit') and unit_active(pub['unit']):
        return True
    pid = pub.get('pid')
    return bool(pid) and 'split_run' in runlock.cmdline(pid)


def unit_active(unit):
    """Is the systemd user unit running (False without systemd)?"""
    if not unit or not shutil.which('systemctl'):
        return False
    return subprocess.run(['systemctl', '--user', 'is-active', '--quiet', unit]).returncode == 0


def publisher_unit(d):
    return 'carve-pub-' + hashlib.sha1(os.path.realpath(d).encode()).hexdigest()[:10]


ENV_KEEP = ('PATH', 'HOME', 'USER', 'LANG', 'LC_ALL', 'MONITOR_HOME')
ENV_PREFIXES = ('P2M_', 'LEAN_', 'ELAN_')


def systemd_run_command(unit, cwd, env, sh):
    """systemd-run running `/bin/sh -c sh` as the transient user unit `unit`, with the environment
    a carve's tools need."""
    sets = ['--setenv=%s=%s' % (k, v) for k, v in sorted(env.items()) if k in ENV_KEEP or k.startswith(ENV_PREFIXES)]
    return ['systemd-run', '--user', '--unit=' + unit, '--collect', '--quiet', '-p', 'WorkingDirectory=' + cwd,
            *sets, '/bin/sh', '-c', sh]


def module_root_name(rootmod, prefixes, files):
    """The ported file (stem) holding OpenAI module ROOTMOD: oai_port_modules.py names a module
    after its path below the longest matching prefix, '.' -> '_', possibly with a further
    directory prefix; an exact stem wins over a suffix match."""
    best = [p for p in prefixes if rootmod.startswith(p + '.')]
    if best:
        root = rootmod[len(max(best, key=len)) + 1:].replace('.', '_')
    else:
        root = rootmod.rsplit('.', 1)[-1]
    stems = [f[:-5] for f in sorted(files) if f.endswith('.lean')]
    if root in stems:
        return root
    for s in stems:
        if s.endswith('_' + root):
            return s
    raise StepFailed('no ported module for %s (looked for %s.lean or *_%s.lean)' % (rootmod, root, root))


def derive_defs(ws, targets):
    defs = []
    for t in targets:
        _, rel = wslib.statement_module(t)
        p = os.path.join(ws, rel)
        if not os.path.exists(p):
            raise StepFailed('the statement of %s is not in the workspace (%s); fetch_theorems.py first' % (t, rel))
        for line in open(p, encoding='utf-8'):
            m = re.match(r'import\s+(Definitions\.\S+)', line)
            if m and m.group(1) not in defs:
                defs.append(m.group(1))
    return defs


def missing_inputs(ws, targets, defs):
    """The names to fetch so every target statement and Def_ bundle the carve imports is in the workspace:
    a target whose Theorems/ file is absent, or whose preamble imports a Definitions.Def_X not on disk,
    and every listed bundle not on disk."""
    need = []
    for t in targets:
        _, rel = wslib.statement_module(t)
        p = os.path.join(ws, rel)
        if not os.path.exists(p):
            need.append(t)
            continue
        for line in open(p, encoding='utf-8'):
            m = re.match(r'import\s+Definitions\.(\S+)', line)
            if m and not os.path.exists(os.path.join(ws, 'Definitions', m.group(1) + '.lean')):
                need.append(t)
                break
    for d in defs:
        m = re.match(r'Definitions\.Def_(\S+)$', d)
        if m and not os.path.exists(os.path.join(ws, 'Definitions', 'Def_' + m.group(1) + '.lean')):
            need.append(m.group(1))
    return list(dict.fromkeys(need))


def check_meta(path, lean_src, root_module):
    """Why oai_meta.json cannot serve the prose links, or None. publish_prep/prose build every link from
    its `prefixes`; a missing file or prefixes that are not the port's module prefixes gave broken links
    only after the whole carve had run (oaiq-007, oaiq-016)."""
    if not os.path.exists(path):
        return 'no %s: write {"title", "date", "family", "commit", "paper", "prefixes"} (see p2mlib/prosetemplate.py)' % path
    try:
        m = json.load(open(path))
    except ValueError as e:
        return '%s is not valid JSON: %s' % (path, e)
    # what publish_prep and the prose templates read (oaiq-066: no `family` crashed publish_prep with a
    # KeyError after the hour of measuring)
    for k in ('title', 'date', 'family', 'commit'):
        if not m.get(k):
            return '%s has no %r (needed by publish_prep and the prose templates)' % (path, k)
    if not re.fullmatch(r'[0-9a-f]{40}', str(m['commit'])):
        return '%s: commit must be the full 40-hex openai/math commit (links pin it)' % path
    pre = m.get('prefixes')
    if not pre or not isinstance(pre, list):
        return '%s has no "prefixes" (the OpenAI module prefixes, e.g. ["OAI.Geometry.Foo"])' % path
    for p in pre:
        if not os.path.isdir(os.path.join(lean_src, *p.split('.'))):
            return '%s: prefix %r is not a directory of the fetched sources (%s)' % (path, p, lean_src)
    if not any(root_module == p or root_module.startswith(p + '.') for p in pre):
        return '%s: no prefix of %s is a prefix of the root module %s' % (path, pre, root_module)
    # the port strips its own prefixes, OAI.<top directory>, from module names; any other value makes
    # every link repeat a directory (oaiq-031: OAI.Algebra.AuslanderReiten, 181 broken links)
    port = [p for p in openai_prefixes(lean_src) if p.startswith('OAI.')]
    wrong = [p for p in pre if p not in port]
    if wrong:
        return ('%s: prefixes %s are not the port\'s module prefixes (%s, what oai_port_modules strips); '
                'use those' % (path, wrong, [p for p in port if any(w.startswith(p + '.') for w in wrong)] or port))
    return None


def hash_paths(paths, exts=('',)):
    """sha1 over the content of files and directory trees (names relative to each root, sorted), or None
    when none of the paths exists: the identity of what a step reads or writes."""
    h, seen = hashlib.sha1(), False
    for root in paths:
        files = []
        if os.path.isdir(root):
            for dp, dn, fn in os.walk(root):
                dn[:] = sorted(x for x in dn if x != '__pycache__' and not x.startswith('.'))
                files += [os.path.join(dp, f) for f in sorted(fn) if f.endswith(tuple(exts))]
        elif os.path.exists(root):
            files = [root]
        for f in files:
            seen = True
            h.update(os.path.relpath(f, root).encode() + b'\0' + open(f, 'rb').read() + b'\0')
    return h.hexdigest() if seen else None


OUTSIDE_CLOSURE_LIMIT = 50


def outside_closure(lean_src, root_module):
    """(OpenAI modules under lean_src outside root_module's import closure, modules in the closure).
    The port and filter-patches steps take every module under lean_src as input, so lean_src must be
    the closure (what oai_fetch writes), never a whole checkout of openai/math (oaiq-033..048)."""
    seen, todo = set(), [root_module]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        f = os.path.join(lean_src, *m.split('.')) + '.lean'
        if not os.path.exists(f):
            continue
        seen.add(m)
        todo += [i for i in leantext.import_names(open(f, encoding='utf-8').read())
                 if i.split('.')[0] in ('OAI', 'ComparatorChallenges')]
    out = 0
    for d, _, fs in os.walk(os.path.join(lean_src, 'OAI')):
        for f in fs:
            if f.endswith('.lean'):
                m = os.path.relpath(os.path.join(d, f), lean_src)[:-5].replace(os.sep, '.')
                if m not in seen:
                    out += 1
                    if out > 10 * OUTSIDE_CLOSURE_LIMIT:
                        return out, len(seen)
    return out, len(seen)


def openai_prefixes(lean_src):
    """The module prefixes the port takes: OAI.<directory> for each directory of OAI/, then each other
    top directory of the sources that holds Lean files (a third-party package the closure imports and
    the openai/math repo does not ship, e.g. PrimeNumberTheoremAnd, StrongPNT; oaiq-083)."""
    oai = os.path.join(lean_src, 'OAI')
    out = ['OAI.' + d for d in sorted(os.listdir(oai)) if os.path.isdir(os.path.join(oai, d))]
    for d in sorted(os.listdir(lean_src)):
        top = os.path.join(lean_src, d)
        if d != 'OAI' and os.path.isdir(top) and any(f.endswith('.lean') for _, _, fs in os.walk(top) for f in fs):
            out.append(d)
    return out


def _now():
    return time.strftime('%Y-%m-%dT%H:%M:%S')


def _epoch(stamp):
    """Seconds since the epoch of a `_now()` stamp (local time); infinity when missing or unreadable."""
    try:
        return int(time.mktime(time.strptime(stamp, '%Y-%m-%dT%H:%M:%S')))
    except (TypeError, ValueError):
        return float('inf')


# What in the running skill snapshot decides a step's output, beside what it reads from other steps:
# {step: (input name, files relative to the snapshot's prove2me/)}. oaiq-085/092: after a fix to an
# oaiport rewrite, `--upgrade` kept the old ported text (it took `--redo port`). oaiq-047: an upgrade
# across a LeanInfo.lean change left `graph` done, and `plan` re-elaborated 1259 modules one at a time
# (the LeanInfo cache is keyed by LeanInfo.lean) for ~3 h with no output.
_COMPAT = ['lean/compat_4_34.lean', 'lean/StdSimplexCompat.lean', 'lean/StdSimplexTopCompat.lean',
           'lean/UnifIntegrableCompat.lean']
# what of carve_prep.py `filter-patches` runs: its rule input was the whole file, which changes almost daily
# for other subcommands, so every skill commit made a planned carve's port stale (oaiq-081, 2026-10-29)
FILTER_PATCHES_CODE = ('cmd_filter_patches', 'port_filter_patches', 'filter_patches', 'cut_identifier', '_IDENT',
                       'COMPAT', 'positional', 'opt')
SNAPSHOT_RULES = {
    'filter_patches': ('filter rules', ['scripts/carve_prep.py::' + ','.join(FILTER_PATCHES_CODE),
                                        'p2mlib/oaiport.py'] + _COMPAT),
    'port': ('port rules', ['scripts/oai_port_modules.py', 'p2mlib/oaiport.py'] + _COMPAT),
    'graph': ('LeanInfo tool', ['lean/LeanInfo.lean', 'lean/DeclGraph.lean']),
    # q145 (2026-11-01): a carver fix reached the staged files only with `--redo gen`; leantext holds the
    # guard rules gen stops on. Kept like the port once publishing has started
    'gen': ('carver', ['p2mlib/carve.py', 'scripts/carve.py', 'p2mlib/leantext.py']),
}
GRAPH_READERS = ('extdefs', 'plan', 'gen')     # the steps that load the graph (and LeanInfo's readings)
# q131 (2026-10-30): the steps that read the files gen writes, with the parts of `out/` each reads; a re-run
# gen whose output changed makes them stale (and everything after them: publish_prep, pieces_prep sync
# publish/out). `--redo gen` after a patch for two stopped pieces had left measure_pieces, calibrate_pieces
# and pieces_prep done, so publish/out kept the old text and split_run resent nothing
GEN_READERS = {'measure': ('lib',), 'measure_pieces': ('solutions',)}
GRAPH_CONFIG_KEYS = ('src', 'roots', 'prefix', 'work', 'external_theorems')   # what `carve.py graph` reads


def merged_promote_private(cur, auto):
    """config `promote_private` with the automatic split's lemmas added; `True` (every private theorem,
    q152) already covers them."""
    return True if cur is True else sorted(set(cur or ()) | set(auto))


def python_defs(text, names):
    """The source of the top-level definitions and assignments `names` of a Python file, as one string
    (a missing one as `NAME=<missing>`); the whole text if it does not parse."""
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return text
    got = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            ns = [node.name]
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            ts = node.targets if isinstance(node, ast.Assign) else [node.target]
            ns = [t.id for t in ts if isinstance(t, ast.Name)]
        else:
            continue
        for n in ns:
            if n in names:
                got[n] = ast.get_source_segment(text, node)
    return '\0'.join('%s=%s' % (n, got.get(n, '<missing>')) for n in names)


def rules_hash(snap, rels):
    """sha1 over the files `rels` (relative to SNAP/prove2me) that exist, or None if none does. An entry
    `FILE.py::a,b` takes only those top-level definitions of FILE.py (python_defs)."""
    h, seen = hashlib.sha1(), False
    for r in rels:
        rel, _, names = r.partition('::')
        f = os.path.join(snap, 'prove2me', rel)
        if os.path.exists(f):
            seen = True
            data = open(f, 'rb').read()
            if names:
                data = python_defs(data.decode('utf-8', 'replace'), names.split(',')).encode()
            h.update(r.encode() + b'\0' + data + b'\0')
    return h.hexdigest() if seen else None


def carve_of(path):
    """The nearest directory at or above `path` that holds a pipeline.json (a carve directory), or None."""
    p = os.path.abspath(os.path.expanduser(path))
    while True:
        if os.path.isfile(os.path.join(p, 'pipeline.json')):
            return p
        q = os.path.dirname(p)
        if q == p:
            return None
        p = q


def logged_snapshot(log):
    """The snapshot directory of the last run recorded in a step log (`==== TIME STEP (skill SHA)`), if
    it is still in the snapshot cache."""
    if not os.path.exists(log):
        return None
    shas = re.findall(r'^==== \S+ \S+ \(skill (\S+)\)$', open(log, errors='replace').read(), re.M)
    if not shas:
        return None
    d = os.path.join(snapshot.cache_dir(), shas[-1])
    return d if os.path.isdir(d) else None


class Pipeline:
    def __init__(self, d, params, snap_root, ws=None):
        self.d = os.path.abspath(d)
        self.p = params
        self.snap = snap_root
        self.ws = ws or wslib.workspace()
        self.scripts = os.path.join(snap_root, 'prove2me', 'scripts')
        self.state_path = os.path.join(self.d, 'pipeline_state.json')
        self.state = json.load(open(self.state_path)) if os.path.exists(self.state_path) else {'steps': {}}
        self.lean_src = os.path.abspath(os.path.expanduser(params.get('lean_src') or os.path.join(self.d, 'src', 'lean')))
        self.meta = os.path.abspath(os.path.expanduser(params.get('meta') or os.path.join(self.d, 'oai_meta.json')))
        self._kept_rules = set()
        self.ran_now = set()
        self.waiting = None          # what the driver waits for, if anything (the monitoring-page section)

    # -- state ------------------------------------------------------------------------------
    def save(self):
        tmp = self.state_path + '.tmp'
        json.dump(self.state, open(tmp, 'w'), indent=1)
        os.replace(tmp, self.state_path)

    def folder_dir(self):
        return os.path.join(self.ws, 'Solutions', self.p['folder'])

    def step_inputs_hash(self, s):
        """{name: hash} of what step `s` reads that another step (or the user) produces, taken now. Recorded
        when the step finishes; a later run that finds a recorded hash different has a stale step, and
        it and everything after it run again. `--redo filter_patches` after editing the patches changed
        port_patches.json and left the port unpatched (six batches, 2026-10); `--from` and `--redo` stay
        as they were. config.json is not tracked: calibrate rewrites it on purpose."""
        pp = os.path.expanduser(self.p['patches']) if self.p.get('patches') else None
        port_out = hash_paths([self.folder_dir()], ('.lean',))
        opts = json.dumps(self.compat_args())
        h = {
            'filter_patches': {'patches file': hash_paths([pp] if pp else []),
                               'sources': hash_paths([self.lean_src], ('.lean',))},
            'port': {'filter_patches': hash_paths([self.port_patches()]),
                     'sources': hash_paths([self.lean_src], ('.lean',)), 'port options': opts},
            'build': {'port': port_out},
            'config': {'port': port_out},
            'gen': {'carve patches': hash_paths([cp] if (cp := self.carve_patches_path()) else [])},
        }.get(s, {})
        if s in GEN_READERS:
            h['gen output'] = self.gen_output_hash(s)
        if s == 'gen' and (cfg := self.read_config()) is not None:
            # q172: a bundle split by hand (`carve.py split --only`, the remedy for a bundle stopped on own
            # timeouts) changed plan.json, and the resume measured the old out/lib; calibrate's own splits
            # invalidate gen themselves, a hand split or fold has only this
            h['plan'] = hash_paths([self.work_paths(cfg)[1]])
        if s in GRAPH_READERS and (gp := self.graph_path()):
            # oaiq-123: a `graph` re-run by a LeanInfo change is popped alone, "its consumers check its
            # output": without this, a changed graph left the old plan in place
            h['graph output'] = hash_paths([gp])
        if s == 'filter_patches' and pp:           # a skipped filter_patches reads no rules
            h['port options'] = opts
        rule = SNAPSHOT_RULES.get(s)
        if rule and (s != 'filter_patches' or pp):
            h[rule[0]] = rules_hash(self.snap, rule[1])
        return h

    def gen_out(self):
        """The directory `carve.py gen` writes (config `out`, carve_prep's default DIR/out)."""
        return os.path.expanduser((self.read_config() or {}).get('out') or os.path.join(self.d, 'out'))

    def gen_output_hash(self, s):
        """What of gen's output step `s` reads: out/lib for `measure` in overlap mode (the pieces are
        measure_pieces'), all of out/ for the classic measure."""
        parts = GEN_READERS[s] if self.overlap() else ('lib', 'solutions')
        return hash_paths([os.path.join(self.gen_out(), x) for x in parts], ('.lean',))

    def graph_path(self):
        """The declaration graph `carve.py graph` writes (config `work`/decl_graph.jsonl), or None."""
        w = (self.read_config() or {}).get('work')
        return os.path.join(self.d, os.path.expanduser(w), 'decl_graph.jsonl') if w else None

    def carve_patches_path(self):
        """The post-carve patches file `carve.py gen` applies (config `patches`), or None. Its text is an input
        of `gen`: oaiq-114 fixed a broken patch in place, and the resume kept generating the old one."""
        try:
            p = json.load(open(os.path.join(self.d, 'config.json'))).get('patches')
        except (OSError, ValueError):
            p = None
        p = p or (self.p.get('config_set') or {}).get('patches')
        return os.path.join(self.d, os.path.expanduser(p)) if p else None

    RULE_KEYS = {r[0] for r in SNAPSHOT_RULES.values()}

    def stale_step(self):
        """The first finished step whose recorded input hashes differ from the current ones: (step, what).
        A record without a rule hash (a state from before they were recorded) is compared with the
        snapshot its step log names, when that is still cached. A changed rule of `graph` matters only
        while a step that loads the graph has still to run (it re-warms the LeanInfo cache)."""
        for s in STEPS:
            rec = self.state['steps'].get(s)
            if not rec or rec['status'] not in ('done', 'skipped'):
                continue
            now = self.step_inputs_hash(s)
            had = rec.get('in') or {}
            if s == 'filter_patches' and not had and (rec['status'] == 'skipped') == bool(self.p.get('patches')):
                # a record from before hashes: no hash to compare, but whether the step is skipped at all changed
                # (oaiq-119: patches added to pipeline.json, and the resume measured the unpatched port)
                return s, 'patches file'
            for k, old in had.items():
                if k in now and now[k] != old and (k not in self.RULE_KEYS or self._rule_matters(s)):
                    return s, k
            g = self.state['steps'].get('graph') or {}
            if (s in GRAPH_READERS and 'graph output' not in had and rec['status'] == 'done'
                    and g.get('status') == 'done' and g.get('finished', '') > rec.get('finished', '~')):
                # a record from before the graph hash: `graph` ran again after it (oaiq-019/oaiq-123)
                return s, 'graph output'
            if (s in GEN_READERS and 'gen output' not in had and rec['status'] == 'done'
                    and (self.state['steps'].get('gen') or {}).get('status') == 'done'
                    and self.state['steps']['gen'].get('finished', '') > rec.get('finished', '~')):
                # a record from before the gen hash: gen ran again after it (q131)
                return s, 'gen output'
            if (s in ('build', 'config') and 'port' not in had and rec['status'] == 'done'
                    and self.newest_ported_mtime() > _epoch(rec.get('finished'))):
                # a record from before the port hash, and the port rewrote a module after it (oaiq-122: an
                # --upgrade grew Compat.lean, build was skipped, graph read stale .olean ranges)
                return s, 'port'
            rule = SNAPSHOT_RULES.get(s)
            if rule and rule[0] in now and rule[0] not in had and rec['status'] == 'done' and self._rule_matters(s):
                then = logged_snapshot(os.path.join(self.d, 'logs', s + '.log'))
                if then and os.path.realpath(then) != os.path.realpath(self.snap):
                    old = rules_hash(then, rule[1])
                    if old is not None and old != now[rule[0]]:
                        return s, rule[0]
        return None

    PORT_STEPS = ('filter_patches', 'port')

    def keep_port(self):
        """--keep-port: keep the port as it is across changes to the skill's port rules, from now until an
        explicit `--redo port` or `--redo filter_patches` (or a --from at or before them): pipeline_state.json
        `keep_port`. oaiq-081: planned and measured (1,586 items) on an old snapshot, the new rules changed
        port_patches.json and would have re-ported, rebuilt and re-planned the whole carve; recording the
        current rules once held only until the next skill commit changed them again. The current rules and
        options are recorded as well, so a later change of the port options is still seen."""
        kept = []
        for s in self.PORT_STEPS:
            rec = self.state['steps'].get(s)
            if not rec or rec['status'] != 'done':
                continue
            now, had = self.step_inputs_hash(s), rec.setdefault('in', {})
            for k in (SNAPSHOT_RULES[s][0], 'port options'):
                if k in now and had.get(k) != now[k]:
                    had[k] = now[k]
                    kept.append(s)
        if not self.state.get('keep_port'):
            self.state['keep_port'] = {'since': _now(), 'skill': os.path.basename(self.snap)}
        print('== --keep-port: keep the port as it is across port-rule changes until `--redo port` (or '
              '`--redo filter_patches`)%s' % (
                  '; the current rules are recorded for %s' % ' and '.join(sorted(set(kept))) if kept else ''),
              flush=True)
        self.save()

    def clear_keep_port(self, why):
        if self.state.pop('keep_port', None):
            print('== %s: --keep-port ends; the port follows the skill\'s port rules again' % why, flush=True)

    def _rule_matters(self, s):
        if s == 'graph':
            return any(self.state['steps'].get(x, {}).get('status') not in ('done', 'skipped') for x in GRAPH_READERS)
        if s in self.PORT_STEPS and self.state.get('keep_port'):
            if s not in self._kept_rules:
                self._kept_rules.add(s)
                print('== note: the skill\'s port rules changed since %s ran; kept by --keep-port (since %s; '
                      '`--redo port` re-ports)' % (s, self.state['keep_port'].get('since')), flush=True)
            return False
        if self.publishing_started():
            # live items froze their text: never re-port under them by ourselves
            if s not in self._kept_rules:
                self._kept_rules.add(s)
                print('== note: the skill\'s %s changed since %s ran, but publishing has started, so '
                      'its output is kept (`--redo %s` runs it anyway)' % (SNAPSHOT_RULES[s][0], s, s), flush=True)
            return False
        return True

    def publishing_evidence(self):
        """Why this carve has visibly begun publishing, or None: a publish or publish_early step record, a
        split_run run state, or the frozen published part (auto_config `frozen`, set by publish_early)."""
        steps = self.state['steps']
        if 'publish' in steps:
            return 'step publish ran'
        if 'publish_early' in steps:
            return 'step publish_early ran'
        if os.path.exists(os.path.join(self.d, 'publish', 'run_state.json')):
            return 'publish/run_state.json exists'
        if (self.state.get('auto_config') or {}).get('frozen'):
            return 'publish_early froze the published part (auto_config frozen)'
        return None

    def mark_publishing(self, why):
        if not self.state.get('publishing_started'):
            self.state['publishing_started'] = {'at': _now(), 'why': why}

    def publishing_started(self):
        """Has publishing begun? A state fact (pipeline_state.json `publishing_started`), set the first time
        any evidence is seen and kept: a frozen re-plan drops publish_early from the step records, and
        publish/run_state.json need not exist yet, so the evidence alone came and went (2026-10-29)."""
        if self.state.get('publishing_started'):
            return True
        why = self.publishing_evidence()
        if why:
            self.mark_publishing(why)
            return True
        return False

    def forget_publishing(self):
        """--forget-publishing: the explicit reset, refused while any evidence remains."""
        why = self.publishing_evidence()
        if why:
            raise StepFailed('--forget-publishing: refused, publishing has visibly begun (%s)' % why)
        if self.state.pop('publishing_started', None):
            print('== --forget-publishing: this carve counts as not publishing again', flush=True)

    # -- the port folder's owner ------------------------------------------------------------
    def owner_path(self):
        return os.path.join(self.folder_dir(), wslib.CARVE_OWNER)

    def read_owner(self):
        try:
            return json.load(open(self.owner_path()))
        except (OSError, ValueError):
            return None

    def write_owner(self, how):
        if not os.path.isdir(self.folder_dir()):
            return
        if not self.state.get('carve_id'):
            self.state['carve_id'] = uuid.uuid4().hex
        rec = {'carve': os.path.realpath(self.d), 'carve_id': self.state['carve_id'], 'since': _now(), 'how': how}
        tmp = self.owner_path() + '.tmp'
        json.dump(rec, open(tmp, 'w'), indent=1)
        os.replace(tmp, self.owner_path())
        print('== Solutions/%s now belongs to this carve (%s)' % (self.p['folder'], how), flush=True)

    def port_log_carves(self):
        """The carve directories named by the last port command in logs/port.log (its sources, its
        port_patches.json), or None when this carve's log records no port."""
        log = os.path.join(self.d, 'logs', 'port.log')
        if not os.path.exists(log):
            return None
        cmds = [l[2:].split() for l in open(log, errors='replace') if l.startswith('$ ') and 'oai_port_modules' in l]
        if not cmds:
            return None
        out = set()
        for t in cmds[-1][2:]:                     # past the interpreter and the (snapshot's) script
            if t.startswith('/'):
                c = carve_of(t)
                if c:
                    out.add(os.path.realpath(c))
        return out

    def ever_ported(self):
        return 'port' in self.state['steps'] or self.port_log_carves() is not None

    def recorded_port_hashes(self):
        """The hashes of the port folder this carve recorded: what build and config read, what port wrote."""
        st = self.state['steps']
        hs = {((st.get(s) or {}).get('in') or {}).get('port') for s in ('build', 'config')}
        hs.add(((st.get('port') or {}).get('out') or {}).get('port'))
        return hs - {None}

    BELONGS = ('Solutions/%s belongs to carve %s; a copy must use its own workspace (P2M_WORKSPACE) or another '
               'folder. If this carve is to own it now (the other was abandoned), `--claim-folder`')

    def check_ownership(self, claim=False):
        """Before any step: the port writes WORKSPACE/Solutions/FOLDER, outside the carve dir, and gen and
        measure write config `out` and `work`. Refuse when the folder belongs to another carve directory
        (its owner file), or config.json points `out`/`work` into another carve or `src` at another workspace. A folder without an
        owner file (a carve from before 2026-10-29) is adopted by the carve whose port log names no other
        carve and whose recorded port hash is its current hash (or that recorded none: ported, not yet
        built), claimed by a carve that never ported, and else waits for `--claim-folder`. A carve moved to
        another directory (same carve_id, the old directory gone) takes its folder along. 2026-10-29: a
        `cp -a` rehearsal copy of oaiq-081 on the shared workspace re-ported and rewrote 228 files of the
        live carve's Solutions/OAIQ081_SAT (its config.json also named the original's out/ and work/)."""
        here, folder, f = os.path.realpath(self.d), self.folder_dir(), self.p['folder']
        problems, how = [], None
        cfg = self.read_config() or {}
        for k in ('out', 'work'):
            v = cfg.get(k)
            c = carve_of(v) if isinstance(v, str) and v else None
            if c and os.path.realpath(c) != here:
                problems.append('config.json `%s` (%s) lies in carve %s, which gen and measure would write: '
                                'a copy must point `out` and `work` at its own directory' % (k, v, c))
        src = cfg.get('src')
        if isinstance(src, str) and src and os.path.realpath(os.path.expanduser(src)) != os.path.realpath(self.ws):
            problems.append('config.json `src` (%s) is not this run\'s workspace %s (P2M_WORKSPACE): graph, plan and '
                            'measure would read and compile there' % (src, self.ws))
        owner = self.read_owner()
        if owner:
            them = owner.get('carve')
            if them != here:
                moved = (owner.get('carve_id') and owner['carve_id'] == self.state.get('carve_id')
                         and not os.path.exists(os.path.join(them or '', 'pipeline_state.json')))
                if claim:
                    how = '--claim-folder, from %s' % them
                elif moved:
                    how = 'the carve moved from %s' % them
                else:
                    problems.append(self.BELONGS % (f, them))
        elif os.path.isdir(folder) and any(x.endswith('.lean') for _, _, fs in os.walk(folder) for x in fs):
            named = self.port_log_carves()
            others = sorted(c for c in named or () if c != here)
            if claim:
                how = '--claim-folder'
            elif others:
                problems.append(self.BELONGS % (f, others[0]) + ' (no owner file; this carve\'s port log names '
                                'that carve: a copy of it?)')
            elif hash_paths([folder], ('.lean',)) in self.recorded_port_hashes():
                how = 'adopted: its modules are the port this carve recorded'
            elif not self.ever_ported():
                how = 'first port'
            elif not self.recorded_port_hashes():
                # ported (by its own log), never built: no hash to compare
                how = 'adopted: this carve\'s port log names no other carve and no hash was recorded since'
            else:
                problems.append('Solutions/%s has no owner file and its modules are not the port this carve recorded '
                                '(changed since by hand, or by another carve). If it is this carve\'s, '
                                '`--claim-folder` (the changed modules then rebuild as stale)' % f)
        if problems:
            raise StepFailed('refused, nothing was run:\n  ' + '\n  '.join(problems))
        if how:
            self.write_owner(how)
            self.save()

    def overlap(self):
        return bool(self.p.get('overlap'))

    def steps(self):
        """The steps this carve runs: every one in overlap mode, else the classic list."""
        return list(STEPS) if self.overlap() else [x for x in STEPS if x not in OVERLAP_ONLY]

    def newest_ported_mtime(self):
        """Whole seconds of the newest ported .lean file's mtime (0 when there is none)."""
        d = self.folder_dir()
        return max((int(os.path.getmtime(os.path.join(dp, f))) for dp, _, fs in os.walk(d) for f in fs
                    if f.endswith('.lean')), default=0) if os.path.isdir(d) else 0

    def ported_modules(self):
        d = self.folder_dir()
        return sum(1 for _, _, fs in os.walk(d) for f in fs if f.endswith('.lean')) if os.path.isdir(d) else 0

    def compat_changed(self):
        """Would a re-port under this snapshot rewrite the built port's Compat.lean? Every ported module
        imports it, so that rebuilds them all (oaiq-088: every full rebuild of four began `Built ...Compat`,
        the snapshots' compat_4_34.lean all differed; an unchanged port replays, oai_build_modules)."""
        if (self.state['steps'].get('build') or {}).get('status') != 'done':
            return False
        cl = os.path.join(self.folder_dir(), 'Compat.lean')
        src = os.path.join(self.snap, 'prove2me', 'lean', 'compat_4_34.lean')
        if not (os.path.exists(cl) and os.path.exists(src)):
            return False
        from . import oaiport
        block = oaiport.compat_block(open(src, encoding='utf-8').read())[0]
        return not open(cl, encoding='utf-8').read().endswith(block)

    def stale_message(self, s, k):
        if k not in self.RULE_KEYS:
            return '== stale: %s (its input "%s" changed); re-running it and every later step' % (s, k)
        msg = ('== stale: %s (the skill\'s %s changed since it ran); re-running it (later steps run again only '
               'if its output changes)' % (s, k))
        if s in self.PORT_STEPS and self.compat_changed():
            n = self.ported_modules()
            msg += ('\n   WARNING: the skill\'s compat shims (lean/compat_4_34.lean) changed since the port: re-porting '
                    'rewrites Compat.lean, which every ported module imports, so `build` recompiles all %d modules '
                    '(oaiq-088: 2.5-7 h for 2,385; oaiq-095: 9 h for 3,243). Nothing else in the build depends on the '
                    'skill snapshot: an unchanged port replays. To keep this port, stop and resume with '
                    '`--keep-port`' % n)
        if s == 'graph':
            n = self.ported_modules()
            msg += ('\n   WARNING: the LeanInfo cache is keyed by LeanInfo.lean, so none of the %d module%s is '
                    'cached for this snapshot: `graph` elaborates every one again (about the build\'s CPU time, '
                    '`jobs` at a time; progress in logs/graph.log)' % (n, '' if n == 1 else 's'))
        return msg

    def invalidate(self, frm):
        i = STEPS.index(frm)
        for s in STEPS[i:]:
            self.state['steps'].pop(s, None)

    # -- running ----------------------------------------------------------------------------
    def env(self):
        e = dict(os.environ)
        cap = os.environ.get('P2M_LEAN_CAP', DEFAULT_LEAN_CAP)
        cap = os.path.expanduser(cap) if cap else ''
        if cap and os.path.isdir(cap):
            e['PATH'] = cap + os.pathsep + e.get('PATH', '')
        e['P2M_SKILL_ROOT'] = self.snap
        e['P2M_WORKSPACE'] = self.ws
        return e

    def tool(self, name, *args):
        return [sys.executable, os.path.join(self.scripts, name + '.py'), *map(str, args)]

    def run_cmds(self, step, cmds, cwd=None):
        log = os.path.join(self.d, 'logs', step + '.log')
        os.makedirs(os.path.dirname(log), exist_ok=True)
        with open(log, 'a') as f:
            f.write('==== %s %s (skill %s)\n' % (_now(), step, os.path.basename(self.snap)))
            for c in cmds:
                f.write('$ %s\n' % ' '.join(c))
                f.flush()
                r = subprocess.run(c, cwd=cwd or self.d, env=self.env(), stdout=f, stderr=subprocess.STDOUT)
                if r.returncode:
                    f.write('(exit %d)\n' % r.returncode)
                    f.flush()
                    tail = ''.join(open(log, errors='replace').readlines()[-15:])
                    raise StepFailed("step '%s' failed (exit %d); log %s\n%s" % (step, r.returncode, log, tail))

    # -- steps ------------------------------------------------------------------------------
    def prefixes(self):
        return openai_prefixes(self.lean_src)

    def defs(self):
        return self.p.get('defs') or derive_defs(self.ws, self.p['targets'])

    def root(self):
        files = os.listdir(os.path.join(self.ws, 'Solutions', self.p['folder']))
        return module_root_name(self.p['root_module'], self.prefixes(), files)

    def port_patches(self):
        return os.path.join(self.d, 'port_patches.json')

    def compat_args(self):
        a = []
        if self.p.get('compat_imports'):
            a += ['--compat-imports', self.p['compat_imports']]
        if self.p.get('stdsimplex'):
            a += ['--stdsimplex', self.p['stdsimplex']]
        if self.p.get('unif_integrable'):
            a += ['--unif-integrable', self.p['unif_integrable']]
        if self.p.get('hide_instances'):
            a += ['--header', self.port_header()]
        return a

    def port_header(self):
        """pipeline.json `hide_instances` (instance names, e.g. compat ones) as the port's --header file, an
        `attribute [-instance]` line after the imports of every ported module, named by its content so a changed list
        changes the port options (oaiq-122: the compat block's global von Neumann instances, added for Kadison
        similarity, made `whnf` time out in FactorGeneration modules with their own instances on a subalgebra)."""
        text = 'attribute [-instance] %s\n' % ' '.join(self.p['hide_instances'])
        path = os.path.join(self.d, 'port_header_%s.lean' % hashlib.sha1(text.encode()).hexdigest()[:10])
        if not os.path.exists(path):
            open(path, 'w', encoding='utf-8').write(text)
        return path

    def step_fetch(self):
        if not self.p.get('fetch'):
            return 'skipped'
        a = [os.path.join(self.d, 'src'), self.p['root_module']]
        if self.p.get('commit'):
            a += ['--commit', self.p['commit']]
        self.run_cmds('fetch', [self.tool('oai_fetch', *a)])

    def step_inputs(self):
        names = missing_inputs(self.ws, self.p['targets'], self.p.get('defs') or [])
        if not names:
            return 'skipped'
        self.run_cmds('inputs', [self.tool('fetch_theorems', '--names', *names, '--no-build')])
        again = missing_inputs(self.ws, self.p['targets'], self.p.get('defs') or [])
        if again:
            raise StepFailed("step 'inputs': still not in the workspace after fetch_theorems: %s "
                             "(published yet? see logs/inputs.log)" % ', '.join(again))

    def check_closure(self, step):
        out, inside = outside_closure(self.lean_src, self.p['root_module'])
        if out > OUTSIDE_CLOSURE_LIMIT:
            raise StepFailed("step '%s': %s holds %s OpenAI modules outside the import closure of %s (%d "
                             "modules); the port would take them all as input. Use --fetch without "
                             "--lean-src (oai_fetch copies just the closure from the local openai/math "
                             "clone), or point lean_src in pipeline.json at a closure-only copy"
                             % (step, self.lean_src, '%d' % out if out <= 10 * OUTSIDE_CLOSURE_LIMIT
                                else 'more than %d' % (10 * OUTSIDE_CLOSURE_LIMIT), self.p['root_module'], inside))

    def step_filter_patches(self):
        if not self.p.get('patches'):
            return 'skipped'
        self.check_closure('filter_patches')
        self.run_cmds('filter_patches', [self.tool('carve_prep', 'filter-patches', os.path.expanduser(self.p['patches']),
                                                   self.lean_src, self.port_patches(), *self.prefixes(), *self.compat_args(),
                                                   '--folder', self.p['folder'])])

    def step_port(self):
        self.check_closure('port')
        a = [self.lean_src, self.p['folder'], *self.prefixes()]
        if self.p.get('patches'):
            a += ['--patches', self.port_patches()]
        self.run_cmds('port', [self.tool('oai_port_modules', *a, *self.compat_args())])
        rec = self.state['steps'].get('port')
        if rec is not None:
            rec['out'] = {'port': hash_paths([self.folder_dir()], ('.lean',))}
        if not self.read_owner():
            self.write_owner('first port')

    def step_build(self):
        self.run_cmds('build', [self.tool('oai_build_modules', self.p['folder'], self.root(), '--log', 'build.log',
                                          '--elab-log', 'build_elab.log')])

    def step_wsbuild(self):
        mods = self.defs() + [wslib.statement_module(t)[0] for t in self.p['targets']]
        self.run_cmds('wsbuild', [['lake', 'build', *mods]], cwd=self.ws)

    def step_config(self):
        bad = check_meta(self.meta, self.lean_src, self.p['root_module'])
        if bad:
            raise StepFailed("step 'config' failed: " + bad)
        a = ['config', self.d, self.p['folder'], self.root(), self.p['targets'][0]]
        for d in self.defs():
            a += ['--def', d]
        a += ['--bundle-prefix', self.p['bundle_prefix'], '--budget', '%g' % self.p.get('budget', 55)]
        for f in self.p.get('forced') or []:
            a += ['--forced', f]
        self.run_cmds('config', [self.tool('carve_prep', *a)])
        path = os.path.join(self.d, 'config.json')
        cfg = json.load(open(path))
        cfg['targets'] = list(self.p['targets'])
        cfg['external'] = sorted(set(cfg.get('external', [])) | set(self.p['targets']))
        if self.p.get('compat_imports'):
            cfg['collapse_mathlib'] = False
        cfg.update(self.p.get('config_set') or {})
        self.apply_auto(cfg)
        json.dump(cfg, open(path, 'w'), indent=1)
        self.state['config_set_applied'] = dict(self.p.get('config_set') or {})

    def apply_auto(self, cfg):
        """What the pipeline itself set once publishing began (pipeline_state.json `auto_config`), over
        config.json: `frozen` (the published plan, its bundles, their published text), `forced` and
        `template_forced` (the published statements, so a re-plan keeps them; unions with what the
        user forced), `cost_factors` (pieces measured over their plan), `promote_private` (their private
        lemmas, which the plan may then promote like public ones) and `no_promote` (the lemmas of live
        pieces, which it may not; unions with the user's). Re-applied whenever
        config.json is rewritten from pipeline.json, so a re-run `config` cannot unfreeze a carve."""
        a = self.state.get('auto_config') or {}
        if a.get('frozen'):
            cfg['frozen'] = dict(cfg.get('frozen') or {}, **a['frozen'])
        for k in ('forced', 'template_forced', 'no_promote'):
            if a.get(k):
                cfg[k] = sorted(set(cfg.get(k) or ()) | set(a[k]))
        if a.get('promote_private'):
            cfg['promote_private'] = merged_promote_private(cfg.get('promote_private'), a['promote_private'])
        if a.get('cost_factors'):
            cf = dict(cfg.get('cost_factors') or {})
            for k, v in a['cost_factors'].items():
                cf[k] = max(cf.get(k, 1.0), v)
            cfg['cost_factors'] = cf
        return cfg

    def sync_config_set(self):
        """pipeline.json `config_set` keys changed since `config` applied them go straight into
        config.json, and the steps that read them run again: from `gen` for `patches` (post-carve
        literal patches), from `plan` for anything else. Re-running `config` instead would regenerate
        config.json and lose what calibrate wrote (time_scale). oaiq-051: a resume never applied new
        patches, and measure kept failing on unpatched text."""
        path = os.path.join(self.d, 'config.json')
        rec = self.state['steps'].get('config')
        if not rec or rec['status'] != 'done' or not os.path.exists(path):
            return
        want = dict(self.p.get('config_set') or {})
        cfg = json.load(open(path))
        if 'config_set_applied' not in self.state:
            # a state from before this was recorded: config.json holds what was applied (oaiq-120: taking
            # `want` as applied skipped a new `frozen`/`forced`, and the resume published the old plan)
            self.state['config_set_applied'] = {k: cfg[k] for k in want if k in cfg}
        old = self.state['config_set_applied']
        changed = sorted(k for k in set(want) | set(old) if want.get(k) != old.get(k))
        if not changed:
            self.save()
            return
        for k in changed:
            if k in want:
                cfg[k] = want[k]
            else:
                cfg.pop(k, None)
        self.apply_auto(cfg)
        json.dump(cfg, open(path, 'w'), indent=1)
        self.state['config_set_applied'] = want
        frm = 'gen' if set(changed) <= {'patches'} else 'plan'
        print('== config_set changed (%s): config.json updated; re-running from %s' % (', '.join(changed), frm), flush=True)
        if frm in self.state['steps']:
            self.invalidate(frm)
        self.save()

    def read_config(self):
        path = os.path.join(self.d, 'config.json')
        try:
            return json.load(open(path))
        except (OSError, ValueError):
            return None

    def config_consumers(self, before):
        """config.json is not hashed (extdefs and calibrate rewrite it on purpose), so a re-run `config`
        that changed it re-runs what reads it: from `graph` if a key graph reads changed, else from
        `extdefs` (oaiq-047: `--redo config` reset time_scale and left the old plan done)."""
        after = self.read_config()
        if after is None or after == before:
            return
        frm = 'graph' if any(before.get(k) != after.get(k) for k in GRAPH_CONFIG_KEYS) else 'extdefs'
        later = [x for x in STEPS[STEPS.index(frm):] if x in self.state['steps']]
        if later:
            print('== config.json changed (%s): re-running from %s' % (
                ', '.join(sorted(k for k in set(before) | set(after) if before.get(k) != after.get(k)))[:200], frm),
                flush=True)
            self.invalidate(frm)

    def step_names(self):
        # planned names already live with other text, checked before the hours of measuring (oaiq-068/074)
        self.run_cmds('names', [self.tool('carve_prep', 'name-check', 'config.json')])

    def step_graph(self):
        self.run_cmds('graph', [self.tool('carve', 'graph', 'config.json')])

    def step_extdefs(self):
        a = ['ext-defs', 'config.json']
        for d in self.defs():
            a += ['--def', d]
        self.run_cmds('extdefs', [self.tool('carve_prep', *a)])

    def step_plan(self):
        self.run_cmds('plan', [self.tool('carve', 'plan', 'config.json')])
        self.check_live_pieces('plan')

    def check_live_pieces(self, step):
        """Once publishing began, a re-plan must not re-shape a live piece (live_pieces) into new statements
        that nothing still to be sent imports: they would go live as Open orphans, since split_run never
        sends a live piece again without a comparison note (q160). Compares the plan with publish/plan.json
        (else published/plan.json), the plan the pieces were sent from; stops on orphans before anything is
        generated or published, and notes a re-shaped live piece whose new statements other pieces import."""
        if not self.publishing_started():
            return
        live = live_pieces(self.d)
        ref = _load_json(os.path.join(self.d, 'publish', 'plan.json')) or \
            _load_json(os.path.join(self.published_dir(), 'plan.json'))
        cfg = self.read_config()
        new = _load_json(self.work_paths(cfg)[1]) if cfg is not None else None
        if not (live and ref and new):
            return
        from . import carve as CV
        cmp_dir = os.path.join(self.d, 'publish', 'comparisons')
        resent = {n for n in live if n in (new.get('pieces') or {}) and
                  os.path.exists(os.path.join(cmp_dir, CV.slug(CV.statement_name(new, n)) + '.md'))}
        reshaped, orphans = live_piece_changes(ref, new, live, resent)
        # pipeline.json `accept_orphans` (a person's call): those that have a piece of their own go live proved, just
        # unused (q153 2026-11-08: six lemmas of three accepted pieces a memory split had re-shaped)
        ok = {s for s in self.p.get('accept_orphans') or () if s in orphans and s in (new.get('pieces') or {})}
        for s in sorted(ok):
            print('== %s: NOTE accepted orphan statement %s (pipeline.json accept_orphans): imported by %s only; it goes '
                  'live with its own piece' % (step, s, ', '.join('piece:' + n for n in orphans[s]) or 'nothing'),
                  flush=True)
        orphans = {s: v for s, v in orphans.items() if s not in ok}
        if orphans:
            raise StepFailed(
                "step '%s': the new plan re-shapes live piece(s), and %d new statement(s) would be imported by live "
                "pieces only, so they would go live as Open orphans (q160):\n  %s\nlive piece(s) changed:\n  %s\n"
                "Keep their lemmas out of the plan: pipeline.json `config_set.no_promote` (the declarations the live "
                "pieces keep; the automatic split of a slow piece sets this itself), then resume; or, to send a live "
                "piece again in its new form, write publish/comparisons/<slug>.md for it first; or, to let them go live proved but "
                "unused (each has its own piece), list them in pipeline.json `accept_orphans`."
                % (step, len(orphans), '\n  '.join('%s (imported by %s)' % (s, ', '.join('piece:' + n for n in imp) or
                                                                           'other new statements only')
                                                   for s, imp in orphans.items()),
                   '\n  '.join('piece:%s: %s' % x for x in reshaped.items())))
        for n, why in reshaped.items():
            print('== %s: NOTE live piece piece:%s changed in the new plan (%s); its new statements are imported by '
                  'pieces still to be sent, and the live proof stays as it is%s' % (
                      step, n, why, ' (its comparison note sends it again)' if n in resent else ''), flush=True)

    def step_gen(self):
        self.set_thawed()
        self.run_cmds('gen', [self.tool('carve', 'gen', 'config.json')])
        self.check_published_unchanged('gen')
        self.flag_whole_mathlib()

    def flag_whole_mathlib(self):
        """A red flag (dbenbenn 2026-11-08): generated files that `import Mathlib` whole start at 6,551 MiB of the
        verifier's ~7 GiB before their own work, so their proofs get split for memory (PIECE_RSS_LIMIT) and their
        bundles and statements may not publish at all. Listed in pipeline_state.json `whole_mathlib` and warned
        about; the narrow imports come from OpenAI's own files (config collapse_mathlib false)."""
        cfg = self.read_config() or {}
        out = self.gen_out()
        hits = []
        for sub in ('lib', 'solutions'):
            dd = os.path.join(out, sub)
            for f in sorted(os.listdir(dd)) if os.path.isdir(dd) else ():
                if f.endswith('.lean'):
                    with open(os.path.join(dd, f), errors='replace') as fh:
                        head = fh.read(20000)
                    if re.search(r'(?m)^import Mathlib\s*$', head):
                        hits.append('%s/%s' % (sub, f))
        self.state['whole_mathlib'] = hits
        self.save()
        if hits:
            print('== gen: WARNING %d generated file(s) import all of Mathlib (6,551 MiB of the verifier\'s ~7 GiB before '
                  'any work of their own; config collapse_mathlib %s): %s%s' % (
                      len(hits), cfg.get('collapse_mathlib'), ', '.join(hits[:5]), ' ...' if len(hits) > 5 else ''),
                  flush=True)

    def set_thawed(self):
        """config `frozen.thawed`: the files of published/lib that are not locked (locked_files), which gen
        generates, with the post-carve patches, instead of copying them (q128: a bundle stopped on the
        verifier before it went live; oaiq-122: an earlier plan's never-sent statement under a name a
        re-plan reused)."""
        cfg = self.read_config()
        if cfg is None or not isinstance(cfg.get('frozen'), dict):
            return
        lib = os.path.join(self.published_dir(), 'lib')
        have = set(os.listdir(lib)) if (self.state.get('auto_config') or {}).get('frozen') and os.path.isdir(lib) else set()
        thawed = sorted(have - locked_files(self.d, self.publisher_running()))
        if thawed == sorted(cfg['frozen'].get('thawed') or ()):
            return
        if thawed:
            cfg['frozen']['thawed'] = thawed
        else:
            cfg['frozen'].pop('thawed', None)
        json.dump(cfg, open(os.path.join(self.d, 'config.json'), 'w'), indent=1)

    def published_dir(self):
        return os.path.join(self.d, 'published')

    def check_published_unchanged(self, step):
        """Overlap mode, once bundles and statements began publishing: none of their files may change
        (published/lib holds them as they went to the publisher)."""
        if not (self.state.get('auto_config') or {}).get('frozen'):
            return
        locked = locked_files(self.d, self.publisher_running())
        lib, plib = os.path.join(self.gen_out(), 'lib'), os.path.join(self.published_dir(), 'lib')
        changed = published_drift(lib, plib)
        drift = [f for f in changed if f in locked]
        plan = _load_json(os.path.join(self.published_dir(), 'plan.json')) or {}
        thawed = [f for f in changed if f not in locked and f in plan_lib_files(plan) and os.path.exists(os.path.join(lib, f))]
        if not drift:
            # a frozen item that is not live (stopped) changed on purpose: its frozen copy follows, as split_run's
            # heartbeat raise does, and publish-prep --sync brings it to publish/out (q128)
            for f in thawed:
                shutil.copy(os.path.join(lib, f), os.path.join(plib, f))
                print('== %s: %s is frozen but not live (thawed): changed, its copy in published/lib updated'
                      % (step, f), flush=True)
        if drift:
            raise StepFailed(
                "step '%s': %d bundle/statement file(s) that are published or being published changed: %s. They are "
                "frozen: undo what changed them (a carve patch must not touch a bundle or statement once it "
                "publishes; config `frozen`/`forced`, which the pipeline set when publishing began, keep a "
                "re-plan from moving them). Compare out/lib with %s/lib."
                % (step, len(drift), ', '.join(drift[:20]), self.published_dir()))

    def step_order(self):
        self.run_cmds('order', [self.tool('carve', 'order', 'config.json')])

    def measure_flags(self):
        # every failing file in one run, not one per ~12 min round (oaiq-051), as the build does
        flags = list(self.p.get('measure_flags') or [])
        if '--keep-going' not in flags:
            flags.append('--keep-going')
        if '--jobs' not in flags:
            flags += ['--jobs', str(self.p.get('measure_jobs', MEASURE_JOBS))]
        return flags

    def step_measure(self):
        if self.streams_bundles():
            return self.stream_bundles()
        kinds = ['--kinds', 'bundle,statement'] if self.overlap() else []
        self.run_cmds('measure', [self.tool('carve_measure', 'config.json', *self.measure_flags(), *kinds)])

    def streams_bundles(self):
        """Overlap mode with --publish: bundles and statements go to the publisher as they are measured
        (pipeline.json `stream_bundles`: false turns it off)."""
        return bool(self.overlap() and self.p.get('go') and self.p.get('stream_bundles', True))

    def stream_bundles(self):
        """`measure` with --publish: the bundles and statements are measured in batches of STREAM_BATCH, in
        publish order, and after each batch those that measured within the limits (calibration's, and the
        import limit unless `accept_heavy_imports`), whose bundles and statements went before them, go to a
        background publisher at once (release_items), frozen as they go (freeze_released). dbenbenn
        2026-11-07: q153's re-carve measured 1,699 bundles and 2,893 statements for ~6 h before sending one;
        "streaming bundles is a good idea, as we could catch problems earlier ... At worst, frozen just
        means we have to use a different name". The gates that read only the generated files (publish_prep,
        prose, check_text) run once after the first batch; dryrun keeps its step (the publisher's own
        reconcile does its lookups first). Until STREAM_SAMPLE bundles are measured nothing goes, and while
        nothing is published a systematic overrun (as calibrate judges it) releases nothing, so calibrate
        can still re-plan the whole carve. Whatever is over a limit stays back for calibrate, which splits it
        alone; its importers were held with it. A batch that fails does not stop the others; the closing full
        carve_measure run (cached) reports what failed, as before."""
        cfg = self.read_config() or {}
        plan = json.load(open(self.work_paths(cfg)[1]))
        from . import carve as CV
        ext = set(plan.get('external') or ())
        live = self.live_items()
        kinds = ('bundle', 'statement', 'piece') if self.p.get('stream_pieces', True) else ('bundle', 'statement')
        todo = [x for w in CV.publish_order(plan, ext)['waves'] for x in w
                if x.split(':', 1)[0] in kinds and x not in live and
                not (x.startswith('statement:') and x.split(':', 1)[1] in ext)]
        n = int(self.p.get('stream_batch') or STREAM_BATCH)
        batches = [todo[i:i + n] for i in range(0, len(todo), n)]
        print('== measure: %d %s to measure in %d batch(es), each released as it passes'
              % (len(todo), 'item(s)' if 'piece' in kinds else 'bundle(s) and statement(s)', len(batches)), flush=True)
        done, gates = set(), None
        for k, batch in enumerate(batches):
            try:
                self.run_cmds('measure', [self.tool('carve_measure', 'config.json', *self.measure_flags(),
                                                    '--kinds', ','.join(kinds), '--only', ','.join(batch))])
            except StepFailed as e:
                print('== measure: batch %d/%d had failures (reported at the end): %s'
                      % (k + 1, len(batches), str(e).splitlines()[0]), flush=True)
            done |= set(batch)
            if gates is None:
                gates = self.stream_gates()
            gates = self.gates_result(gates)
            if gates is True and self.stream_sample_ready(plan, done | live):
                why = self.release_items(done)
                # every piece measured so far: those of batches measured while check_text ran go now too
                pieces = sorted(x for x in done if x.startswith('piece:'))
                if pieces:
                    # each proof right behind its statement (dbenbenn 2026-11-07: "rather than waiting until all
                    # the bundles are live"); a slow or failed one stays for calibrate_pieces, as before
                    why = '; '.join(w for w in (why, self.release_measured(pieces, gated=True)) if w)
            elif gates is False:
                why = 'none released (a gate failed)'
            elif gates is True:
                why = 'none released yet (the first %d bundles are measured first)' % STREAM_SAMPLE
            else:
                why = 'none released yet (check_text runs)'
            print('== measure: batch %d/%d measured; %s' % (k + 1, len(batches), why or 'none released'), flush=True)
            if self.stream_memory_split():
                if isinstance(gates, subprocess.Popen) and gates.poll() is None:
                    gates.terminate()           # check_text runs again with the restarted measure
                    gates.wait()
                return
        if todo:
            gates = self.gates_result(self.stream_gates() if gates is None else gates, wait=True)
            if gates is True:
                print('== measure: %s' % (self.release_items(done) or 'none released'), flush=True)
                pieces = sorted(x for x in done if x.startswith('piece:'))
                if pieces:
                    print('== measure: %s' % (self.release_measured(pieces, gated=True) or 'no pieces released'), flush=True)
        # every bundle and statement once more, from the cache: the failures compile again and stop the step
        # (a piece's stop measure_pieces, which finds the streamed ones measured)
        self.run_cmds('measure', [self.tool('carve_measure', 'config.json', *self.measure_flags(),
                                            '--kinds', 'bundle,statement')])
        self.save()

    def stream_sample_ready(self, plan, done):
        """Are STREAM_SAMPLE of the plan's bundles (or all) measured in this run, or live already?"""
        names = [b['name'] for b in plan.get('bundles') or ()]
        return sum(1 for n in names if 'bundle:' + n in done) >= min(STREAM_SAMPLE, len(names))

    def stream_gates(self):
        """publish_prep and prose on the whole plan now (they read the generated files, not the times; seconds),
        and check_text started beside the measure (q153: 22 min over 4,592 items, which held the first release
        back): returns its Popen, which gates_result follows. False when one fails: the measure goes on
        releasing nothing, and the step itself stops later as it would have."""
        try:
            self.step_publish_prep()
            self.step_prose()
        except StepFailed as e:
            print('== measure: not streaming to the publisher, a gate failed (its step stops later): %s'
                  % str(e).splitlines()[0], flush=True)
            return False
        log = os.path.join(self.d, 'logs', 'check_text.log')
        kinds = 'bundle,statement,piece' if self.p.get('stream_pieces', True) else 'bundle,statement'
        cmd = self.tool('carve_prep', 'check-text', os.path.join(self.d, 'publish'), '--kinds', kinds)
        f = open(log, 'a')
        f.write('==== %s check_text (skill %s; beside the streaming measure)\n$ %s\n'
                % (_now(), os.path.basename(self.snap), ' '.join(cmd)))
        f.flush()
        proc = subprocess.Popen(cmd, cwd=self.d, env=self.env(), stdout=f, stderr=subprocess.STDOUT)
        proc._log = (f, log)
        return proc

    def gates_result(self, gates, wait=False):
        """True or False once the background check_text (stream_gates) has ended, else the process itself."""
        if not isinstance(gates, subprocess.Popen):
            return gates
        rc = gates.wait() if wait else gates.poll()
        if rc is None:
            return gates
        f, log = gates._log
        if rc:
            f.write('(exit %d)\n' % rc)
        f.close()
        if rc:
            print('== measure: not streaming to the publisher, check_text failed (its step stops later); log %s'
                  % log, flush=True)
            return False
        return True

    def stream_base_stubs(self, plan):
        """The statements a streaming measure may release: those of the plan streaming began with
        (pipeline_state.json `streamed_stubs`). A statement a later re-plan or piece split added waits for its
        pieces' CoeT check, as publish_early's held statements do (q160). Before anything is frozen, all of
        them; once a carve froze without streaming, none (they go with publish_early)."""
        if 'streamed_stubs' in self.state:
            return set(self.state['streamed_stubs'])
        if (self.state.get('auto_config') or {}).get('frozen'):
            return set()
        return set(plan.get('stubs') or {})

    def release_items(self, done):
        """Release to the background publisher the bundles and statements of `done` (measured in this run)
        that measured ok within the limits and whose own bundles and statements are released or live
        (stream_bundles). Their files go to publish/out/lib as measured (a repair or dropped edge rewrites
        them), they are frozen (freeze_released), and publish/release.json lists them with `open`; a
        streaming publisher (run_stream.json) is started when none runs. Returns a line for the log."""
        got = self.calibrate_inputs()
        if not got:
            return ''
        cfg, plan, times, fz, _ = got
        P = os.path.join(self.d, 'publish')
        pplan = os.path.join(P, 'plan.json')
        if not os.path.exists(pplan):
            return ''
        sha = hashlib.sha1(open(pplan, 'rb').read()).hexdigest()
        if sha != hashlib.sha1(open(self.work_paths(cfg)[1], 'rb').read()).hexdigest():
            return 'not released: publish/plan.json is not the measured plan'
        res = calibration(dict(plan, pieces={}), times, cfg.get('time_scale', 1.5), cfg.get('budget', 55), fz,
                          accepted=self.p.get('accept_over') or (), rss_limit=self.rss_limit())
        bad = {k for k, _, _ in res['over']} | {k for k, _ in res['statements_over']}
        if not self.p.get('accept_heavy_imports'):
            bad |= {k for k, _ in heavy_imports(plan, times, fz, kinds=('bundle', 'statement'))}
        over_b = [k for k, _, _ in res['over'] if k.startswith('bundle:') and k in done]
        measured_b = sum(1 for b in plan.get('bundles') or ()
                         if 'bundle:' + b['name'] in done and (times.get('bundle:' + b['name']) or {}).get('ok'))
        if not self.anything_published(cfg) and len(over_b) >= UNIFORM_MIN and \
                len(over_b) >= SYSTEMATIC_FRACTION * measured_b:
            return ('none released: %d of %d measured bundles over the limit, a systematic cost-model error '
                    'calibrate re-plans' % (len(over_b), measured_b))
        from . import carve as CV
        ext = set(plan.get('external') or ())
        order = CV.publish_order(plan, ext)
        live = self.live_items()
        rel_path = os.path.join(P, 'release.json')
        old = _load_json(rel_path) or {}
        prev = set(old.get('items') or ()) if old.get('plan_sha') == sha and isinstance(old.get('items'), list) else set()
        if old.get('plan_sha') == sha and old.get('items') == 'all':
            return ''
        base = self.stream_base_stubs(plan)
        ok = set(prev)

        def fine(d):
            kind, n = d.split(':', 1)
            return kind == 'piece' or n in ext or d in ok or d in live

        for x in (x for w in order['waves'] for x in w):
            kind, n = x.split(':', 1)
            if kind not in ('bundle', 'statement') or n in ext or x in ok or x in live or x not in done or x in bad:
                continue
            # a statement a split added goes once its own piece measured ok in this run: that is the CoeT check
            # publish_early's hold waits for (q160). q153 2026-11-08: held to the measure's end, 1,251 released
            # pieces importing such statements could not be verified
            if kind == 'statement' and n not in base and not (
                    'piece:' + n in done and (times.get('piece:' + n) or {}).get('ok')):
                continue
            if (times.get(x) or {}).get('ok') and all(fine(d) for d in order['deps'].get(x, ())):
                ok.add(x)
        new = ok - prev
        if not new:
            return ''
        src, dst = os.path.join(self.gen_out(), 'lib'), os.path.join(P, 'out', 'lib')
        os.makedirs(dst, exist_ok=True)
        for f in sorted(plan_lib_files(self.only_items(plan, new))):
            if os.path.exists(os.path.join(src, f)):
                data = open(os.path.join(src, f), 'rb').read()
                q = os.path.join(dst, f)
                if not os.path.exists(q) or open(q, 'rb').read() != data:
                    open(q + '.tmp', 'wb').write(data)
                    os.replace(q + '.tmp', q)
        self.freeze_released(plan, ok | live)
        self.write_release(sha, items=sorted(ok), open=True)
        if self.publisher_running():
            how = 'the background publisher sends them'
        else:
            self.start_publisher(gated=True)
            how = 'a streaming publisher was started'
        return 'released %d bundle(s)/statement(s) (%d in all; %s)' % (len(new), len(ok), how)

    @staticmethod
    def only_items(plan, items):
        """The plan with only the bundles and statements of `items` (external statements kept)."""
        ext = set(plan.get('external') or ())
        return dict(plan, bundles=[b for b in plan.get('bundles') or () if 'bundle:' + b['name'] in items],
                    stubs={n: v for n, v in (plan.get('stubs') or {}).items() if 'statement:' + n in items or n in ext})

    def freeze_released(self, plan, items):
        """Freeze what a streaming measure released, as freeze_published does for the whole plan:
        published/plan.json holds the plan with only those bundles and statements, published/lib their
        files, and config `frozen` (those bundles), `forced` and `template_forced` (those statements). What is
        not released stays free: calibrate may split it alone. The first call records the plan's statements
        (`streamed_stubs`, stream_base_stubs)."""
        P = os.path.join(self.d, 'publish')
        dst = self.published_dir()
        os.makedirs(os.path.join(dst, 'lib'), exist_ok=True)
        was = _load_json(os.path.join(dst, 'plan.json')) or {}       # what is frozen stays frozen
        items = set(items) | {'bundle:' + b['name'] for b in was.get('bundles') or ()} | \
            {'statement:' + n for n in was.get('stubs') or {}}
        part = self.only_items(plan, items)
        tmp = os.path.join(dst, 'plan.json.tmp')
        json.dump(part, open(tmp, 'w'), indent=1)
        os.replace(tmp, os.path.join(dst, 'plan.json'))
        lib = os.path.join(P, 'out', 'lib')
        for f in sorted(plan_lib_files(part)):
            if os.path.exists(os.path.join(lib, f)):
                shutil.copy(os.path.join(lib, f), os.path.join(dst, 'lib', f))
        ext = set(plan.get('external') or ())
        stubs = {n for n in part.get('stubs') or {} if n not in ext}
        named = set(self.p.get('forced') or ()) | set((self.p.get('config_set') or {}).get('forced') or ())
        self.mark_publishing('the streaming measure released bundles and statements')
        self.state.setdefault('streamed_stubs', sorted(n for n in plan.get('stubs') or {} if n not in ext))
        a = self.state.setdefault('auto_config', {})
        a['frozen'] = {'plan': os.path.join(dst, 'plan.json'), 'bundles': [b['name'] for b in part['bundles']],
                       'lib': os.path.join(dst, 'lib')}
        a['forced'] = sorted(set(a.get('forced') or ()) | stubs)
        a['template_forced'] = sorted(set(a.get('template_forced') or ()) | (stubs - named))
        json.dump(self.apply_auto(self.read_config() or {}), open(os.path.join(self.d, 'config.json'), 'w'), indent=1)
        self.save()

    def write_release(self, sha=None, **fields):
        """Update publish/release.json for the plan `sha` (publish/plan.json's by default): a release for
        another plan is replaced, else its other fields are kept."""
        path = os.path.join(self.d, 'publish', 'release.json')
        if sha is None:
            sha = hashlib.sha1(open(os.path.join(self.d, 'publish', 'plan.json'), 'rb').read()).hexdigest()
        old = _load_json(path) or {}
        rel = dict(old) if isinstance(old, dict) and old.get('plan_sha') == sha else {'plan_sha': sha}
        rel.update(fields)
        rel['released'] = _now()
        tmp = path + '.tmp'
        json.dump(rel, open(tmp, 'w'), indent=1)
        os.replace(tmp, path)
        return rel

    def step_measure_pieces(self):
        if self.p.get('go'):
            return self.stream_pieces()
        self.run_cmds('measure_pieces', [self.tool('carve_measure', 'config.json', *self.measure_flags(),
                                                   '--kinds', 'piece')])
        self.save()

    def stream_pieces(self):
        """With --publish: the pieces are measured in batches of STREAM_BATCH and each batch's pieces that
        measured within the limit are released to the background publisher at once (release_measured), so
        verifier feedback arrives within the hour instead of after every piece is measured (dbenbenn
        2026-11-06: q153 measured ~3,000 pieces for a day before sending one). First the pieces the rest
        waits for: those of the statements bundles import (gate_pieces, q153: bundles had stalled ~10 h)
        and of the statements publish_early held (new since the published plan: they go once their pieces
        pass the CoeT check, q160). A batch that fails does not stop the others; the closing full
        carve_measure run (cached, so only the failures compile again) reports what failed, as before."""
        held = self.state.get('publish_held')
        live = self.live_items()
        first = self.gate_pieces() + ['piece:' + n for n in (held or {}).get('statements') or ()
                                      if 'piece:' + n not in live]
        first = list(dict.fromkeys(first))
        got = self.calibrate_inputs()
        plan = got[1] if got else {}
        rest = sorted('piece:' + n for n in (plan.get('pieces') or {})
                      if 'piece:' + n not in live and 'piece:' + n not in first)
        batches = [first[i:i + STREAM_BATCH] for i in range(0, len(first), STREAM_BATCH)] + \
            [rest[i:i + STREAM_BATCH] for i in range(0, len(rest), STREAM_BATCH)]
        print('== measure_pieces: %d piece(s) to measure in %d batch(es), each released as it passes'
              % (len(first) + len(rest), len(batches)), flush=True)
        try:
            for k, batch in enumerate(batches):
                if not batch:
                    continue
                try:
                    self.run_cmds('measure_pieces', [self.tool('carve_measure', 'config.json', *self.measure_flags(),
                                                               '--kinds', 'piece', '--only', ','.join(batch))])
                except StepFailed as e:
                    print('== measure_pieces: batch %d/%d had failures (reported at the end): %s'
                          % (k + 1, len(batches), str(e).splitlines()[0]), flush=True)
                self.publish_held_if_measured()
                print('== measure_pieces: batch %d/%d measured; %s' % (k + 1, len(batches),
                                                                     self.release_measured(batch) or 'none released'),
                      flush=True)
        finally:
            self.close_release()
        # every piece once more, from the cache: the failures compile again and stop the step, as before
        self.run_cmds('measure_pieces', [self.tool('carve_measure', 'config.json', *self.measure_flags(),
                                                   '--kinds', 'piece')])
        self.publish_held_if_measured(final=True)
        self.save()

    def publish_held_if_measured(self, final=False):
        """publish_early held new statements until their pieces are measured (held_statements, q160): once all
        of them measured ok, the held publish_early goes now (it started no publisher)."""
        held = self.state.get('publish_held')
        if not held:
            return
        got = self.calibrate_inputs()
        times = got[2] if got else {}
        if not final and not all((times.get('piece:' + n) or {}).get('ok') for n in held.get('statements') or ()):
            return
        self.state.pop('publish_held', None)
        print('== measure_pieces: the pieces of the %d statement(s) publish_early held passed; publishing them '
              'now' % len(held.get('statements') or ()), flush=True)
        if self.publisher_running() and not self.gated_publisher():
            print('== a publisher already runs on this carve; it goes on (new items wait for the final publish)',
                  flush=True)
        else:
            self.publish_early_now()
        self.save()

    def release_measured(self, items, gated=False):
        """Release the pieces of `items` that measured ok within the limit to the background publisher, without
        the full pieces' gates (pieces_prep runs them before the final publish): each solution file goes to
        publish/out/solutions as measured, and publish/release.json, for this plan, lists them with `open`
        (split_run keeps waiting for more while it is). A publisher is started when none runs and publish_early
        has frozen the published part. Returns a line for the log ('' when nothing goes)."""
        if not self.p.get('go'):
            return ''
        got = self.calibrate_inputs()
        if not got:
            return ''
        cfg, plan, times, _, _ = got
        limit = max(cfg.get('budget', 55) * LIMIT_FACTOR, PIECE_CAP)
        accepted = set(self.p.get('accept_over') or ())
        trying = {'piece:' + n for n in self.trying_pieces()}
        fast = sorted(x for x in items if (times.get(x) or {}).get('ok') and (fits_memory(times[x], self.rss_limit()) or x in trying) and
                      ((times[x].get('secs') or 0) <= limit or (x in accepted and times[x]['secs'] <= ACCEPT_CAP)))
        P = os.path.join(self.d, 'publish')
        pplan = os.path.join(P, 'plan.json')
        if not fast or not os.path.exists(pplan):
            return ''
        sha = hashlib.sha1(open(pplan, 'rb').read()).hexdigest()
        if sha != hashlib.sha1(open(self.work_paths(cfg)[1], 'rb').read()).hexdigest():
            return 'not released: publish/plan.json is not the measured plan (publish_prep runs again first)'
        from . import carve as CV
        src, dst = os.path.join(self.gen_out(), 'solutions'), os.path.join(P, 'out', 'solutions')
        os.makedirs(dst, exist_ok=True)
        for x in fast:
            f = 'Sol_%s.lean' % CV.slug(CV.statement_name(plan, x.split(':', 1)[1]))
            if os.path.exists(os.path.join(src, f)):
                data = open(os.path.join(src, f), 'rb').read()
                q = os.path.join(dst, f)
                if not os.path.exists(q) or open(q, 'rb').read() != data:
                    tmp = q + '.tmp'
                    open(tmp, 'wb').write(data)
                    os.replace(tmp, q)
        rel_path = os.path.join(P, 'release.json')
        old = _load_json(rel_path) or {}
        pieces = set(fast)
        if old.get('plan_sha') == sha and isinstance(old.get('pieces'), list):
            pieces |= set(old['pieces'])
        if old.get('plan_sha') == sha and old.get('pieces') == 'all':
            return ''
        self.write_release(sha, pieces=sorted(pieces), open=True)
        if self.publisher_running():
            how = 'the background publisher sends them'
        elif not (self.state.get('auto_config') or {}).get('frozen') or (not gated and self.held_statements()):
            how = 'no publisher yet (publish_early has not started one)'
        else:
            # the streaming measure's (gated): it sends only what release.json lists, so held statements stay held.
            # q153 2026-11-08: with the publisher stopped by hand, batches releasing 174-206 pieces each started none
            self.start_publisher(gated=gated)
            how = 'a background publisher was started'
        return 'released %d piece(s) (%d in all; %s)' % (len(fast), len(pieces), how)

    def close_release(self):
        """The streaming release is complete: `open` off, so the publisher ends once it has sent it."""
        path = os.path.join(self.d, 'publish', 'release.json')
        rel = _load_json(path)
        if isinstance(rel, dict) and rel.get('open'):
            rel['open'] = False
            tmp = path + '.tmp'
            json.dump(rel, open(tmp, 'w'), indent=1)
            os.replace(tmp, path)

    def gate_pieces(self):
        """The pieces bundles wait for, not yet live: a bundle may import a statement only once it is Proved,
        so every piece of that statement's proof closure (carve.publish_order's bundle dependencies) gates it.
        ['piece:NODE', ...], the earliest bundle's first. q153 (2026-11-06): only the bundles' own statements
        were taken, 2 pieces, while bundles E125 and E237 (and the goal's bundle behind them) waited on 694."""
        got = self.calibrate_inputs() or (None,)
        cfg = got[0] or json.load(open(os.path.join(self.d, 'config.json')))
        _, plan_path, _ = self.work_paths(cfg)
        if not os.path.exists(plan_path):
            return []
        plan = json.load(open(plan_path))
        live = self.live_items()
        from . import carve as CV
        order = CV.publish_order(plan, plan.get('external', ()))
        out = []
        for wave in order['waves']:
            for x in wave:
                if x.startswith('bundle:') and x not in live:
                    out += [d for d in order['deps'][x] if d.startswith('piece:') and d not in live]
        return list(dict.fromkeys(out))

    def work_paths(self, cfg):
        work = os.path.expanduser(cfg.get('work') or os.path.join(self.d, 'carve_work'))
        plan_path = os.path.expanduser(cfg.get('plan') or os.path.join(work, 'plan.json'))
        return work, plan_path, os.path.join(work, 'times.json')

    STATEMENT_OVER_MSG = (
        "step 'calibrate': statement module(s) over the %.0f s limit: %s. A statement publishes, but every "
        "verify that imports it compiles its module and times out (opus-kadison, oaiq-039), and re-planning "
        "cannot shrink one. Profile it (`lean -o x.olean -Dprofiler=true`): if `.olean serialization` "
        "dominates, the statement's type is huge; name its large sides or subterms with `abbrev`s in a "
        "bundle (only declaration types cost, a definition's value is cheap) and state it with them "
        "(references/openai-ports.md \"Slow or odd failures\"); log %s")

    PIECE_HINT = (
        "Find what is slow before splitting. (1) Compile the piece's check file with "
        "`lean -o x.olean -Dprofiler=true`: if `.olean serialization` dominates while elaboration is fast, "
        "the statement's type is huge (oaiq-075: 316 s of 341 s, a term re-embedded thousands of times); "
        "name its large sides or subterms with `abbrev`s in a bundle and state it with them (declaration types cost, a definition's value is cheap; opus-kadison), do not split. (2) Else "
        "`-Dtrace.profiler=true -Dtrace.profiler.threshold=20000` shows the slow declaration or tactic "
        "(oaiq-074: one fun_prop goal, 53 s). (3) Kernel computation (`decide +kernel`, `native_decide`) or "
        "plain bulk: force the heavy lemmas into statements, listing them in pipeline.json `forced` (a private "
        "one by its graph node name, `_private.<module>.0.<name>`), then --from config (oaiq-031: one 192 s "
        "piece became 20 pieces of ~11 s).")

    UNSHRINKABLE_MSG = (
        "step '%s': bundle(s) over the %.0f s limit that splitting cannot shrink (down to one declaration, or a "
        "split returned it unchanged), so no further split round was spent; each was profiled once "
        "(carve_measure --profile, logs <work>/profile_*.log):\n  %s\n"
        "Fix it at the source (a post-carve patch, config_set.patches, or a port patch), then --from gen; "
        "or excuse it below %d s with pipeline.json `accept_over` [\"bundle:NAME\"]. Log %s")

    def unshrinkable(self, plan, names):
        """Which of the over-limit bundles `names` splitting cannot shrink: down to one declaration, or the
        same declarations a split round (or re-plan) already had (oaiq-124: `--only` returned
        OAIQ124K032 unchanged twice; one 7-line theorem, 91 s of 92 in .olean serialization)."""
        seen = {tuple(v) for v in (self.state.get('bundle_split_nodes') or {}).values()}
        by = {b['name']: b for b in plan.get('bundles', [])}
        out = []
        for n in names:
            nodes = tuple(sorted(by.get(n, {}).get('nodes') or ()))
            if len(nodes) == 1 or (nodes and nodes in seen):
                out.append(n)
        return out

    def remember_split(self, plan, names):
        """Record the declarations of the bundles a split round (or re-plan) is about to cut."""
        rec = self.state.setdefault('bundle_split_nodes', {})
        for b in plan.get('bundles', []):
            if b['name'] in names and b.get('nodes'):
                rec[b['name']] = sorted(b['nodes'])

    def profile_bundles(self, cfg, names, times):
        """{name: diagnosis} of each bundle by Lean's profiler (carve_measure --profile, one compile
        each; a profile of the same text is reused), for a bundle splitting cannot shrink: serialization-
        or kernel-bound, naming the declaration (oaiq-124, oaiq-092)."""
        work, _, _ = self.work_paths(cfg)
        path = os.path.join(work, 'profiles.json')

        def load():
            try:
                return json.load(open(path))
            except (OSError, ValueError):
                return {}
        have = load()
        todo = [n for n in names if not (have.get('bundle:' + n) and (times.get('bundle:' + n) or {}).get('key')
                                         and have['bundle:' + n].get('key') == times['bundle:' + n]['key'])]
        if todo:
            flags = list(self.p.get('measure_flags') or [])
            extra = ['--dir', flags[flags.index('--dir') + 1]] if '--dir' in flags else []
            self.run_cmds('calibrate', [self.tool('carve_measure', 'config.json', *extra, '--profile',
                                                  ','.join('bundle:' + n for n in todo))])
            have = load()
        return {n: (have.get('bundle:' + n) or {}).get('message') or 'no profile recorded (see logs/calibrate.log)'
                for n in names}

    def stop_unshrinkable(self, cfg, plan, times, res, stuck, lines, step):
        diag = self.profile_bundles(cfg, stuck, times)
        secs = {k.split(':', 1)[1]: v for k, v, _ in res['over'] if k.startswith('bundle:')}
        found = ['%s (%.0f s): %s' % (n, secs.get(n, 0), diag[n]) for n in stuck]
        log = self.calibrate_log(lines + ['  cannot shrink: ' + x for x in found])
        raise StepFailed(self.UNSHRINKABLE_MSG % (step, res['limit'], '\n  '.join(found), ACCEPT_CAP, log))

    def calibrate_inputs(self):
        cfg = json.load(open(os.path.join(self.d, 'config.json')))
        work, plan_path, times_path = self.work_paths(cfg)
        if not (os.path.exists(plan_path) and os.path.exists(times_path)):
            return None                                            # nothing was measured
        frozen = cfg.get('frozen') or {}
        fz = list(frozen.get('bundles') or ())
        fp = os.path.expanduser(frozen.get('plan') or '')
        if fp and os.path.exists(os.path.join(self.d, fp)):
            fz += list((json.load(open(os.path.join(self.d, fp))).get('stubs') or {}))   # live statements
        return cfg, json.load(open(plan_path)), json.load(open(times_path)), fz, times_path

    def calibrate_log(self, lines):
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        os.makedirs(os.path.dirname(log), exist_ok=True)
        open(log, 'a').write('\n'.join(lines) + '\n')
        return log

    def calibrate_head(self, cfg, res, what=''):
        lines = ['%s: %smeasured %d items against budget %g (limit %.0f s, unpublished bundles %.0f s), slowest %s' % (
            _now(), what, res['measured'], cfg.get('budget', 55), res['limit'], res.get('bundle_limit', res['limit']),
            res['slowest'])]
        for key, secs, cost in res['over']:
            lines.append('  over: %s measured %.0f s, planned %.0f s' % (key, secs, cost))
        return lines

    def chain_warnings(self, plan, times, res, frozen):
        """chain_lines, its WARNING lines also on stderr (they never stop the step)."""
        lines = chain_lines(plan, times, res, frozen)
        for l in lines:
            if 'WARNING' in l:
                print('calibrate:%s' % l, file=sys.stderr, flush=True)
        return lines

    def step_calibrate(self):
        got = self.calibrate_inputs()
        if got is None:
            return 'skipped'
        cfg, plan, times, fz, times_path = got
        if self.overlap():
            return self.calibrate_frozen_part(cfg, plan, times, fz, times_path)
        res = calibration(plan, times, cfg.get('time_scale', 1.5), cfg.get('budget', 55), fz,
                          accepted=self.p.get('accept_over') or (), rss_limit=self.rss_limit())
        lines = self.calibrate_head(cfg, res) + self.chain_warnings(plan, times, res, fz)
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        if res['statements_over']:
            self.calibrate_log(lines + ['  statement over: %s measured %.0f s' % x for x in res['statements_over']])
            raise StepFailed(self.STATEMENT_OVER_MSG % (
                res['limit'], ', '.join('%s (%.0f s)' % x for x in res['statements_over']), log))
        if not res['over']:
            self.calibrate_log(lines + ['fits the model; time_scale %g kept' % cfg.get('time_scale', 1.5)])
            return None
        over_b = [k.split(':', 1)[1] for k, _, _ in res['over'] if k.startswith('bundle:')]
        stuck = self.unshrinkable(plan, over_b)
        if stuck and len(stuck) == len(res['over']):
            # a re-plan cannot shrink these either: say why they are slow instead (oaiq-124, oaiq-092)
            self.stop_unshrinkable(cfg, plan, times, res, stuck, lines, 'calibrate')
        self.remember_split(plan, over_b)
        pieces_only = all(k.startswith('piece:') for k, _, _ in res['over'])
        ratios = sorted(secs / max(cost, 1.0) for _, secs, cost in res['over'])
        uniform = (pieces_only and len(ratios) >= UNIFORM_MIN and ratios[len(ratios) // 2] >= UNIFORM_RATIO
                   and ratios[-1] <= 2 * ratios[0])
        if pieces_only and not uniform:
            # one slow piece (or a scatter) is something specific, which re-planning has never shrunk
            # (KMedian 106 s through two re-plans, oaiq-031 192 s): stop and say how to find it
            self.calibrate_log(lines)
            raise StepFailed(
                "step 'calibrate': only pieces are over the limit, and re-planning does not shrink a piece:\n%s\n%s Log %s"
                % ('\n'.join(lines[1:]), self.PIECE_HINT, log))
        if uniform:
            # several pieces over plan by a similar large factor: the model underestimates this port, and a
            # re-plan at that factor promotes lemmas to statements (oaiq-073: ratio 3.5-4.3, re-planned at 4,
            # all 364 items fitted)
            res['new_scale'] = round(min(MAX_SCALE, cfg.get('time_scale', 1.5) * ratios[len(ratios) // 2]), 1)
        self.replan(cfg, res['new_scale'], lines)

    def replan(self, cfg, new_scale, lines, step='calibrate'):
        """Raise time_scale and plan again from `plan` (at most MAX_REPLANS times)."""
        n = self.state.get('replans', 0)
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        if n >= MAX_REPLANS:
            self.calibrate_log(lines)
            raise StepFailed("step '%s': %d re-plans did not fit the budget; items over the limit:\n%s\n"
                             "split by hand (carve.py split) or raise time_scale; log %s" % (step, n, '\n'.join(lines[1:]), log))
        lines.append('re-planning %d/%d: time_scale %g -> %g' % (n + 1, MAX_REPLANS, cfg.get('time_scale', 1.5),
                                                               new_scale))
        self.calibrate_log(lines)
        cfg['time_scale'] = new_scale
        json.dump(cfg, open(os.path.join(self.d, 'config.json'), 'w'), indent=1)
        self.state['replans'] = n + 1
        # work/repairs.json keys its cuts by file name, and a re-plan renumbers the bundles: the old
        # cuts would be re-applied to other files (oaiq-039: bundle 30 lost two imports it needs)
        rp = os.path.join(os.path.expanduser(cfg.get('work') or os.path.join(self.d, 'carve_work')), 'repairs.json')
        if os.path.exists(rp):
            os.replace(rp, rp.replace('repairs.json', 'repairs.before-replan-%d.json' % (n + 1)))
        self.invalidate('plan')
        self.restart = True
        print('%s: %s' % (step, lines[-1]), file=sys.stderr, flush=True)

    # -- overlap mode: calibrating the part that freezes, then the pieces -------------------------
    def anything_published(self, cfg):
        """Has any item of this carve (or of a carve it extends: config `frozen`) gone to the platform?"""
        return self.publishing_started() or bool((cfg.get('frozen') or {}).get('bundles'))

    def calibrate_frozen_part(self, cfg, plan, times, fz, times_path):
        """Overlap mode, `calibrate`: the bundles and statements only (pieces are measured after).
        A statement over the limit stops, as ever. Bundles over it: a systematic cost-model error (at
        least UNIFORM_MIN and SYSTEMATIC_FRACTION of the measured bundles) re-plans globally at a
        larger time_scale, but only while nothing is published; otherwise each slow bundle is split
        alone (`carve.py split --only`), every other bundle kept, so only the files importing it
        change and are measured again (dbenbenn 2026-10-29: oaiq-081's bundle 22 of 194 re-planned the
        whole carve)."""
        part = dict(plan, pieces={})
        res = calibration(part, times, cfg.get('time_scale', 1.5), cfg.get('budget', 55), fz,
                          accepted=self.p.get('accept_over') or (), rss_limit=self.rss_limit())
        lines = self.calibrate_head(cfg, res, 'bundles and statements: ') + self.chain_warnings(plan, times, res, fz)
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        heavy = heavy_imports(plan, times, fz, kinds=('bundle', 'statement'))
        if heavy and not self.p.get('accept_heavy_imports'):
            self.calibrate_log(lines + ['  imports over %.0f MB: %s %.0f MB' % (IMPORT_LIMIT / 1e6, x, mb) for x, mb in heavy])
            raise StepFailed(
                "step 'calibrate': %d bundle(s)/statement(s) import more than %.0f MB of .olean, where the verifier's "
                "workers run out of memory (q153): %s. Every proof importing them pays the same. Usually a bundle mixes "
                "unrelated declarations: re-plan with config_set `chunker`: \"closure\" (and a smaller `closure_slack`), "
                "or split the heavy bundle; pipeline.json `accept_heavy_imports`: true publishes as is. Log %s"
                % (len(heavy), IMPORT_LIMIT / 1e6, ', '.join('%s (%.0f MB)' % x for x in heavy[:10]), log))
        if res['statements_over']:
            self.calibrate_log(lines + ['  statement over: %s measured %.0f s' % x for x in res['statements_over']])
            raise StepFailed(self.STATEMENT_OVER_MSG % (
                res['limit'], ', '.join('%s (%.0f s)' % x for x in res['statements_over']), log))
        if not res['over']:
            self.calibrate_log(lines + ['fits the model; time_scale %g kept' % cfg.get('time_scale', 1.5)])
            return None
        measured = sum(1 for b in plan.get('bundles', []) if (times.get('bundle:' + b['name']) or {}).get('ok'))
        names = [k.split(':', 1)[1] for k, _, _ in res['over']]
        stuck = self.unshrinkable(plan, names)
        if stuck and len(stuck) == len(names):
            # one declaration, or a split that returned it unchanged: profile once and say why, rather than
            # spend more split rounds (oaiq-124: two more rounds on a serialization-bound 7-line theorem)
            self.stop_unshrinkable(cfg, plan, times, res, stuck, lines, 'calibrate')
        if stuck:
            lines.append('splitting cannot shrink %s: left over until the others fit, then profiled' % ', '.join(stuck))
            names = [x for x in names if x not in stuck]
        systematic = len(names) >= UNIFORM_MIN and len(names) >= SYSTEMATIC_FRACTION * measured
        if systematic and not self.anything_published(cfg):
            self.remember_split(plan, names)
            return self.replan(cfg, res['new_scale'], lines)
        n = self.state.get('bundle_splits', 0)
        if n >= MAX_BUNDLE_SPLITS:
            self.calibrate_log(lines)
            raise StepFailed("step 'calibrate': %d rounds of splitting single bundles left these over the limit:\n%s\n"
                             "split by hand (carve.py split CONFIG TIMES --limit S --only NAME) or look at what is "
                             "slow in them (lean -Dprofiler=true); log %s" % (n, '\n'.join(lines[1:]), log))
        lines.append('splitting %s alone (round %d/%d; %s): every other bundle kept, its importers regenerated' % (
            ', '.join(names), n + 1, MAX_BUNDLE_SPLITS,
            'published items are frozen' if self.anything_published(cfg) else
            '%d of %d bundles over: no systematic error' % (len(names), measured)))
        self.calibrate_log(lines)
        self.remember_split(plan, names)
        self.run_cmds('calibrate', [self.tool('carve', 'split', 'config.json', times_path, '--limit',
                                              '%g' % cfg.get('budget', 55), '--only', ','.join(names))])
        self.state['bundle_splits'] = n + 1
        self.invalidate('gen')
        self.restart = True
        print('calibrate: %s' % lines[-1], file=sys.stderr, flush=True)

    # -- splitting single pieces ------------------------------------------------------------------
    def piece_split_rounds(self, n):
        return len((self.state.get('piece_splits') or {}).get(n) or ())

    def server_split_wanted(self):
        """{node: parts} for the pieces the publisher stopped in state `split` (own verifier timeouts,
        verdicts.decide) that have not had MAX_PIECE_SPLITS local splits yet: each is halved. Only while
        the piece's file is still the text that stopped (the state's `sha`, as split_run.file_sha): once it
        changed, it was split already and split_run sends it again when a publisher next starts."""
        try:
            st = json.load(open(os.path.join(self.d, 'publish', 'run_state.json')))
        except (OSError, ValueError):
            return {}
        plan = _load_json(os.path.join(self.d, 'publish', 'plan.json')) or {}
        from . import carve as CV
        out = {}
        for x, v in sorted(st.items()):
            n = x.split(':', 1)[1]
            if not (x.startswith('piece:') and v.get('state') == 'split') or self.piece_split_rounds(n) >= MAX_PIECE_SPLITS \
                    or n in (self.state.get('unsplittable') or {}):
                continue
            if v.get('sha') and n in (plan.get('pieces') or {}):
                slug = CV.slug(CV.statement_name(plan, n))
                f = os.path.join(self.gen_out(), 'solutions', 'Sol_%s.lean' % slug)
                if os.path.exists(f):
                    h = hashlib.sha1(open(f, 'rb').read())
                    cmp_ = os.path.join(self.d, 'publish', 'comparisons', slug + '.md')
                    if os.path.exists(cmp_):
                        h.update(b'\0' + open(cmp_, 'rb').read())
                    if h.hexdigest() != v['sha']:
                        continue
            out[n] = 2
        return out

    def split_pieces_locally(self, want, step, why):
        """Split each piece of `want` ({node: parts}) alone (carve.py split-piece: lemmas it keeps become new
        statements, only its own files and theirs are regenerated), then run again from `names`; every other
        measurement is cached, and gen is not re-run. dbenbenn 2026-11-06: q153's frozen global re-plan for
        four slow pieces changed ~2,000 other pieces (a day of measuring); `plan` and `gen` alone took 3 h.
        The new statements join auto_config `forced` (a later re-plan keeps them) and `template_forced`
        (mechanical prose). A stopped piece whose file changed is sent again by split_run itself
        (_restart_changed). Returns {node: [new nodes]}."""
        spec = ','.join('%s=%g' % (n, k) for n, k in sorted(want.items()))
        self.run_cmds(step, [self.tool('carve', 'split-piece', 'config.json', spec, '--skip-unsplittable')])
        self.check_published_unchanged(step)
        log = os.path.join(self.d, 'logs', step + '.log')
        line = [l for l in open(log, errors='replace').read().splitlines() if l.startswith('SPLIT_PIECES ')]
        if not line:
            raise StepFailed("step '%s': carve.py split-piece printed no SPLIT_PIECES line; log %s" % (step, log))
        done = json.loads(line[-1].split(' ', 1)[1])
        un = [l for l in open(log, errors='replace').read().splitlines() if l.startswith('UNSPLITTABLE_PIECES ')]
        if un:
            # nothing in them can be a statement: they go once as they are (trying_pieces), a person looks if rejected
            got = json.loads(un[-1].split(' ', 1)[1])
            self.state.setdefault('unsplittable', {}).update(got)
            if got:
                print('== %s: unsplittable, sent once as they are: %s' % (step, ', '.join(sorted(got))), flush=True)
        if not done:
            self.save()
            return done
        rec = self.state.setdefault('piece_splits', {})
        for n, new in done.items():
            rec.setdefault(n, []).append({'at': _now(), 'why': why % n if '%s' in why else why,
                                          'parts': want.get(n), 'new': new})
        new_all = sorted({m for v in done.values() for m in v})
        if new_all:
            a = self.state.setdefault('auto_config', {})
            a['forced'] = sorted(set(a.get('forced') or ()) | set(new_all))
            a['template_forced'] = sorted(set(a.get('template_forced') or ()) | set(new_all))
        cfg = self.apply_auto(self.read_config() or {})
        json.dump(cfg, open(os.path.join(self.d, 'config.json'), 'w'), indent=1)
        g = self.state['steps'].get('gen')
        if g and 'in' in g:
            # split-piece generated exactly the files that changed: gen stands for the new plan
            g['in']['plan'] = hash_paths([self.work_paths(cfg)[1]])
        self.invalidate('names')
        self.restart = True
        self.save()
        print('== %s: split alone: %s' % (step, '; '.join('%s -> %d new statement(s) %s' % (n, len(v), ', '.join(v))
                                                          for n, v in sorted(done.items()))), flush=True)
        return done

    def live_items(self):
        sp = os.path.join(self.d, 'publish', 'run_state.json')
        try:
            st = json.load(open(sp))
        except (OSError, ValueError):
            return set()
        return {x for x, v in st.items() if v.get('state') == 'live'}

    def rss_limit(self):
        """The piece memory limit for this carve: pipeline.json `piece_rss_limit`, else PIECE_RSS_LIMIT (q153
        2026-11-09: 39 pieces at 7,151-8,579 MiB all accepted, so the carve set 8,600)."""
        return int(self.p.get('piece_rss_limit') or PIECE_RSS_LIMIT)

    def trying_pieces(self):
        """Pieces sent whatever their measured peak: pipeline.json `try_over_memory` (a person's trial) and those
        split-piece found unsplittable (q153 2026-11-09). A memory kill of one leaves it for a person."""
        return set(self.p.get('try_over_memory') or ()) | set(self.state.get('unsplittable') or {})

    def memory_triage(self, plan, times, memory_over, tried):
        """calibration's `memory_over` pieces -> ([(node, rss, secs, parts)] to split automatically, [why] for a
        person): each into enough parts for the proof's share of the peak to fit beside the imports (its
        statement's own peak, memory_parts); a person when it was split already, its imports alone are over,
        or the plan records no declarations for it."""
        auto_mem, manual = [], []
        for key, rss, secs in memory_over:
            n = key.split(':', 1)[1]
            base = (times.get('statement:' + n) or {}).get('rss_mib')
            parts = memory_parts(rss, base)
            rounds = (tried.get(n) or {}).get('memory_rounds', 1 if n in tried else 0)
            if n in tried and (rounds >= MAX_MEMORY_ROUNDS or not tried[n].get('rss_mib')):
                manual.append('%s: %d MiB, still over the %d MiB memory limit after %d automatic split(s) (it was %s)' % (
                    key, rss, PIECE_RSS_LIMIT, max(rounds, 1), ('%d MiB' % tried[n]['rss_mib']) if tried[n].get('rss_mib')
                    else '%.0f s' % tried[n]['secs']))
            elif parts is None:
                manual.append('%s: %d MiB, and its statement alone peaks at %d MiB: the imports are over the %d MiB '
                              'memory limit, and no split helps (regroup the bundles it imports)' % (
                                  key, rss, base, PIECE_RSS_LIMIT))
            elif not (plan.get('pieces') or {}).get(n, {}).get('keep'):
                manual.append('%s: %d MiB, no declarations recorded for it in the plan' % (key, rss))
            else:
                auto_mem.append((n, rss, secs, parts))
        return auto_mem, manual

    def stream_memory_split(self):
        """While the measure streams: split the pieces measured over the verifier's memory so far, at once the first
        time and then at most every STREAM_SPLIT_MINUTES (each round re-runs names, order and the cached part of
        the measure). dbenbenn 2026-11-08: "is it not possible to start splitting heavy pieces in parallel? ...
        earlier feedback about whether the strategy is working". Returns True when it split (the run restarts
        from names)."""
        if not self.p.get('stream_memory_splits', True):
            return False
        last = self.state.get('stream_split_at')
        if last and time.time() - last < STREAM_SPLIT_MINUTES * 60:
            return False
        got = self.calibrate_inputs()
        if not got:
            return False
        cfg, plan, times, _, _ = got
        # live and in flight alike (live_pieces, as check_live_pieces): q153 2026-11-08, 6 of 25 in-flight pieces
        # split here had been accepted, and their new statements were orphans
        live = live_pieces(self.d)
        res = calibration(dict(plan, bundles=[], stubs={}), times, cfg.get('time_scale', 1.5), cfg.get('budget', 55),
                          live, rss_limit=self.rss_limit())
        tried = self.state.setdefault('auto_split', {})
        # pipeline.json `try_over_memory`: sent whatever their peak; a memory kill splits them (server_split_wanted)
        trying = self.trying_pieces()
        res['memory_over'] = [m for m in res['memory_over'] if m[0].split(':', 1)[1] not in trying]
        auto_mem, _ = self.memory_triage(plan, times, res['memory_over'], tried)
        # and those the verifier rejected (state `split`: a memory kill, or own timeouts), sized from their peak
        server = {}
        for n in self.server_split_wanted():
            if n in (plan.get('pieces') or {}) and n not in {a[0] for a in auto_mem}:
                rec = times.get('piece:' + n) or {}
                base = (times.get('statement:' + n) or {}).get('rss_mib')
                server[n] = memory_parts(rec['rss_mib'], base) or 2 if rec.get('rss_mib') else 2
        if not auto_mem and not server:
            return False
        want = dict(server, **{n: parts for n, _, _, parts in auto_mem})
        for n, rss, secs, parts in auto_mem:
            tried[n] = dict(tried.get(n) or {}, secs=secs, rss_mib=rss, parts=parts,
                            memory_rounds=(tried.get(n) or {}).get('memory_rounds', 1 if n in tried else 0) + 1)
        self.state['stream_split_at'] = time.time()
        line = 'splitting %d piece(s) alone while measuring (%d over the %d MiB memory limit, %d the verifier rejected): %s' % (
            len(want), len(auto_mem), self.rss_limit(), len(server), ', '.join('%s into %d' % x for x in sorted(want.items())))
        print('== measure: ' + line, flush=True)
        self.calibrate_log([line])
        self.split_pieces_locally(want, 'measure', 'measure: %s over the memory limit, split while streaming')
        return True

    def step_calibrate_pieces(self):
        """Overlap mode: the pieces, measured after the bundles and statements. A uniform overrun of several
        pieces while nothing is published re-plans at the ratio, as `calibrate` always did. Otherwise each slow
        piece is measured once more, then split alone (carve.py split-piece: lemmas it keeps become new
        statements; split_pieces_locally), once; so is each piece the publisher stopped after own verifier
        timeouts (state `split`), up to MAX_PIECE_SPLITS times. A piece still slow after its split, or whose
        statement alone is slow (its type is the cost), stops for a person. Until 2026-11-06 a slow piece of a
        published carve got a frozen global re-plan with its declarations costed at its ratio (config
        `cost_factors`), which re-shaped thousands of other pieces (q153)."""
        got = self.calibrate_inputs()
        if got is None:
            return 'skipped'
        cfg, plan, times, _, _ = got
        live = live_pieces(self.d)              # in flight too: a verdict may still make it live
        part = dict(plan, bundles=[], stubs={})
        res = calibration(part, times, cfg.get('time_scale', 1.5), cfg.get('budget', 55), live,
                          accepted=self.p.get('accept_over') or (), rss_limit=self.rss_limit())
        # pipeline.json `try_over_memory`: sent whatever their peak; a memory kill splits them (server_split_wanted)
        trying = self.trying_pieces()
        res['memory_over'] = [m for m in res['memory_over'] if m[0].split(':', 1)[1] not in trying]
        lines = self.calibrate_head(cfg, res, 'pieces: ')
        heavy = heavy_imports(plan, times, live, kinds=('piece',))
        if heavy:
            lines.append('WARNING %d piece(s) import more than %.0f MB (the verifier may run out of memory; a split does '
                         'not shrink imports, regrouping the bundles does): %s' % (
                             len(heavy), IMPORT_LIMIT / 1e6, ', '.join('%s %.0f MB' % x for x in heavy[:5])))
            print('calibrate_pieces: ' + lines[-1], file=sys.stderr, flush=True)
        log = os.path.join(self.d, 'logs', 'calibrate.log')
        server = {n: k for n, k in self.server_split_wanted().items() if n in (plan.get('pieces') or {})}
        if not res['over'] and not server and not res['memory_over']:
            self.calibrate_log(lines + ['pieces fit; time_scale %g kept' % cfg.get('time_scale', 1.5)])
            return None
        ratios = sorted(secs / max(cost, 1.0) for _, secs, cost in res['over'])
        uniform = (len(ratios) >= UNIFORM_MIN and ratios[len(ratios) // 2] >= UNIFORM_RATIO
                   and ratios[-1] <= 2 * ratios[0])
        if uniform and not server and not res['memory_over'] and not self.anything_published(cfg):
            return self.replan(cfg, round(min(MAX_SCALE, cfg.get('time_scale', 1.5) * ratios[len(ratios) // 2]), 1),
                               lines, 'calibrate_pieces')
        tried = self.state.setdefault('auto_split', {})
        auto, manual = [], []
        for key, secs, cost in res['over']:
            n = key.split(':', 1)[1]
            st = times.get('statement:' + n) or {}
            if n in tried:
                manual.append('%s: %.0f s, still over after an automatic split (it was %.0f s)' % (
                    key, secs, tried[n]['secs']))
            elif st.get('ok') and st['secs'] >= STATEMENT_SHARE * secs:
                manual.append('%s: %.0f s, of which its statement alone takes %.0f s: the type is the cost, '
                              'and no split helps' % (key, secs, st['secs']))
            elif not (plan.get('pieces') or {}).get(n, {}).get('keep'):
                manual.append('%s: %.0f s, no declarations recorded for it in the plan' % (key, secs))
            else:
                auto.append((n, secs, cost))
        # over the verifier's memory: split at once (a peak is no thrashing artefact to measure again)
        auto_mem, manual_mem = self.memory_triage(plan, times, res['memory_over'], tried)
        manual += manual_mem
        again = [(n, secs) for n, secs, _ in auto if n not in (self.state.get('remeasured') or {})]
        if again:
            # measured once more before any split (q138: 1595 s of CPU for a piece that compiles in 2 s alone,
            # measured while the machine thrashed): its entry is dropped, measure_pieces measures it again
            rm = self.state.setdefault('remeasured', {})
            times_path = got[4]
            for n, secs in again:
                rm[n] = secs
                times.pop('piece:' + n, None)
            json.dump(times, open(times_path, 'w'), indent=1)
            self.calibrate_log(lines + ['measuring %s again before any split' % ', '.join('piece:' + n for n, _ in again)])
            self.invalidate('measure_pieces')
            self.restart = True
            print('calibrate_pieces: measuring %d slow piece(s) again before any split' % len(again),
                  file=sys.stderr, flush=True)
            return None
        want = dict(server)
        budget = max(float(cfg.get('budget', 55)), 1.0)
        for n, secs, cost in auto:
            want[n] = max(want.get(n, 2), int(math.ceil(secs / budget)))
        for n, rss, secs, parts in auto_mem:
            want[n] = max(want.get(n, 2), parts)
        if want:
            for n, secs, cost in auto:
                tried[n] = {'secs': secs, 'cost': cost, 'parts': want[n]}
            for n, rss, secs, parts in auto_mem:
                tried[n] = dict(tried.get(n) or {}, secs=secs, rss_mib=rss, parts=want[n],
                                memory_rounds=(tried.get(n) or {}).get('memory_rounds', 1 if n in tried else 0) + 1)
            mem = {n for n, _, _, _ in auto_mem}
            lines.append('splitting %d piece(s) alone (carve.py split-piece; every other item kept): %s' % (
                len(want), ', '.join('%s into %d%s' % (n, k, ' (verifier timeouts or memory kills)' if n in server else
                                                       ' (over the %d MiB memory limit)' % PIECE_RSS_LIMIT if n in mem else '')
                                     for n, k in sorted(want.items()))))
            for m in manual:
                lines.append('  needs a person (after this round): ' + m)
            self.calibrate_log(lines)
            print('calibrate_pieces: %s' % lines[-1 - len(manual)], file=sys.stderr, flush=True)
            self.split_pieces_locally(want, 'calibrate_pieces', 'calibrate_pieces: %s slow or timed out')
            return None
        released = self.release_within_budget(plan, times, [key for key, _, _ in res['over']] +
                                              [key for key, _, _ in res['memory_over']])
        self.calibrate_log(lines + ['  needs a person: ' + m for m in manual] + ([released.strip()] if released else []))
        raise StepFailed(
            "step 'calibrate_pieces': piece(s) over the %.0f s limit:\n  %s\nA slow piece holds back only itself "
            "(with --publish the pieces within budget are released at once), and the full release is written in "
            "`publish`. %s A published statement cannot be restated: where its type is the cost, declaring "
            "OpenAI's theorem directly as `theorem _root_.solution` halves the serialization. To split a piece by "
            "hand: --split-piece NODE[=PARTS]. A piece under %d s may go as is and be split after two real "
            "timeouts: pipeline.json `accept_over` [\"piece:NAME\"]. Log %s%s"
            % (res['limit'], '\n  '.join(manual), self.PIECE_HINT, ACCEPT_CAP, log, released))

    def release_within_budget(self, plan, times, slow):
        """calibrate_pieces stops for a person (with --publish, once publishing began): the pieces measured
        within budget pass the pieces' gates (as pieces_prep) and are released for this plan
        (publish/release.json lists them; split_run holds every other piece), to the background publisher
        if it runs on this plan, else to one started now. A slow piece holds back only itself: no piece
        imports another. q129 (2026-10-30): oaiq-122 stopped on three slow pieces and never sent the other 36
        (10-112 s), so 68 live statements stayed Open leaves for hours; sent by hand, 36 were accepted at
        once. Returns the line for the stop message ('' when nothing is released)."""
        if not self.p.get('go'):
            return ''
        fast = sorted('piece:' + n for n in plan.get('pieces') or {}
                      if (times.get('piece:' + n) or {}).get('ok') and 'piece:' + n not in slow)
        return self.release_pieces(fast, 'calibrate_pieces', 'within budget', held=slow)

    def release_pieces(self, items, step, what, held=()):
        """Release `items` (pieces, measured) that measured ok and within the limit, through the pieces'
        gates, to the background publisher (started if none runs): publish/release.json lists them, adding
        to an earlier release for the same plan. Returns the line for the log ('' when nothing goes)."""
        cfg, plan, times, _, _ = self.calibrate_inputs()
        limit = cfg.get('budget', 55) * LIMIT_FACTOR
        ok = [x for x in items if (times.get(x) or {}).get('ok')]
        # calibrate_pieces has judged the slow ones (`held`); otherwise the limit decides here
        fast = sorted(x for x in ok if x not in held) if held else \
            sorted(x for x in ok if (times[x].get('secs') or 0) <= limit and fits_memory(times[x], self.rss_limit()))
        if not fast:
            return ''
        try:
            self.pieces_gates(step)
        except StepFailed as e:
            return ('\nThe %d piece(s) %s were not released: their gates failed: %s'
                    % (len(fast), what, str(e).splitlines()[0]))
        P = os.path.join(self.d, 'publish')
        sha = hashlib.sha1(open(os.path.join(P, 'plan.json'), 'rb').read()).hexdigest()
        try:
            old = json.load(open(os.path.join(P, 'release.json')))
        except (OSError, ValueError):
            old = {}
        if old.get('plan_sha') == sha and isinstance(old.get('pieces'), list):
            fast = sorted(set(fast) | set(old['pieces']))
        rel = {'plan_sha': sha, 'pieces': fast, 'held': sorted(held), 'released': _now()}
        tmp = os.path.join(P, 'release.json.tmp')
        json.dump(rel, open(tmp, 'w'), indent=1)
        os.replace(tmp, os.path.join(P, 'release.json'))
        if self.publisher_running():
            pub = os.path.join(self.published_dir(), 'plan.json')
            same = os.path.exists(pub) and hashlib.sha1(open(pub, 'rb').read()).hexdigest() == sha
            how = ('the running background publisher sends them' if same else 'a publisher on an earlier plan '
                   'still runs and does not send them: once it ends, run again with --publish')
        elif self.held_statements():
            # a publisher now would post a re-plan's new statements before their pieces are measured (q160)
            how = 'the publisher starts once measure_pieces has measured the new statements\' pieces'
        else:
            self.freeze_published()
            self.start_publisher()
            how = 'a background publisher was started for them'
        return ('\nReleased now (publish/release.json; %s): %d piece(s), %s, %s%s.'
                % (how, len(fast), what, ', '.join(fast), '; held: ' + ', '.join(sorted(held)) if held else ''))

    def source_line(self):
        m = json.load(open(self.meta))
        return ('OpenAI, %s, OpenAI Math Release, %s, https://github.com/openai/math (result family %s), '
                'Apache License 2.0' % (m['title'], m['date'], m['family']))

    def step_publish_prep(self):
        # once publishing began, publish/ is read by a publisher: sync it, never rebuild it
        sync = ['--sync'] if self.overlap() and self.publishing_started() else []
        self.check_live_pieces('publish_prep')            # a re-plan by hand (carve.py plan) as well
        self.run_cmds('publish_prep', [self.tool('carve_prep', 'publish-prep', self.d, self.source_line(),
                                                 self.p.get('tags') or 'openai-math', *sync)])

    def step_prose(self):
        # the sources map each module to its openai/math path (oaiq-035: guessed paths doubled a directory)
        self.run_cmds('prose', [self.tool('carve_prep', 'prose-template', self.d, '--meta', self.meta,
                                          '--lean-root', self.lean_src)])
        log = os.path.join(self.d, 'logs', 'prose.log')
        need = [l for l in open(log).read().splitlines() if 'needs written prose' in l]
        if need:
            print('NOTE: written prose still needed (goal and forced items); check_text and dryrun fail until '
                  'these files exist:', *need, sep='\n  ', file=sys.stderr)

    def step_check_text(self):
        # overlap mode: the bundles' and statements' text now, the explanations in pieces_prep
        kinds = ['--kinds', 'bundle,statement'] if self.overlap() else []
        self.run_cmds('check_text', [self.tool('carve_prep', 'check-text', os.path.join(self.d, 'publish'), *kinds)])

    def step_dryrun(self):
        run = 'publish/run_early.json' if self.overlap() else 'publish/run.json'
        self.run_cmds('dryrun', [self.tool('split_run', run)])

    def step_publish(self):
        if not self.p.get('go'):
            return 'skipped'
        self.mark_publishing('step publish started')
        self.save()
        if self.overlap():
            # every piece measured, calibrated and checked (pieces_prep): release them for this plan; a
            # background publisher still running on it sends them, and the final run below resumes it
            self.write_release(pieces='all', items='all', open=False)
            print('== pieces released for publishing (publish/release.json)', flush=True)
            self.join_publisher('the final publish')
        try:
            self.run_cmds('publish', [self.tool('split_run', 'publish/run.json', '--go')])
        except StepFailed:
            # pieces the verifier timed out on (state `split`) are split alone and the run goes on; any other
            # stop is a person's (dbenbenn 2026-11-06: split the one piece, get feedback fast)
            want = self.server_split_wanted() if self.overlap() else {}
            if not want:
                raise
            self.split_pieces_locally(want, 'publish', 'publish: %s timed out on the verifier')
            return None

    # -- overlap mode: the background publisher ---------------------------------------------------
    def publish_lock_key(self):
        return runlock.dir_key('publish', os.path.join(self.d, 'publish', 'run.json'))

    def publisher_running(self):
        """Is a publisher (the background one, or any `split_run --go` on this carve) running?"""
        return publisher_running_at(self.d, self.state)

    def join_publisher(self, before, poll=30):
        if not self.publisher_running():
            return
        pub = self.state.get('publisher') or {}
        print('== waiting for the background publisher (%s) to end before %s; progress in publish/PROGRESS.log, '
              'its output in logs/publish_early.log' % (pub.get('unit') or 'pid %s' % pub.get('pid'), before), flush=True)
        self.waiting = 'the background publisher (%s)' % (pub.get('unit') or 'pid %s' % pub.get('pid'))  # monitor note
        try:
            while self.publisher_running():
                time.sleep(poll)
        finally:
            self.waiting = None
        print('== background publisher ended %s' % _now(), flush=True)

    def step_publish_early(self):
        """Overlap mode, with --publish: the bundles and statements (measured, calibrated, checked)
        go to the platform from a background publisher, its own systemd user unit, while the pieces
        are measured. Before it starts, what it will publish is frozen: published/ keeps the plan and
        the files, and config `frozen`, `forced` (the statements) and `template_forced` are set
        (pipeline_state.json `auto_config`), so no later step re-plans or rewrites them.
        After a re-plan of the frozen part (new statements), it waits for measure_pieces (held_statements)."""
        if self.publisher_running() and not self.gated_publisher():
            print('== a publisher already runs on this carve; it goes on (new items wait for the final publish)',
                  flush=True)
            return None
        held = self.held_statements()
        if held:
            self.state['publish_held'] = {'at': _now(), 'statements': held}
            print('== publish_early: held until measure_pieces has measured their pieces (the CoeT check): %d new '
                  'statement(s) since the published plan, %s%s' % (len(held), ', '.join(held[:10]),
                                                                  ', ...' if len(held) > 10 else ''), flush=True)
            return 'skipped'
        self.publish_early_now()

    def held_statements(self):
        """The statements a re-plan added since publish_early froze the published part (publish/plan.json less
        published/plan.json), while measure_pieces has not run on this plan: they wait for it, since only it
        runs the verifier's CoeT check (a piece's). q160 (2026-11-03): 3 of a re-plan's 14 new statements failed
        that check after the background publisher had posted them, Open orphans now. A carve's first
        publish_early is not held: nothing is frozen yet, and its statements go while the pieces are measured."""
        if not (self.state.get('auto_config') or {}).get('frozen'):
            return []
        if (self.state['steps'].get('measure_pieces') or {}).get('status') == 'done':
            return []
        new = _load_json(os.path.join(self.d, 'publish', 'plan.json')) or {}
        old = _load_json(os.path.join(self.published_dir(), 'plan.json')) or {}
        # a streaming measure freezes only what it released: the plan it began with is not new
        return sorted(set(new.get('stubs') or {}) - set(old.get('stubs') or {}) - set(new.get('external') or ())
                      - set(self.state.get('streamed_stubs') or ()))

    def publish_early_now(self):
        if not os.path.exists(os.path.join(self.d, 'publish', 'run_early.json')):
            # publish_prep ran from a skill before overlap mode (a classic carve switched after it): the
            # background publisher would die at once on the missing file
            raise StepFailed("step 'publish_early': no publish/run_early.json (publish_prep ran from a skill before "
                             "overlap mode); run again with `--redo publish_prep` (nothing is published yet)")
        self.freeze_published()
        if self.publisher_running() and self.gated_publisher():
            # the streaming measure's publisher: every bundle and statement is calibrated and checked now
            self.write_release(items='all')
            print('== the streaming publisher goes on with every bundle and statement (publish/release.json items: '
                  'all)', flush=True)
            return
        self.start_publisher()

    def gated_publisher(self):
        """Is the background publisher the streaming one (run_stream.json: bundles and statements gated)?"""
        return bool((self.state.get('publisher') or {}).get('gated'))

    def freeze_published(self):
        P = os.path.join(self.d, 'publish')
        plan_file = os.path.join(P, 'plan.json')
        if not os.path.exists(plan_file):
            raise StepFailed("step 'publish_early': no publish/plan.json (publish_prep did not run?)")
        plan = json.load(open(plan_file))
        dst = self.published_dir()
        os.makedirs(os.path.join(dst, 'lib'), exist_ok=True)
        shutil.copy(plan_file, os.path.join(dst, 'plan.json'))
        lib = os.path.join(P, 'out', 'lib')
        ext = set(plan.get('external') or ())
        stubs = {n for n in plan.get('stubs') or {} if n not in ext}
        # only this plan's bundles and statements: publish/out/lib keeps earlier plans' files (oaiq-122: 227
        # never-posted files frozen beside 83 published blocked every later re-plan reusing one of their names)
        mine = plan_lib_files(plan)
        for f in sorted(os.listdir(lib)) if os.path.isdir(lib) else ():
            if f in mine:
                shutil.copy(os.path.join(lib, f), os.path.join(dst, 'lib', f))
        named = set(self.p.get('forced') or ()) | set((self.p.get('config_set') or {}).get('forced') or ())
        self.mark_publishing('publish_early froze the published part')
        a = self.state.setdefault('auto_config', {})
        a['frozen'] = {'plan': os.path.join(dst, 'plan.json'), 'bundles': [b['name'] for b in plan.get('bundles') or ()],
                       'lib': os.path.join(dst, 'lib')}
        a['forced'] = sorted(set(a.get('forced') or ()) | stubs)
        a['template_forced'] = sorted(set(a.get('template_forced') or ()) | (stubs - named))
        path = os.path.join(self.d, 'config.json')
        cfg = self.read_config() or {}
        json.dump(self.apply_auto(cfg), open(path, 'w'), indent=1)
        self.save()

    def start_publisher(self, gated=False):
        log = os.path.join(self.d, 'logs', 'publish_early.log')
        os.makedirs(os.path.dirname(log), exist_ok=True)
        run = 'publish/run_stream.json' if gated else 'publish/run_early.json'
        if gated and not os.path.exists(os.path.join(self.d, run)):
            raise StepFailed("step 'measure': no %s (publish_prep from an older skill); run again with "
                             "`--redo publish_prep`" % run)
        cmd = ' '.join(shlex.quote(x) for x in self.tool('split_run', run, '--go'))
        sh = '%s >> %s 2>&1; echo "== publisher exit $?" >> %s' % (cmd, shlex.quote(log), shlex.quote(log))
        with open(log, 'a') as f:
            f.write('== %s background publisher (%s), skill %s\n'
                    % (_now(), 'streaming: bundles, statements and pieces as released' if gated else
                       'bundles and statements; pieces once released', os.path.basename(self.snap)))
        unit, pid = None, None
        if shutil.which('systemd-run'):
            unit = publisher_unit(self.d)
            r = subprocess.run(systemd_run_command(unit, self.d, self.env(), sh), capture_output=True, text=True)
            if r.returncode:
                raise StepFailed("step 'publish_early': systemd-run failed: %s" % (r.stderr or r.stdout).strip())
        else:
            pid = subprocess.Popen(['/bin/sh', '-c', sh], cwd=self.d, env=self.env(), start_new_session=True,
                                   stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                   stderr=subprocess.DEVNULL).pid
        self.state['publisher'] = {'unit': unit, 'pid': pid, 'started': _now(), 'log': log, 'gated': gated}
        self.save()
        print('== background publisher started (%s): bundles and statements now, pieces once released; '
              'progress in publish/PROGRESS.log' % (unit or 'pid %d' % pid), flush=True)

    def step_pieces_prep(self):
        """Overlap mode: the pieces' gates, after calibrate_pieces. publish-prep --sync brings the measured
        pieces (and any new statements) into publish/ without touching what is published (it refuses
        if a published file would change), then prose-template, check-text of the explanations and a dry
        run over every item."""
        self.pieces_gates('pieces_prep')

    def pieces_gates(self, step):
        meta = ['--meta', self.meta, '--lean-root', self.lean_src]
        self.check_live_pieces(step)
        self.run_cmds(step, [
            self.tool('carve_prep', 'publish-prep', self.d, self.source_line(), self.p.get('tags') or 'openai-math', '--sync'),
            self.tool('carve_prep', 'prose-template', self.d, *meta),
            # the prose was checked in check_text (which re-runs after any re-plan): the explanations only
            # (oaiq-047: check-text over 1,279 statements took 50 min)
            self.tool('carve_prep', 'check-text', os.path.join(self.d, 'publish'), '--kinds', 'piece'),
            self.tool('split_run', 'publish/run.json')])

    # -- driver -----------------------------------------------------------------------------
    def run(self, stop_after=None, only_redo=(), claim_folder=False):
        self.check_ownership(claim_folder)
        self.publishing_started()                 # record evidence seen now as a state fact
        self.save()
        self.sync_config_set()
        redo = set(only_redo)
        self.ran_now = set()
        while True:
            self.restart = False
            self._run_once(stop_after, redo)
            if not self.restart:
                return self.state
            redo = set()               # a re-plan invalidated what follows the plan: run it again

    STALE_AFTER_PUBLISHING = (
        "step '%s': its input \"%s\" changed since it ran, but publishing has started: re-running it would re-port, "
        "rebuild and re-plan under live items, so nothing was run. Undo the change, or run `--redo %s` to do it "
        "deliberately (an overlap carve keeps its published part frozen; a classic one needs config `frozen` and "
        "`forced`, references/openai-ports.md \"After publishing\").")

    def _run_once(self, stop_after, only_redo):
        for s in self.steps():
            while True:
                st = self.stale_step()
                if not st or STEPS.index(st[0]) > STEPS.index(s):
                    break
                # after publishing, only what this run did deliberately (a --redo, or a step it ran before)
                # may make a step stale; a change from outside (an edited patches file, a port folder
                # rewritten under the carve) stops for a person
                # (a changed gen output only measures again: what is published is guarded by
                # check_published_unchanged and publish-prep --sync, q131)
                if (st[1] not in self.RULE_KEYS and st[1] != 'gen output' and self.publishing_started()
                        and st[0] not in only_redo
                        and not any(STEPS.index(x) < STEPS.index(st[0]) for x in self.ran_now)):
                    raise StepFailed(self.STALE_AFTER_PUBLISHING % (st[0], st[1], st[0]))
                print(self.stale_message(*st), flush=True)
                if st[1] in self.RULE_KEYS:
                    self.state['steps'].pop(st[0])        # like --redo: its consumers check its output
                else:
                    self.invalidate(st[0])
                self.save()
            rec = self.state['steps'].get(s)
            # --publish always re-enters split_run (it resumes from its run state): after a re-split the
            # recorded `publish` made --publish a 2 s no-op (oaiq-065, oaiq-071)
            again = s in ('publish', 'publish_early') and self.p.get('go')
            if rec and rec['status'] in ('done', 'skipped') and s not in only_redo and not again:
                if s == stop_after:
                    break
                continue
            if s == 'publish' and not self.p.get('go'):
                break                                              # publishing is opt-in, never recorded
            if s == 'publish_early' and not self.p.get('go'):
                if s == stop_after:
                    break
                continue                                           # the pieces are measured all the same
            print('== %s %s' % (s, _now()), flush=True)
            rec = self.state['steps'][s] = {'status': 'running', 'started': _now()}
            hashes = self.step_inputs_hash(s)
            if hashes:
                rec['in'] = hashes
            self.save()
            cfg_before = self.read_config() if s == 'config' else None
            try:
                res = getattr(self, 'step_' + s)()
            except StepFailed as e:
                rec.update(status='failed', finished=_now(), message=str(e).splitlines()[0])
                self.save()
                raise
            rec.update(status=res or 'done', finished=_now())
            if s in GEN_READERS and 'in' in rec:
                # what was measured, after the step's own repairs (carve_measure cuts a failing file in
                # place and records the cut, which gen re-applies): those never make it stale
                rec['in']['gen output'] = self.gen_output_hash(s)
            self.ran_now.add(s)
            if cfg_before is not None:
                self.config_consumers(cfg_before)
            self.save()
            if self.restart:
                self.state['steps'].pop(s, None)                   # re-run this step after the re-plan
                self.save()
                return
            if s == stop_after:
                break


def lock(d):
    runlock.hold(runlock.dir_key('pipeline', d), 'carve_pipeline.py on %s (pid %d)' % (d, os.getpid()))
