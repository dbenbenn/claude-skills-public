#!/usr/bin/env python3
"""Port patches from hand-repaired modules: diff the repaired module-route port against the pristine
one and write the patches.json entries that reproduce the repairs.

usage: mkpatches.py PRISTINE_DIR REPAIRED_DIR OUT.json [--why TEXT] [--drop-stale]

  PRISTINE_DIR  the ported modules as oai_port_modules.py writes them with NO patches (`[]`): copy
                Solutions/FOLDER/*.lean right after such a port, or port into a scratch workspace
                (--ws). Counts are taken on this text, never on a patched or repaired workspace
                (oaiq-072 counted on the patched workspace and got count 0).
  REPAIRED_DIR  the same modules repaired by hand, each compiled alone (`lake env lean FILE`) in
                Solutions/FOLDER; keep a copy outside the workspace, since every re-port overwrites it
  OUT.json      the port's patches.json. If it exists its entries are kept, in order, and applied to
                the pristine text first; only what they leave different from the repair becomes new
                entries, appended. So a re-run after more repairs adds just the new hunks.
  --why TEXT    the `why` of every new entry (default a `TODO: why (MODULE)` placeholder; replace
                it: each patch says what Mathlib drift it repairs)
  --drop-stale  drop existing entries that no longer apply exactly their `count` times (otherwise
                they are listed and nothing is written: is PRISTINE_DIR already patched?)

Each new entry is {old, new, count: 1, route: "modules", why}: one per diff hunk, whole lines, the
context widened a line at a time on both sides (merging hunks whose context meets) until `old`
occurs exactly once over all modules, as the entries before it leave them, and starts and ends at no
identifier (carve_prep.cut_identifier: oaiq-040's `hpos` matched inside `hpositive`). Compat.lean and
the StdSimplex shims are generated after the patches, so edits there are reported, not patched; a
module only in REPAIRED_DIR is reported too (patches cannot create files). A new hunk that changes
lines an existing entry wrote is reported as amending it (it works; consider folding the two).

Before writing, the result is checked with the port's own apply_patches (p2mlib.oaiport, route
"modules") on the pristine text: every module must come out byte-identical to its repair.

The cycle (lessons oaiq-080, oaiq-043, oaiq-063, oaiq-071): repair the ported modules in place,
copy them to a kept REPAIRED dir; after a skill fix re-port with patches `[]`, copy PRISTINE, run
this, re-port with the patches, `cmp` each repaired module with the workspace one. The diff is
against the new port, so a skill fix that makes a repair unnecessary shows up as a smaller patch,
and an existing entry it broke shows up as stale.
"""
import difflib
import glob
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import oaiport as O  # noqa: E402
from carve_prep import cut_identifier  # noqa: E402

GENERATED = ('Compat.lean', O.STDSIMPLEX_MODULE + '.lean', O.STDSIMPLEX_TOP_MODULE + '.lean', O.UNIFINT_MODULE + '.lean')


class MkPatchError(Exception):
    pass


def lines(t):
    """t split after each newline; ''.join(lines(t)) == t."""
    return re.findall(r'[^\n]*\n|[^\n]+$', t)


def _cores(a, b):
    """The changed line ranges [i1, i2, j1, j2] of a -> b, adjacent ones joined."""
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == 'equal':
            continue
        if out and out[-1][1] == i1:
            out[-1][1], out[-1][3] = i2, j2
        else:
            out.append([i1, i2, j1, j2])
    return out


def _groups(cores, ctx, n):
    """Cores with their context (ctx[k] lines each side, clamped to [0, n]) merged where the
    widened ranges overlap: [(lo, hi, [core indices])]."""
    gs = []
    for k, (i1, i2, _, _) in enumerate(cores):
        lo, hi = max(i1 - ctx[k], 0), min(i2 + ctx[k], n)
        if gs and lo < gs[-1][1]:
            gs[-1] = (gs[-1][0], max(hi, gs[-1][1]), gs[-1][2] + [k])
        else:
            gs.append((lo, hi, [k]))
    return gs


def _module_patches(a, b, cur, name, why):
    """Entries turning lines a into lines b, each unique over `cur` ({file: text}, a's file in it
    as a) as the entries before it leave it; `cur` is updated. [(patch, first core line)]."""
    cores = _cores(a, b)
    ctx = [0] * len(cores)
    while True:
        gs = _groups(cores, ctx, len(a))
        texts = dict(cur)
        out, grow = [], []
        for lo, hi, ks in gs:
            first, last = cores[ks[0]], cores[ks[-1]]
            old = ''.join(a[lo:hi])
            new = ''.join(b[first[2] - (first[0] - lo):last[3] + (hi - last[1])])
            ok = old and sum(t.count(old) for t in texts.values()) == 1 \
                and cut_identifier(old, texts.values()) is None
            if not ok:
                if lo == 0 and hi == len(a):
                    raise MkPatchError('%s: even the whole module is not unique over the port' % name)
                grow += ks
                continue
            out.append(({'old': old, 'new': new, 'count': 1, 'route': 'modules',
                         'why': why or 'TODO: why (%s)' % name[:-5]}, first[0]))
            texts = {f: t.replace(old, new) for f, t in texts.items()}
        if not grow:
            cur.update(texts)
            return out
        for k in grow:
            ctx[k] += 1


def derive(pristine, repaired, existing, why=None):
    """(patches, report): `existing` (entries still applying) then new entries such that
    oaiport.apply_patches(pristine, patches, route='modules') gives `repaired` ({file: text}; a file
    missing there is unchanged). report: {'skipped': [str], 'stale': [(reason, entry)],
    'amends': [str]}."""
    rep = {'skipped': [], 'stale': [], 'amends': []}
    base = {f: t for f, t in pristine.items() if f not in GENERATED}
    for f in sorted(repaired):
        if f in GENERATED and repaired[f] != pristine.get(f):
            rep['skipped'].append('%s: generated by the port, not patched; edit the compat block instead' % f)
        elif f not in pristine:
            rep['skipped'].append('%s: not in the pristine port (patches cannot create a module)' % f)
    cur, kept = dict(base), []
    for p in existing:
        if O.applies_to(p, 'modules'):
            n = sum(t.count(p['old']) for t in cur.values())
            if n != p.get('count', 1):
                rep['stale'].append(('applies %d times, want %d' % (n, p.get('count', 1)), p))
                continue
            cur = {f: t.replace(p['old'], p['new']) for f, t in cur.items()}
        kept.append(p)
    new = []
    for f in sorted(base):
        if f not in repaired or repaired[f] == cur[f]:
            continue
        a, b = lines(cur[f]), lines(repaired[f])
        touched = set()
        for i1, i2, j1, j2 in _cores(lines(base[f]), a):
            touched.update(range(j1, j2))
        for i1, i2, _, _ in _cores(a, b):
            hit = touched.intersection(range(i1, max(i2, i1 + 1)))
            if hit:
                line = a[min(hit)]
                k = next((k for k, p in enumerate(kept) if line in p['new']), None)
                rep['amends'].append('%s line %d changes text existing entry %s wrote: %r'
                                     % (f, min(hit) + 1, '#%d' % k if k is not None else '?', line[:70]))
        for p, at in _module_patches(a, b, cur, f, why):
            p['_at'] = '%s:%d' % (f, at + 1)
            new.append(p)
    pats = kept + [{k: v for k, v in p.items() if k != '_at'} for p in new]
    got = O.apply_patches(base, pats, route='modules')
    bad = [f for f in base if got[f] != repaired.get(f, base[f])]
    if bad:
        raise MkPatchError('the patches do not reproduce: ' + ', '.join(bad))
    rep['new'] = [p['_at'] for p in new]
    return pats, rep


def read_dir(d):
    out = {os.path.basename(f): open(f, encoding='utf-8').read() for f in glob.glob(os.path.join(d, '*.lean'))}
    if not out:
        raise MkPatchError('no .lean files in ' + d)
    return out


def main(argv):
    pos = [a for i, a in enumerate(argv) if not a.startswith('--') and (i == 0 or argv[i - 1] != '--why')]
    if len(pos) != 3:
        sys.exit(__doc__)
    pri, rpd, out = pos
    why = argv[argv.index('--why') + 1] if '--why' in argv else None
    existing = json.load(open(out, encoding='utf-8')) if os.path.exists(out) else []
    try:
        pats, rep = derive(read_dir(pri), read_dir(rpd), existing, why)
    except (MkPatchError, O.PortError) as e:
        sys.exit('mkpatches: %s' % e)
    for s in rep['skipped']:
        print('skipped:', s)
    for reason, p in rep['stale']:
        print('stale entry (%s): %r' % (reason, p['old'][:70]))
    for s in rep['amends']:
        print('amends:', s)
    for at in rep['new']:
        print('new:', at)
    if rep['stale'] and '--drop-stale' not in argv:
        print('nothing written: %d stale entries (is %s already patched? else --drop-stale)'
              % (len(rep['stale']), pri))
        return 1
    with open(out, 'w', encoding='utf-8') as fh:
        json.dump(pats, fh, indent=1, ensure_ascii=False)
        fh.write('\n')
    print('%s: %d kept, %d new, %d stale dropped' % (out, len(pats) - len(rep['new']), len(rep['new']),
                                                    len(rep['stale'])))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
