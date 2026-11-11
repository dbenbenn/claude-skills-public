#!/usr/bin/env python3
"""Port patches from hand-repaired modules: diff the repaired module-route port against the pristine
one and write the patches.json entries that reproduce the repairs.

usage: mkpatches.py PRISTINE_DIR REPAIRED_DIR OUT.json [--why TEXT] [--drop-stale] [--port-dir DIR] [--ws WS]

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
                it: each patch says what Mathlib drift it repairs). It lands in the generated explanation
                of every piece the patch touches, where check-text looks up each backticked name: one our
                Mathlib lacks (OpenAI's old lemma name) is refused here, nothing written, since check-text
                would stop on it hours later at pieces_prep (q243-free-ising, nine NOT FOUND). Name an
                old lemma without backticks. Looked up as check-text does (carve_prep.missing_names) in
                the modules and the --ws workspace's Mathlib and Lean core.
  --port-dir DIR  the whole port PRISTINE was copied from (default: the workspace's Solutions/ folder
                holding every PRISTINE module, found by name and text). Uniqueness is counted over
                PRISTINE alone; when it holds fewer modules than the port this warns, and refuses (nothing
                written) a new `old` that also occurs in a port module PRISTINE lacks: filter_patches
                counts over the whole port (q220-uniform-kserver: a two-module scratch PRISTINE gave
                `  rfl` count 1, 96 over the port). Copy all of Solutions/FOLDER as PRISTINE.
  --drop-stale  drop existing entries that no longer apply exactly their `count` times (otherwise
                they are listed and nothing is written: is PRISTINE_DIR already patched?)

Each new entry is {old, new, count: 1, route: "modules", why}: one per diff hunk, whole lines, the
context widened a line at a time on both sides (merging hunks whose context meets) until `old`
occurs exactly once over all modules, as the entries before it leave them, and starts and ends at no
identifier (carve_prep.cut_identifier: oaiq-040's `hpos` matched inside `hpositive`); it never reaches up into an
`import Solutions.` line, which filter-patches cannot see (q147-ostmann-retry). Compat.lean and
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


def _floors(a, cores):
    """Per core, the first line its context may reach upward: just past the last `import
    Solutions.` line before it. filter-patches ports under the placeholder folder
    `Solutions.FilterPatches`, so an `old` holding the real folder's import counts 0 there and the
    pipeline refuses it (q147-ostmann-retry); such a hunk widens downward instead."""
    out = []
    for i1, _, _, _ in cores:
        imp = [i for i in range(i1) if a[i].startswith('import Solutions.')]
        out.append(imp[-1] + 1 if imp else 0)
    return out


def _groups(cores, ctx, n, floors=None):
    """Cores with their context (ctx[k] lines each side, clamped to [floors[k], n]) merged where the
    widened ranges overlap: [(lo, hi, [core indices])]."""
    gs = []
    for k, (i1, i2, _, _) in enumerate(cores):
        lo, hi = max(i1 - ctx[k], floors[k] if floors else 0), min(i2 + ctx[k], n)
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
    floors = _floors(a, cores)
    while True:
        gs = _groups(cores, ctx, len(a), floors)
        texts = dict(cur)
        out, grow = [], []
        for lo, hi, ks in gs:
            first, last = cores[ks[0]], cores[ks[-1]]
            old = ''.join(a[lo:hi])
            new = ''.join(b[first[2] - (first[0] - lo):last[3] + (hi - last[1])])
            ok = old and sum(t.count(old) for t in texts.values()) == 1 \
                and cut_identifier(old, texts.values()) is None
            if not ok:
                if lo <= floors[ks[0]] and hi == len(a):
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


def read_dir(d, empty_ok=False):
    out = {os.path.basename(f): open(f, encoding='utf-8').read() for f in glob.glob(os.path.join(d, '*.lean'))}
    if not out and not empty_ok:
        raise MkPatchError('no .lean files in ' + d)
    return out


def why_missing_names(why, texts, ws):
    """(names, searched): the backticked Lean-looking names of `why` that check-text would report NOT FOUND,
    looked up as it does (carve_prep.missing_names) in `texts` ({file: text}) and the workspace's Mathlib
    and Lean core; ([], False) when there is no library or rg to search (nothing can be judged)."""
    from carve_prep import missing_names, word_index, library_lookup, library_roots, rg_exe
    roots, rg = library_roots(ws), rg_exe()
    if not roots or not rg:
        return [], False
    local = word_index(texts.values())
    return missing_names(why, local, library_lookup(ws, roots, rg, os.devnull)), True


def port_folder(pristine, repaired, ws):
    """The workspace's Solutions/<FOLDER> PRISTINE was copied from: a folder holding every PRISTINE module
    by name, the one holding one of them with PRISTINE's or REPAIRED's text when several do; None when
    no folder or no single one fits."""
    names = set(pristine) - set(GENERATED)
    if not names:
        return None
    cands = []
    for d in sorted(glob.glob(os.path.join(ws, 'Solutions', '*', ''))):
        try:
            have = set(os.listdir(d))
        except OSError:
            continue
        if names <= have:
            cands.append(d.rstrip(os.sep))
    if len(cands) > 1:
        def same(d):
            for f in names:
                try:
                    t = open(os.path.join(d, f), encoding='utf-8').read()
                except OSError:
                    continue
                if t == pristine[f] or t == repaired.get(f):
                    return True
            return False
        cands = [d for d in cands if same(d)]
    return cands[0] if len(cands) == 1 else None


def scope_problems(pristine, port, new):
    """(warning or None, [refusal lines]): PRISTINE against the whole port `port` ({file: text}); a new
    entry's `old` occurring in a port module PRISTINE lacks is a refusal (filter_patches counts over all)."""
    extra = {f: t for f, t in port.items() if f not in pristine and f not in GENERATED}
    if not extra:
        return None, []
    total = len([f for f in port if f not in GENERATED])
    warn = ('WARNING: PRISTINE holds %d of the %d modules of the port; counts are over PRISTINE only, and '
            'filter_patches counts over the whole port (q220): copy all of Solutions/FOLDER as PRISTINE'
            % (len([f for f in pristine if f not in GENERATED and f in port]), total))
    bad = []
    for p in new:
        hits = {f: t.count(p['old']) for f, t in sorted(extra.items()) if p['old'] in t}
        if hits:
            bad.append('%r also occurs in %s' % (p['old'][:70], ', '.join('%s (%d)' % h for h in hits.items())))
    return warn, bad


VALUED = ('--why', '--port-dir', '--ws')


def main(argv):
    pos = [a for i, a in enumerate(argv) if not a.startswith('--') and (i == 0 or argv[i - 1] not in VALUED)]
    if len(pos) != 3:
        sys.exit(__doc__)
    pri, rpd, out = pos
    val = {k: argv[argv.index(k) + 1] for k in VALUED if k in argv}
    why = val.get('--why')
    ws = val.get('--ws')
    if not ws:
        try:
            from p2mlib.workspace import workspace
            ws = workspace()
        except SystemExit:
            ws = None
    existing = json.load(open(out, encoding='utf-8')) if os.path.exists(out) else []
    try:
        pristine, repaired = read_dir(pri), read_dir(rpd)
        pats, rep = derive(pristine, repaired, existing, why)
    except (MkPatchError, O.PortError) as e:
        sys.exit('mkpatches: %s' % e)
    port_dir = val.get('--port-dir') or (port_folder(pristine, repaired, ws) if ws else None)
    port = read_dir(port_dir, empty_ok=True) if port_dir else {}
    refuse = []
    if why:
        missing, searched = why_missing_names(why, {**port, **pristine, **repaired}, ws) if ws else ([], False)
        if not searched:
            print('warning: no Mathlib or rg to look up the --why\'s backticked names (check-text will)')
        for nm in missing:
            refuse.append('--why names `%s` in backticks, which neither the port nor our Mathlib has: check-text '
                          'stops on it (NOT FOUND) in every piece explanation the patch reaches (q243); write it '
                          'without backticks' % nm)
    warn, bad = scope_problems(pristine, port, [p for p in pats[len(pats) - len(rep['new']):]])
    if warn:
        print(warn + ' (port %s)' % port_dir)
    refuse += ['new entry %s: filter_patches would drop it for its count' % b for b in bad]
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
    if refuse:
        for r in refuse:
            print('REFUSED:', r)
        print('nothing written: %d problem%s' % (len(refuse), '' if len(refuse) == 1 else 's'))
        return 1
    with open(out, 'w', encoding='utf-8') as fh:
        json.dump(pats, fh, indent=1, ensure_ascii=False)
        fh.write('\n')
    print('%s: %d kept, %d new, %d stale dropped' % (out, len(pats) - len(rep['new']), len(rep['new']),
                                                    len(rep['stale'])))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
