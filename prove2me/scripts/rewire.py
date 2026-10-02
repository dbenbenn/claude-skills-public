#!/usr/bin/env python3
"""Make a solution import the published theorems it re-derives, so each is a graph edge.

usage: rewire.py FILE --target NAME -o OUT [--only NAME ...] [--dry]

  --target  the short name of the theorem FILE proves; its own copy is never rewired
  --only    rewire only copies of these published theorems (short names)
  --dry     list the copies and stop

A proof assembled from a mission's shared modules carries its own copies of theorems that are
published on their own (`closure_mapA_mapB_eq_F'` beside `CannonFloydParry.closure_mapA_mapB_eq_F`).
The proof then depends on them without saying so: the platform draws an edge only for an
`import Theorems.*`, so the dependency the source argument has is missing from the graph. The
2026-09-24 sweep found eleven such proofs across Chou, CFP, Brin-Squier and Rosenblatt.

A copy is a theorem of FILE that
  * states a published theorem, under any name: Lean decides (p2mlib.copies -- equal statements
    after renaming universes, unfolding FILE's own predicates and erasing proofs; Moore's
    `reduced_iff`, stated through a local `CommonCaret`, was rewired by hand before this); or
  * is named after one (its short name, primes dropped), whatever it states: a variant that the
    published theorem still proves is a dependency too, and one it does not prove is restored.
A copy declared under the published theorem's own full name would clash with the import, so it is
deleted and the theorem imported; so is the target's own `sorry` stub under its published name.

Every other copy keeps its statement and gets a call to the published theorem as its proof, and
the import is added; prune_solution --check then deletes what only the old proof used and
compiles the result. The rewire is sound whatever the two statements look like: if the call
proves the copy's statement, the dependency is real. A copy the call cannot prove is restored and
reported, and the file recompiled without it. Explicit hypotheses the published theorem takes as
instances are handled by installing every hypothesis as an instance first.

Every edit goes by the command ranges LeanInfo reports (p2mlib.leanedit), never by regex over the
text. A copy that only re-derives part of a published theorem (Moore's `reduced_unique`, the
uniqueness half of an `∃!`) is not a copy of anything; `edge_audit.py` reports which copies of
published theorems a proof keeps.
"""
import argparse
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))  # p2mlib
from p2mlib import copies, leanedit, leaninfo, names  # noqa: E402
from p2mlib.workspace import workspace, published as _published, published_by_full  # noqa: E402

_workspace = workspace


def explicit_binders(header):
    from p2mlib.leantext import explicit_binders as eb
    return eb(header)


def published(ws):
    """{short name: (full name, module, explicit binder names)} -- p2mlib.workspace.published,
    which reads statements comment-aware (a comment line beginning "theorem" once named the
    wrong declaration here)."""
    return _published(ws)


def body_for(full, header, pub_args):
    """A proof of the copy's statement from the published theorem. Every hypothesis of class
    type becomes available as an instance (the published theorem may take as `[Group.FG N]` what
    the copy took as `(hN : Group.FG N)`), then a few standard ways of applying it are tried."""
    mine = explicit_binders(header)
    inst = ''.join('try haveI := %s; ' % h for h in mine)
    # pass the copy's own arguments wherever the published theorem has an explicit binder of the
    # same name (`fg_of_extension N` when the copy's `hN hQ` became instances there)
    named = ' '.join(a for a in pub_args if a in mine)
    alts = (['exact %s %s' % (full, named)] if named else []) + [
        'exact %s' % full, 'exact %s ..' % full,
        '(apply %s <;> first | assumption | infer_instance)' % full, 'simpa using %s' % full]
    return 'by\n  %sfirst\n%s' % (inst, ''.join('    | %s\n' % x for x in alts))


def add_imports(text, modules):
    """`text` with `import M` added at the top for each module it does not import yet."""
    have = set(copies.imports_of(text))
    new = [m for m in dict.fromkeys(modules) if m not in have]
    return ''.join('import %s\n' % m for m in new) + text


def _value(info, c):
    """The text of command `c` from its `:=` on ('' when it has none)."""
    return info.slice(c.value_start.byte, c.end.byte) if c.value_start else ''


def rewrite(info, cands):
    """The source of `info` with each copy's proof replaced by a call to its published theorem
    (cands: {local full name: Published}) and the imports added."""
    reps = {}
    for name, p in cands.items():
        c = info.commands[leanedit.command_of(info, name)]
        header = info.slice(c.start.byte, c.value_start.byte).rstrip()
        reps[c.index] = header + ' :=\n  ' + body_for(p.full, header, p.binders).rstrip('\n')
    return add_imports(leanedit.replace_commands(info, reps), [p.module for p in cands.values()])


def check(path):
    """Prune `path` in place, then compile the pruned file itself, so error line numbers refer to
    the file whose command ranges we attribute them to."""
    p = subprocess.run([sys.executable, os.path.join(HERE, 'prune_solution.py'), path],
                       capture_output=True, text=True)
    if p.returncode:
        return False, p.stdout + p.stderr
    ws = workspace()
    c = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false', os.path.relpath(os.path.abspath(path), ws)],
                       cwd=ws, capture_output=True, text=True)
    out = c.stdout + c.stderr
    bad = c.returncode != 0 or re.search(r': error\b', out) or re.search(r'declaration uses .sorry.', out)
    return not bad, out


def blame(path, out, kept):
    """The rewired copy whose command holds the first compile error in `out`, or None."""
    info = leaninfo.run(path, parse_only=True)
    for line in (int(n) for n in re.findall(r'\.lean:(\d+):\d+: error', out)):
        for c in info.commands:
            nxt = info.commands[c.index + 1].start.line if c.index + 1 < len(info.commands) else 1 << 30
            if c.start.line <= line < nxt:
                hit = [n for n in c.names if n in kept]
                if hit:
                    return hit[0]
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('file'); ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--target', required=True)
    ap.add_argument('--only', nargs='*'); ap.add_argument('--dry', action='store_true')
    a = ap.parse_args()
    ws = workspace()
    pub, byfull = published(ws), published_by_full(ws)
    tgt = a.target.split('.')[-1]
    tgt_full = pub[tgt].full if tgt in pub else None

    # 1. by declared full name (one parse): the target's own `sorry` stub (a development that
    # imports a Statements module with the exact names, as Moore's did, 2026-10-02: `theorem
    # solution` proves it, and the stub would make the file a sorry), and copies under a published
    # theorem's full name (the import would clash: CFP §6 carried §2's `represents_mul` this way).
    # Only the FULL name clashes: Monod's `Monod.Dev.Alg.BS.supp_conj` beside
    # `BrinSquier.supp_conj`, about a different `supp`, is rewired or left, never deleted.
    info0 = leaninfo.run(a.file, parse_only=True, ws=ws)
    if not any('solution' in c.names for c in info0.commands):
        sys.exit('no `solution` declaration in %s' % a.file)
    drop, imps = [], []
    for c in info0.commands:
        for n in c.names:
            if n == tgt_full and re.fullmatch(r'\s*:=\s*(by\s+)?sorry\s*', _value(info0, c)):
                drop.append(c.index)
                print('   the target %s was a sorry stub under its published name; deleted' % tgt)
            elif n in byfull and n != tgt_full:
                drop.append(c.index); imps.append(byfull[n].module)
                print('   %s had the published name; deleted and imported %s' % (n, byfull[n].module))
    text = add_imports(leanedit.remove_commands(info0, drop), imps) if drop else open(a.file, encoding='utf-8').read()
    open(a.out, 'w', encoding='utf-8').write(text)

    # 2. copies: by statement (Lean), else by name
    info, same = copies.find(a.out, ws)
    if info.errors:
        sys.exit('%s does not elaborate:\n%s' % (a.out, '\n'.join(m.text[:200] for m in info.errors[:5])))
    cands = {}
    for d in info.decls:
        base = d.short.rstrip("'")
        if d.generated or d.name == 'solution' or base == tgt or d.kind != 'theorem':
            continue
        hits = [h for h in same.get(d.name, []) if h != tgt_full]
        p = byfull[hits[0]] if hits else pub.get(base)
        if p is None or p.full == tgt_full or (a.only and p.full.rsplit('.', 1)[-1] not in a.only):
            continue
        c = info.commands[d.command]
        if c.value_start is None or names.mentions(_value(info, c), p.full):
            continue                       # no proof to replace, or already a call (an earlier wiring)
        cands[d.name] = p
        print('   %s %s -> %s' % ('states' if hits else 'is named after', d.name, p.full))
    print('copies of published theorems: %d' % len(cands))
    if a.dry:
        return
    if not cands:
        ok, out = check(a.out)
        print(('compiles clean: %s' if ok else 'DOES NOT COMPILE: %s') % a.out)
        if not ok:
            print(out[-800:])
        sys.exit(0 if ok else 1)

    # 3. rewire, compile, and restore any copy the call cannot prove
    kept, failed = dict(cands), []
    while kept:
        open(a.out, 'w', encoding='utf-8').write(rewrite(info, kept))
        ok, out = check(a.out)
        if ok:
            break
        bad = blame(a.out, out, kept)
        if bad is None:
            sys.exit('compile failed outside every rewired copy -- the input itself may not compile:\n'
                     + out[-800:])
        print('   could not prove %s from %s; left as it was. Lean said:' % (bad, kept[bad].full))
        for l in [l for l in out.split('\n') if ': error' in l][:4]:
            print('      ' + l[:220])
        del kept[bad]; failed.append(bad)
    if not kept:
        open(a.out, 'w', encoding='utf-8').write(text)
        ok, out = check(a.out)
        print('no copy could be rewired; %s is %s pruned' % (a.out, 'the input,' if ok else 'the input (NOT compiling),'))
        sys.exit(1)
    imps = copies.imports_of(open(a.out, encoding='utf-8').read())
    print('rewired %d: %s' % (len(kept), ', '.join(kept)))
    print('theorem imports now: %s' % ', '.join(i.split('Thm_', 1)[-1] for i in imps if i.startswith('Theorems.')))
    print('compiles clean: %s' % a.out)
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
