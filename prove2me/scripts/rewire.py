#!/usr/bin/env python3
"""Make a solution import the published theorems it re-derives, so each is a graph edge.

usage: rewire.py FILE --target NAME -o OUT [--only NAME ...] [--dry]

  --target  the short name of the theorem FILE proves; its own copy is never rewired

A proof assembled from a mission's shared modules carries its own copies of theorems that are
published on their own (`closure_mapA_mapB_eq_F'` beside `CannonFloydParry.closure_mapA_mapB_eq_F`).
The proof then depends on them without saying so: the platform draws an edge only for an
`import Theorems.*`, so the dependency the source argument has is missing from the graph. The
2026-09-24 sweep found eleven such proofs across Chou, CFP, Brin-Squier and Rosenblatt.

For each declaration whose name, with any trailing primes dropped, is the short name of a theorem
in $P2M_WORKSPACE/Theorems/, this replaces its proof with a call to the published theorem and adds
the import; prune_solution --check then deletes what only the old proof used and compiles the
result. The copy's own statement is kept, so the rewire is sound whatever the two statements look
like: if the call proves the copy's statement, the dependency is real. A copy the call cannot
prove (a genuinely different statement that happens to share a name) is restored and reported,
and the file is recompiled without it. Explicit hypotheses the published theorem takes as
instances are handled by installing every hypothesis as an instance first.

Name matching finds copies named after the published theorem; one renamed to something unrelated
is not found. `edge_audit.py` reports which copies are left.
"""
import argparse, os, re, shutil, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # p2mlib
from prune_solution import parse, _workspace

HERE = os.path.dirname(os.path.abspath(__file__))



def qualified(lines, start, name):
    """`name` declared at line `start`, prefixed by the namespaces open there."""
    if name.startswith('_root_.'):
        return name[len('_root_.'):]
    stack = []
    for l in lines[:start]:
        m = re.match(r'(namespace|end)\s+([\w.]+)\s*$', l)
        if m and m.group(1) == 'namespace':
            stack.append(m.group(2))
        elif m and stack and stack[-1] == m.group(2):
            stack.pop()
    return '.'.join(stack + [name])

def explicit_binders(header):
    from p2mlib.leantext import explicit_binders as eb
    return eb(header)


def published(ws):
    """{short name: (full name, module, explicit binder names)} -- p2mlib.workspace.published,
    which reads statements comment-aware (a comment line beginning "theorem" once named the
    wrong declaration here)."""
    from p2mlib.workspace import published as pub
    return pub(ws)


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


def rewrite(text, targets, pub):
    lines = text.split('\n')
    for d in sorted(parse(lines), key=lambda d: -d[2]):          # bottom-up keeps spans valid
        base = d[0].split('.')[-1].rstrip("'")
        if d[0].split('.')[-1] not in targets:
            continue
        full, mod, pub_args = pub[base]
        decl = '\n'.join(lines[d[2]:d[3]])
        i = decl.find(':=')
        header = decl[:i].rstrip()
        lines[d[2]:d[3]] = (header + ' :=\n  ' + body_for(full, header, pub_args)).split('\n')
    text = '\n'.join(lines)
    for t in targets:
        mod = pub[t.rstrip("'")][1]
        if not re.search(r'^import %s\s*$' % re.escape(mod), text, re.M):
            text = 'import %s\n' % mod + text
    return text


def check(path):
    """Prune `path` in place, then compile the pruned file itself, so error line numbers refer to
    the file whose declaration spans we attribute them to."""
    p = subprocess.run([sys.executable, os.path.join(HERE, 'prune_solution.py'), path],
                       capture_output=True, text=True)
    if p.returncode:
        return False, p.stdout + p.stderr
    ws = _workspace()
    c = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false', os.path.relpath(os.path.abspath(path), ws)],
                       cwd=ws, capture_output=True, text=True)
    out = c.stdout + c.stderr
    bad = c.returncode != 0 or re.search(r': error\b', out) or re.search(r'declaration uses .sorry.', out)
    return not bad, out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('file'); ap.add_argument('-o', '--out', required=True)
    ap.add_argument('--target', required=True)
    ap.add_argument('--only', nargs='*'); ap.add_argument('--dry', action='store_true')
    a = ap.parse_args()
    ws = _workspace()
    pub = published(ws)
    text = open(a.file, encoding='utf-8').read()
    if not re.search(r'^theorem solution\b', text, re.M):
        sys.exit('no `theorem solution` in %s' % a.file)
    # The target's own statement may sit in the merged file as a `sorry` stub under its published
    # full name (a development that imports a Statements module with the exact names, as Moore's
    # did, 2026-10-02): `theorem solution` proves it, and the stub would make the file a sorry.
    tgt = a.target.split('.')[-1]
    if tgt in pub:
        lines0 = text.split('\n')
        for d in sorted(parse(lines0), key=lambda d: -d[2]):
            if d[0].split('.')[-1] != tgt or qualified(lines0, d[2], d[0]) != pub[tgt][0]:
                continue
            decl = '\n'.join(lines0[d[2]:d[3]])
            if re.fullmatch(r'\s*(by\s+)?sorry\s*', decl[decl.find(':=') + 2:]):
                del lines0[d[2]:d[3]]
                print('   the target %s was a sorry stub under its published name; deleted' % tgt)
        text = '\n'.join(lines0)
    cands = []
    for d in parse(text.split('\n')):
        name = d[0].split('.')[-1]
        base = name.rstrip("'")
        if name == 'solution' or base not in pub or base == a.target.split('.')[-1]:
            continue
        if a.only and base not in a.only:
            continue
        # already a thin call to the published theorem (an earlier wiring): nothing to do
        body = '\n'.join(text.split('\n')[d[2]:d[3]])
        if re.search(r'(?<![\w.])%s(?![\w\'])' % re.escape(pub[base][0]), body[body.find(':='):]):
            continue
        cands.append(name)
    print('copies of published theorems: %s' % (', '.join(
        '%s -> %s' % (c, pub[c.rstrip("'")][0]) for c in cands) or 'none'))
    if a.dry:
        return
    # a copy declared under the published theorem's own full name cannot be rewired (the import
    # would clash: "has already been declared"); delete it and import the theorem instead.
    # CFP §6's Lemma 6.1 carried §2's `represents_mul` this way.
    # Only the FULL name clashes: a copy in another namespace (Monod's `Monod.Dev.Alg.BS.supp_conj`
    # beside `BrinSquier.supp_conj`, about a different `supp`) is rewired or left, never deleted.
    lines = text.split('\n')
    same = [d for d in parse(lines) if d[0].split('.')[-1] in cands
            and qualified(lines, d[2], d[0]) == pub[d[0].split('.')[-1].rstrip("'")][0]]
    imps = []
    for d in sorted(same, key=lambda d: -d[2]):
        name = d[0].split('.')[-1]
        del lines[d[2]:d[3]]
        imp = 'import ' + pub[name][1]
        if imp not in lines and imp not in imps:
            imps.append(imp)
        cands.remove(name)
        print('   %s had the published name; deleted and imported %s' % (name, pub[name][1]))
    # insert the imports only after every deletion: inserting at line 0 inside the loop shifted
    # the later (higher) spans by one line each, and each deletion then left its last line behind
    # (Monod 2026-09-30: three orphaned proof lines, "unexpected token 'show'; expected command")
    lines[0:0] = imps
    text = '\n'.join(lines)
    if not cands:
        open(a.out, 'w', encoding='utf-8').write(text)
        ok, out = check(a.out)
        print(('compiles clean: %s' if ok else 'DOES NOT COMPILE: %s') % a.out)
        if not ok:
            print(out[-800:])
        sys.exit(0 if ok else 1)
    kept, failed = list(cands), []
    while kept:
        open(a.out, 'w', encoding='utf-8').write(rewrite(text, kept, pub))
        ok, out = check(a.out)
        if ok:
            break
        # the copy whose span holds the first error line is the one the call could not prove;
        # restore it and try again without it
        spans = {d[0].split('.')[-1]: (d[2] + 1, d[3]) for d in parse(open(a.out).read().split('\n'))}
        errl = [int(n) for n in re.findall(r'\.lean:(\d+):\d+: error', out)]
        # a copy the prune deleted has no span any more (it was unused): it cannot hold the error
        bad = next((c for c in kept for n in errl if c in spans and spans[c][0] <= n <= spans[c][1]), None)
        if bad is None:
            sys.exit('compile failed outside every rewired copy -- the input itself may not compile:\n'
                     + out[-800:])
        print('   could not prove %s from %s; left as it was. Lean said:' % (bad, pub[bad.rstrip("'")][0]))
        for l in [l for l in out.split('\n') if ': error' in l][:4]:
            print('      ' + l[:220])
        kept.remove(bad); failed.append(bad)
    if not kept:
        shutil.copy(a.file, a.out)
        ok, out = check(a.out)
        print('no copy could be rewired; %s is %s pruned' % (a.out, 'the original,' if ok else 'the original (NOT compiling),'))
        sys.exit(1)
    imps = re.findall(r'^import (Theorems\.\S+)', open(a.out).read(), re.M)
    print('rewired %d: %s' % (len(kept), ', '.join(kept)))
    print('theorem imports now: %s' % ', '.join(i.split('Thm_', 1)[-1] for i in imps))
    print('compiles clean: %s' % a.out)
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
