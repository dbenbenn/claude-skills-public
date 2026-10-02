#!/usr/bin/env python3
"""Build a mission's solutions from its development's check files: one file per statement.

usage: build_solutions.py MISSION_DIR --check MOD [--check MOD ...] [--out DIR] [NAME ...]

  MOD      a check module under $P2M_WORKSPACE/Solutions, e.g. Monod/AlgCheck
  NAME     statements to build (default: every THEOREMS entry of MISSION_DIR/mission.py that
           some check file proves)
  --out    default MISSION_DIR/solutions; writes Sol_<name>.lean and Sol_<name>.log

A development proves each statement in a check file, as `theorem <name>` or `theorem chk_<name>`,
from the development's own modules, which carry primed copies of sibling statements because
nothing was published when they were written. For each statement this merges the Solutions modules
that check file imports (dependencies first, with merge.py), appends the check block renamed to
`theorem solution` at top level under `open <namespace> in`, then runs rewire.py, which turns each
copy of a published theorem into a call to it plus an import, prunes and compiles.

Run `fetch_theorems.py` first, so every published name is in $P2M_WORKSPACE/Theorems; rewire only
sees names there. Afterwards run edge_overlap.py on the output: a helper that re-derives a sibling
under another name is invisible to rewire.

Generalised 2026-09-30 from the per-mission builders of CFP §5, §6 and §7.
"""
import argparse, os, re, subprocess, sys

SK = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SK)
from prune_solution import _workspace  # noqa: E402


def deps(sol, mod, seen):
    """Append Solutions module `mod` ('Monod/AlgG') after the Solutions modules it imports."""
    text = open(os.path.join(sol, mod + '.lean'), encoding='utf-8').read()
    for m in re.findall(r'^import Solutions\.([\w.]+)', text, re.M):
        dep = m.replace('.', '/')
        if dep not in seen:
            deps(sol, dep, seen)
    if mod not in seen:
        seen.append(mod)
    return seen


def find_block(sol, checks, name):
    """(check module, namespace, opens, block) for the check theorem proving `name`, else None."""
    for mod in checks:
        text = open(os.path.join(sol, mod + '.lean'), encoding='utf-8').read()
        # the block ends at the next command; `open` included, or the `open X in` heading the
        # next check block was swallowed and left dangling at the end of the solution (Moore, 2026-10-02)
        m = re.search(r'^theorem (?:chk_)?%s(?![\w\']).*?(?=^(?:(?:theorem|lemma|end|namespace|section|open|def|'
                      r'noncomputable|private|protected|example|variable|set_option|instance|abbrev|'
                      r'attribute)\b|#|/-|@\[)|\Z)' % re.escape(name), text, re.M | re.S)
        if not m:
            continue
        # scan commands only: a docstring line beginning with "open" was once copied into a
        # solution as an `open` command (F-amenability Cor 3, 2026-09-30)
        before = re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', text[:m.start()], flags=re.S))
        # the namespaces still open at the block: push on `namespace`, pop on a matching `end`
        stack = []
        for kw, ns in re.findall(r'^(namespace|end)\s+([\w.]+)', before, re.M):
            if kw == 'namespace':
                stack.append(ns)
            elif stack and stack[-1] == ns:
                stack.pop()
        # `open X in` scopes only the next command: keep it (without its `in`) when it sits
        # directly above the block, drop it otherwise. Copying it verbatim gave `open X in in`
        # and broke 20 of Moore's 31 solutions (2026-10-02).
        opens = []
        lines = [l for l in before.rstrip().split('\n')]
        tail = len(lines)
        while tail and re.match(r'^open .* in\s*$', lines[tail - 1]):
            tail -= 1
        for i, l in enumerate(lines):
            mo = re.match(r'^open ([^\n]+?)(\s+in)?\s*$', l)
            if not mo:
                continue
            if mo.group(2) and i < tail:
                continue
            opens.append(mo.group(1))
        block = re.sub(r'^theorem (?:chk_)?%s(?![\w\'])' % re.escape(name), 'theorem solution', m.group(0).rstrip(),
                       count=1, flags=re.M)
        return mod, '.'.join(stack), opens, block
    return None


def build(mdir, checks, name, out):
    ws = _workspace()
    sol = os.path.join(ws, 'Solutions')
    found = find_block(sol, checks, name)
    if not found:
        return name, 'NO-CHECK', []
    mod, ns, opens, block = found
    seen = []
    text = open(os.path.join(sol, mod + '.lean'), encoding='utf-8').read()
    for m in re.findall(r'^import Solutions\.([\w.]+)', text, re.M):
        deps(sol, m.replace('.', '/'), seen)
    files = [os.path.join(sol, s + '.lean') for s in seen]
    # the check file's own helpers (definitions and lemmas above its check blocks) are merged too,
    # minus every check block: the Moore weak-reading counterexamples kept `wAct`, `mu`, ... in the
    # check file itself, and the solution came out naming undefined helpers (2026-10-01)
    from merge import blocks
    last = lambda n: (n or '').split('.')[-1]
    helpers = '\n'.join(t for n, t in blocks(text) if not (n and (last(n).startswith('chk_') or last(n) == name)))
    if re.search(r'^(?:@\[[^\n]*\]\s*)?(?:private |protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev|instance|structure|inductive)\b',
                 helpers, re.M):
        hf = os.path.join(out, '.checkhelpers_%s.lean' % name)
        open(hf, 'w', encoding='utf-8').write(helpers)
        files.append(hf)
    merged = os.path.join(out, '.merged_%s.lean' % name)
    p = subprocess.run([sys.executable, os.path.join(SK, 'merge.py'), merged] + files, capture_output=True, text=True)
    if p.returncode:
        open(os.path.join(out, 'Sol_%s.log' % name), 'w').write(p.stdout + p.stderr)
        return name, 'MERGE-FAIL', []
    # the check file's own non-Solutions imports (Definitions, Theorems, Mathlib) go first
    extra = [l for l in re.findall(r'^(import (?!Solutions\.)\S+)$', text, re.M)]
    body = open(merged, encoding='utf-8').read()
    have = set(re.findall(r'^(import \S+)$', body, re.M))
    body = ''.join(l + '\n' for l in extra if l not in have) + body
    # A check block that names a published sibling statement directly (`Gpp_eq_G_top_and_Hpp_eq_H_top.2`)
    # needs its import, and the import is what draws the graph edge (Monod 2026-09-30).
    thm = os.path.join(ws, 'Theorems')
    for tok in sorted(set(re.findall(r"(?<![\w'])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)", block))):
        short = tok.split('.')[-1] if not ns or not tok.startswith(ns + '.') else tok[len(ns) + 1:]
        short = short.split('.')[0] if '.' in short else short
        if short == name:
            continue
        for cand in ([ns.split('.')[0] + '_' + short] if ns else []) + [tok.replace('.', '_')]:
            if os.path.exists(os.path.join(thm, 'Thm_%s.lean' % cand)):
                imp = 'import Theorems.Thm_%s' % cand
                if imp not in body:
                    body = imp + '\n' + body
                break
    prefix = ''.join('open %s in\n' % o for o in ([ns] if ns else []) + opens)
    body += '\n%s%s\n' % (prefix, block)
    open(merged, 'w', encoding='utf-8').write(body)
    dst = os.path.join(out, 'Sol_%s.lean' % name)
    p = subprocess.run([sys.executable, os.path.join(SK, 'rewire.py'), merged, '--target', name, '-o', dst],
                       capture_output=True, text=True, cwd=ws)
    open(os.path.join(out, 'Sol_%s.log' % name), 'w').write(p.stdout + p.stderr)
    os.remove(merged)
    for f in files:
        if os.path.basename(f).startswith('.checkhelpers_'):
            os.remove(f)
    imps = re.findall(r'^import Theorems\.(\S+)', open(dst).read(), re.M) if os.path.exists(dst) else []
    # rewire exits 1 when it left a copy it could not prove from the published theorem (a genuinely
    # different statement sharing a name); the file itself still compiles: report OK*, read the log
    st = 'OK' if p.returncode == 0 else \
        'OK*' if 'compiles clean' in p.stdout + p.stderr and 'could not prove' in p.stdout + p.stderr \
        else 'RC%d' % p.returncode
    # a proof may never import its own target (the verifier answers FAILED); this happens when a
    # development lemma was re-derived from the published statement and the check block still uses it
    if any(i.endswith('_' + name) and i.startswith((ns.split('.')[0] if ns else '') + '_') for i in imps):
        st = 'SELF-IMPORT'
    return name, st, imps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mission_dir')
    # repeatable, not nargs='+': a list option swallows the positional NAMEs after it
    ap.add_argument('--check', dest='checks', action='append', required=True)
    ap.add_argument('--out')
    ap.add_argument('names', nargs='*')
    a = ap.parse_intermixed_args()
    mdir = os.path.abspath(a.mission_dir)
    out = a.out or os.path.join(mdir, 'solutions')
    os.makedirs(out, exist_ok=True)
    names = a.names
    if not names:
        sys.path.insert(0, mdir)
        import mission  # noqa: E402
        names = [T['name'] for T in mission.THEOREMS]
    for n in names:
        name, st, imps = build(mdir, a.checks, n, out)
        print('%-9s %-52s imports: %s' % (st, name, ', '.join(imps) or '(none)'), flush=True)


if __name__ == '__main__':
    main()
