#!/usr/bin/env python3
"""Delete the declarations an assembled solution never uses, before submitting it.

A solution built by concatenating modules carries lemmas its target does not touch, and
`import Theorems.*` lines for published theorems only those lemmas used. Both go. That is
not merely untidy:

  * a reader cannot tell which lemmas the proof depends on, and neither can you months later;
  * an unused copy of a *published* theorem looks like a missing graph edge, and importing it
    to "fix" that asserts a dependency the proof does not have — a false edge, which is worse
    than a missing one, and it still compiles so nothing catches it.

What counts as used is reachability from `solution` in the file's own call graph — not being
referenced somewhere, since a lemma referenced only by another unused lemma is still unused.

DANGER, and the reason this script never prunes on its own judgement alone: **unused by name is
not unused**. A `@[simp]` lemma is applied by `simp` without being named, an `instance` is found
by typeclass resolution, `@[ext]`/`@[norm_cast]`/`@[elab_as_elim]` and friends register a
declaration with a tactic or the elaborator. Any of those can be load-bearing while no proof
mentions it. So every attributed declaration, every `instance`, and everything reachable from
them is treated as a root, and the result MUST be compiled before it is submitted. Pass
--check to have this script do that, and do not skip it.

usage:
    prune_solution.py FILE [-o OUT] [--check] [--dry]

    --check  elaborate the pruned file with `lake env lean -DautoImplicit=false` (run from
             $P2M_WORKSPACE) BEFORE writing it; the destination is replaced only if it compiles.
             The verifier has autoImplicit off, and `lake env lean` ignores the lakefile's
             leanOptions, so without the flag an out-of-scope `universe u` passes here
    --dry    report what would go, write nothing
"""
import argparse
import os
import re
import subprocess
import sys
from collections import defaultdict

KINDS = r'(?:lemma|theorem|def|abbrev|instance|structure|inductive|class|alias)'
# an attribute may sit on the declaration's own line (`@[simp] theorem foo …`); such a
# declaration is attributed exactly as if the attribute were on the line above
DECL = re.compile(r'^(?P<attr>(?:@\[[^\]]*\]\s*)*)'
                  r'(?P<mods>(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*)'
                  # Lean identifiers are Unicode (`φ`, `ψₙ`) or «guillemeted»; an ASCII-only
                  # pattern missed `def φ`, folded its body into the lemma above, and pruned
                  # everything only φ used (two CFP replacements failed --check on it)
                  r'(?P<kind>%s)\s+(?P<name>«[^»]+»|[^\W\d][\w.\'!?\u2080-\u209c]*)' % KINDS)
# anything that starts a new top-level command ends the declaration above it; without this a
# `set_option … in`, a `notation` or a `mutual` is absorbed into the previous declaration and
# deleted along with it
TOP = re.compile(r'^(?:@\[|/--|/-!|%s|private|protected|noncomputable|partial|unsafe|end\b|'
                 r'namespace\b|section\b|open\b|variable\b|universe\b|attribute\b|local\b|'
                 r'scoped\b|set_option\b|mutual\b|omit\b|include\b|notation\b|infix[lr]?\b|'
                 r'prefix\b|postfix\b|macro\b|macro_rules\b|syntax\b|elab\b|#)' % KINDS)
# an anonymous instance has no name for DECL to capture, but it is a root all the same
ANON_INSTANCE = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|scoped)\s+)*'
                           r'instance\b(?!\s+(?:«|[^\W\d]))')


def parse(lines):
    """[(name, kind, start, end, attributed)] for top-level declarations, in file order.

    `start` includes any attribute lines and doc comment immediately above.
    """
    heads = []
    for i, l in enumerate(lines):
        m = DECL.match(l)
        if m:
            heads.append((i, m.group('name'), m.group('kind'), bool(m.group('attr'))))
        elif ANON_INSTANCE.match(l):
            heads.append((i, '_anonymous_instance_%d' % i, 'instance', True))
    out = []
    for k, (i, name, kind, inline_attr) in enumerate(heads):
        j = i + 1
        while j < len(lines) and not TOP.match(lines[j]):
            j += 1
        while j - 1 > i and lines[j - 1].strip() == '':
            j -= 1
        s = i
        attributed = inline_attr
        # walk back over blank lines, a doc comment, and any attribute lines
        while s - 1 >= 0:
            prev = lines[s - 1].rstrip()
            if prev.strip() == '':
                s -= 1
                continue
            if prev.endswith('-/'):
                d = s - 1
                while d >= 0 and not lines[d].lstrip().startswith(('/--', '/-!')):
                    d -= 1
                if d >= 0 and lines[d].lstrip().startswith('/--'):
                    s = d
                    continue
                break
            if prev.lstrip().startswith('@['):
                attributed = True
                s -= 1
                continue
            # a scoping prefix (`open Classical in`, `variable (m) in`, `set_option … in`)
            # belongs to the declaration: left behind, it would attach to whatever follows
            if re.match(r'(open|variable|set_option|omit|include)\b.*\bin$', prev.strip()):
                s -= 1
                continue
            break
        out.append((name, kind, s, j, attributed))
    return out


def callgraph(lines, decls):
    names = {d[0] for d in decls}
    g = defaultdict(set)
    # a reference may be namespace-qualified (`Chou.Lib.foo` for a `foo` declared inside
    # `namespace Chou.Lib`), so allow a dotted prefix. Excluding a preceding '.' — the obvious
    # way to stop `Foo.bar` matching `bar` — makes every qualified call invisible, and the
    # analysis then reports live code as dead.
    # ...and a declaration `Foo.qux` is called as plain `qux` from inside `namespace Foo`, so its
    # last component counts too (over-matching only keeps more, which --check then confirms)
    pats = {n: re.compile(r"(?<![\w'\u2080-\u209c])(?:[^\W\d][\w'\u2080-\u209c]*\.)*(?:%s)(?![\w'\u2080-\u209c])"
                          % '|'.join(sorted({re.escape(n), re.escape(n.split('.')[-1])})))
            for n in names}
    for name, kind, s, e, _ in decls:
        body = '\n'.join(lines[s:e])
        for other in names:
            if other != name and pats[other].search(body):
                g[name].add(other)
    return g


def prune(text, verbose=True):
    lines = text.split('\n')
    decls = parse(lines)
    if not any(d[0] == 'solution' for d in decls):
        raise SystemExit('no `solution` declaration — refusing to prune')

    roots = {'solution'}
    # `attribute [simp] foo` registers foo with a tactic exactly as `@[simp]` on it would
    for l in lines:
        m = re.match(r'^(?:local\s+|scoped\s+)?attribute\s*\[[^\]]*\]\s+(.*)$', l)
        if m:
            for ref in m.group(1).split():
                roots.update(d[0] for d in decls if ref in (d[0], d[0].split('.')[-1]))
    for name, kind, s, e, attributed in decls:
        # implicit users: tactics and typeclass resolution find these without naming them
        if attributed or kind in ('instance', 'structure', 'inductive', 'class'):
            roots.add(name)

    g = callgraph(lines, decls)
    seen = set(roots)
    stack = list(roots)
    while stack:
        n = stack.pop()
        for m in g.get(n, ()):
            if m not in seen:
                seen.add(m)
                stack.append(m)

    doomed = [d for d in decls if d[0] not in seen]
    if verbose:
        kept = len(decls) - len(doomed)
        print('declarations: %d   kept: %d   unused: %d' % (len(decls), kept, len(doomed)))
        for name, kind, s, e, _ in doomed:
            print('   - %-58s %s, %d lines' % (name[:58], kind, e - s))
    keep_mask = [True] * len(lines)
    for _, _, s, e, _ in doomed:
        for i in range(s, e):
            keep_mask[i] = False
    out = '\n'.join(l for i, l in enumerate(lines) if keep_mask[i])
    out, dropped = prune_theorem_imports(out, verbose)
    return out, doomed + dropped


def _workspace():
    for p in (os.environ.get('P2M_WORKSPACE'), '~/claude/prove2me_workspace', '~/prove2me_workspace'):
        if p and os.path.isdir(os.path.expanduser(p)):
            return os.path.expanduser(p)
    return os.path.expanduser('~/claude/prove2me_workspace')


def prune_theorem_imports(text, verbose=True):
    """Drop each `import Theorems.X` whose theorem the remaining code never names.

    The platform draws a dependency edge for every imported theorem, so an unused one is a false
    edge -- and it survives everything else here, because the declaration pass never looks at
    imports. Five live edges came from this (2026-09-24 audit): a rewire cut a helper and imported
    it, then cut its only user too, and the first import stayed. A theorem is "named" by its full
    name or its last component, comments excluded; --check then proves the import was unused."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from stage_auditor import strip
    ws = _workspace()
    code = '\n'.join(l for l in strip(text).split('\n') if not l.startswith('import '))
    keep, dropped = [], []
    for l in text.split('\n'):
        m = re.match(r'^import\s+(Theorems\.\S+)\s*$', l)
        if m:
            f = os.path.join(ws, m.group(1).replace('.', os.sep) + '.lean')
            try:
                d = re.search(r'^\s*(?:theorem|lemma)\s+([^\s:({]+)', strip(open(f).read()), re.M)
            except OSError:
                d = None
            if d:
                short = re.escape(d.group(1).split('.')[-1])
                if not re.search(r"(?<![\w'\u2080-\u209c])(?:[^\W\d][\w'\u2080-\u209c]*\.)*%s(?![\w'\u2080-\u209c])"
                                 % short, code):
                    dropped.append((m.group(1), 'import', 0, 0, False))
                    continue
        keep.append(l)
    if verbose and dropped:
        print('unused theorem imports (each would be a false graph edge): %d' % len(dropped))
        for name, *_ in dropped:
            print('   - import %s' % name)
    return '\n'.join(keep), dropped


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('file')
    ap.add_argument('-o', '--out')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--dry', action='store_true')
    a = ap.parse_args()
    if a.dry and a.check:
        sys.exit('--dry writes nothing, so there is nothing to --check; drop one of them')

    text = open(a.file, encoding='utf-8').read()
    n0 = len(text.split('\n'))
    out, doomed = prune(text)
    n1 = len(out.split('\n'))
    print('%d -> %d lines (%d removed)' % (n0, n1, n0 - n1))
    if a.dry:
        return
    dest = a.out or a.file
    if not a.check:
        open(dest, 'w', encoding='utf-8').write(out)
        print('wrote %s' % dest)
        return

    # check a candidate next to the destination, and replace the destination only if it passes:
    # overwriting first would leave nothing but the broken version when the prune was wrong
    ws = os.environ.get('P2M_WORKSPACE') or next(
        (p for p in map(os.path.expanduser, ('~/claude/prove2me_workspace', '~/prove2me_workspace'))
         if os.path.isdir(p)), os.path.expanduser('~/claude/prove2me_workspace'))
    cand = os.path.join(os.path.dirname(os.path.abspath(dest)),
                        '.pruned_%d_%s' % (os.getpid(), os.path.basename(dest)))
    open(cand, 'w', encoding='utf-8').write(out)
    try:
        p = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false',
                            os.path.relpath(cand, ws)], cwd=ws, capture_output=True, text=True)
        # the verifier rejects a sorry as firmly as an error, so a sorry warning fails too; and
        # match `: error` as a prefix, since coded errors print as `: error(lean.unknownIdentifier):`
        errs = [l for l in (p.stdout + p.stderr).split('\n')
                if re.search(r': error\b', l) or re.search(r"declaration uses .sorry.", l)]
        if errs or p.returncode != 0:
            print('COMPILE FAILED (exit %d) — an error or a sorry; if the unpruned file was clean, '
                  'the prune removed something load-bearing. %s left unchanged:' % (p.returncode, dest))
            for l in (errs or (p.stdout + p.stderr).strip().split('\n')[-5:])[:10]:
                print('   ', l[:200])
            sys.exit(1)
        os.replace(cand, dest)
        cand = None
        print('wrote %s\ncompiles clean' % dest)
    finally:
        if cand and os.path.exists(cand):
            os.remove(cand)

if __name__ == '__main__':
    main()
