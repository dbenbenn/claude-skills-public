#!/usr/bin/env python3
"""Build the solution file for one published theorem from a Lean development, ready to submit.

usage: build_solution.py TARGET MODULE OUT --root REPO --merge-dir DIR [--merge-dir DIR ...]
                         [--drop NAME ...] [--package PKG]   (default: first component of MODULE)

  TARGET     the published theorem, e.g. QFS.theoremOneFour_univ
  MODULE     the development file that proves it (relative to REPO)
  --merge-dir  directories (relative to REPO) whose modules are merged whole when MODULE imports
             them, directly or not; every other module is left to resolve_imports.py, which
             imports what is published and Proved (and not deprecated) and copies in the rest
  --drop     declarations to remove from the merge so that resolve_imports imports them instead:
             the mission's OTHER milestones once they are Proved, so the graph records the
             dependency rather than an inlined copy (a missing edge)

The steps, each an existing tracked tool:
  1. the import closure of MODULE inside the merge dirs, in dependency order, each module's
     imports stripped and its text wrapped in `section ... end` (module-level `open`s otherwise
     leak into later modules and change what a bare name resolves to);
  2. merge.py (refuses conflicting duplicates);
  3. the `solution` wrapper, generated from the PUBLISHED formal_statement: the statement renamed
     to a root-level `solution`, its `namespace NS` replaced by `open NS` so its bare names still
     resolve, proved by applying the development's own theorem, with the preamble's `open`s;
  4. resolve_imports.py, then prune_solution.py --check (compiles with autoImplicit off, as the
     verifier does). Submit the result with submit_solution.py.
"""
import argparse, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from p2m import call
from prune_solution import parse


def published(name):
    r = [t for t in (call('GET', '/theorems?theorem_name=' + name).get('theorems') or [])
         if t.get('theorem_name') == name]
    if not r:
        sys.exit('no published theorem named ' + name)
    return r[0]


def namespaces_by_line(lines):
    """The namespace in force at each line, from `namespace` / `section` / `end` lines."""
    stack, out = [], []
    for l in lines:
        out.append('.'.join(n for k, n in stack if k == 'ns'))
        m = re.match(r'^\s*(namespace|section|end)\b\s*(\S*)', l)
        if not m:
            continue
        if m.group(1) == 'namespace':
            stack += [('ns', p) for p in m.group(2).split('.')]
        elif m.group(1) == 'section':
            stack.append(('sec', m.group(2)))
        elif stack:
            # `end A.B` closes the namespaces A and B; a bare `end` closes the innermost section
            for _ in range(max(1, m.group(2).count('.') + 1) if m.group(2) else 1):
                if stack:
                    stack.pop()
    return out


def drop_declarations(lines, drops):
    """(lines without the declarations to be imported instead, [full names dropped]). A qualified
    drop takes the declaration of exactly that name when there is one (Lusin-Novikov, 2026-10-03:
    matching the last component also dropped `Dev.PartB.cover` and an alias to it, both still
    needed); otherwise, as before, every declaration with that last component (a development copy
    under another namespace)."""
    ns = namespaces_by_line(lines)
    decls = []
    for name, _k, st, en, _attr in parse(lines):
        head = next((i for i in range(st, en) if name in lines[i]), st)
        full = name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(x for x in (ns[head], name) if x)
        decls.append((full, st, en))
    spans, dropped = [], []
    for d in drops:
        hit = [x for x in decls if x[0] == d] or [x for x in decls if x[0].split('.')[-1] == d.split('.')[-1]]
        for full, st, en in hit:
            if (st, en) not in spans:
                spans.append((st, en)); dropped.append(full)
    lines = list(lines)
    for st, en in sorted(spans, reverse=True):
        del lines[st:en]
    return lines, dropped


def missing_statements(root, drops):
    """The qualified --drop names whose published statement is not in ROOT/Theorems: resolve_imports
    can only import a theorem whose file is there, so they are fetched first."""
    return [d for d in drops if '.' in d and not os.path.exists(
        os.path.join(root, 'Theorems', 'Thm_%s.lean' % d.replace('.', '_')))]


def package_of(module):
    """The Lean package a development module belongs to: the first component of its path
    (`Solutions/LNS/Proofs.lean` -> `Solutions`), whose imports the closure follows."""
    return module.replace(os.sep, '/').lstrip('./').split('/')[0]


def closure(repo, pkg, module, dirs):
    """Modules (paths) to merge, dependencies first."""
    order, seen = [], set()

    def visit(path):
        if path in seen:
            return
        seen.add(path)
        for m in re.findall(r'^import\s+(\S+)', open(path, encoding='utf-8').read(), re.M):
            if not m.startswith(pkg + '.'):
                continue
            p = os.path.join(repo, *m.split('.')) + '.lean'
            rel = os.path.relpath(p, repo)
            if os.path.exists(p) and any(rel.startswith(d.rstrip('/') + '/') for d in dirs):
                visit(p)
        order.append(path)
    visit(os.path.join(repo, module))
    return order


def drop_redeclared_universes(body, stmt):
    """`stmt` without the universe names `body` already declares at its top level (outside every
    `section`/`namespace`): the published statement brings its own `universe u v`, and a
    development that declares the same at the top of its file made the wrapper fail with "a
    universe level named `u` has already been declared" (Garrido full strength, 2026-10-04)."""
    depth, top = 0, set()
    for l in body.split('\n'):
        s = l.strip()
        if re.match(r'(section|namespace)\b', s):
            depth += 1
        elif re.match(r'end\b', s):
            depth = max(0, depth - 1)
        elif depth == 0 and s.startswith('universe '):
            top.update(s.split()[1:])
    out = []
    for l in stmt.split('\n'):
        s = l.strip()
        if s.startswith('universe '):
            new = [n for n in s.split()[1:] if n not in top]
            if not new:
                continue
            l = 'universe ' + ' '.join(new)
        out.append(l)
    return '\n'.join(out)


def external_imports(mods, drop=()):
    """The `Definitions.*` and `Theorems.*` modules the merged modules import, in first-seen order.
    The merge strips every import line and resolve_imports.py recovers only names it can trace; a
    bundle used under `open` (bare `HB` from the Monod bundle) it cannot, so these are passed on as
    --module (dense-subgroups, 2026-10-03). A --drop target's own statement module is left out:
    resolve_imports imports it only if it is Proved. Unused theorem imports are pruned later."""
    dropped = {'Theorems.Thm_' + d.replace('.', '_') for d in drop}
    out = []
    for p in mods:
        for m in re.findall(r'^import\s+(\S+)', open(p, encoding='utf-8').read(), re.M):
            if m.startswith(('Definitions.', 'Theorems.')) and m not in dropped and m not in out:
                out.append(m)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('target'); ap.add_argument('module'); ap.add_argument('out')
    ap.add_argument('--root', required=True)
    ap.add_argument('--merge-dir', action='append', required=True)
    ap.add_argument('--drop', action='append', default=[])
    ap.add_argument('--package', help='default: the first component of MODULE\'s path')
    a = ap.parse_args()
    a.package = a.package or package_of(a.module)
    need = missing_statements(a.root, a.drop)
    if need:
        print('fetching the statements of', ' '.join(need))
        subprocess.run([sys.executable, os.path.join(HERE, 'fetch_theorems.py'), '--names'] + need,
                       check=True, cwd=a.root)
    ns, short = a.target.rsplit('.', 1)
    work = a.out + '.work'
    os.makedirs(work, exist_ok=True)

    # 1. wrapped copies of the closure
    mods = closure(a.root, a.package, a.module, a.merge_dir)
    wrapped = []
    for i, p in enumerate(mods):
        body = '\n'.join(l for l in open(p, encoding='utf-8').read().split('\n')
                         if not l.startswith('import '))
        w = os.path.join(work, '%02d_%s' % (i, os.path.basename(p)))
        open(w, 'w', encoding='utf-8').write('section\n' + body.strip() + '\n\nend\n')
        wrapped.append(w)
    print('merging %d module(s): %s' % (len(mods), ' '.join(os.path.relpath(m, a.root) for m in mods)))

    # 2. merge
    merged = os.path.join(work, 'merged.lean')
    subprocess.run([sys.executable, os.path.join(HERE, 'merge.py'), merged] + wrapped, check=True)
    text = '\n'.join(l for l in open(merged, encoding='utf-8').read().split('\n')
                     if not l.startswith('import '))
    # the verifier rejects macro registration; a development's tactic macros are inlined
    from p2mlib.leantext import inline_tactic_macros
    text, macros = inline_tactic_macros(text)
    for n in macros:
        print('  inlined tactic macro', n)

    # drop the declarations to be imported instead
    if a.drop:
        lines, dropped = drop_declarations(text.split('\n'), a.drop)
        for n in dropped:
            print('  drop', n)
        text = '\n'.join(lines)

    # 3. the solution wrapper, from the published statement
    t = published(a.target)
    fs = t['formal_statement']
    # a root-level `solution` (prune_solution and the verifier look for exactly that name); the
    # statement's own `namespace NS ... end NS` becomes `open NS`, so its bare names still resolve
    fs = '\n'.join(l for l in fs.split('\n') if l.strip() not in ('namespace ' + ns, 'end ' + ns))
    fs2, n = re.subn(r'\btheorem\s+' + re.escape(short) + r'\b', 'theorem solution', fs, count=1)
    if n != 1:
        sys.exit('cannot find `theorem %s` in the published formal_statement' % short)
    fs2, n = re.subn(r':=\s*by\s+sorry\s*', ':= by\n  apply %s <;> assumption\n' % a.target, fs2, count=1)
    if n != 1:
        sys.exit('cannot find `:= by sorry` in the published formal_statement')
    fs2 = drop_redeclared_universes(text, fs2)
    opens = [l for l in (t.get('preamble') or '').split('\n') if l.startswith('open')]
    text = (text.rstrip() + '\n\nsection\n' + '\n'.join(opens + ['open ' + ns]) + '\n\n'
            + fs2.strip() + '\n\nend\n')
    body = os.path.join(work, 'body.lean')
    open(body, 'w', encoding='utf-8').write(text)

    # 4. resolve, prune, check
    mods_args = [x for m in external_imports(mods, a.drop) for x in ('--module', m)]
    subprocess.run([sys.executable, os.path.join(HERE, 'resolve_imports.py'), body, a.out,
                    '--src', os.path.join(a.root, a.package), '--ns', ns] + mods_args, check=True)
    subprocess.run([sys.executable, os.path.join(HERE, 'prune_solution.py'), a.out, '--check'], check=True)
    print('built %s' % a.out)


if __name__ == '__main__':
    main()
