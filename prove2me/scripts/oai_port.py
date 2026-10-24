#!/usr/bin/env python3
"""Port an openai/math result for a published OAI goal into one solution file, then check it the
way the verifier does (locally; never submits).

usage: oai_port.py TARGET ROOT_MODULE SRC_LEAN_DIR OUT_DIR [--bundle Def_X ...] [--patches P.json]
                   [--root-compat] [--stdsimplex auto|structure|subtype|off] [--stdsimplex-inline]
                   [--no-check]

  TARGET        the published theorem, e.g. OAI.Saxl.saxl_conjecture (its statement and bundles
                must be in the workspace: fetch_theorems.py --names TARGET)
  ROOT_MODULE   the OpenAI module proving it, e.g. OAI.RepresentationTheory.Saxl.Main
  SRC_LEAN_DIR  the fetched lean/ tree (oai_fetch.py DEST ROOT_MODULE, then DEST/lean)
  --bundle      a published Definitions bundle the statement imports: its declarations are dropped
                from the port by full name (p2mlib.oaiport.drop_declarations)
  --patches     [{old, new, count, why}]: each must apply exactly `count` times (default 1)
  --root-compat the compatibility lemmas at the root, as before 2026-10-18; by default they live in
                namespace OAI (two bundles each declaring root `ite_eq_left` clash)
  --stdsimplex  the StdSimplex shim (lean/StdSimplexCompat.lean; p2mlib.oaiport.stdsimplex_mode):
                auto (default) applies it when the source uses `Convexity.StdSimplex`, giving our
                `Convexity.StdSimplex` the d13f23b API OpenAI uses; `subtype` also renames it to
                `OAI.SStd` (the subtype `stdSimplex`, for code that identifies the simplex with
                SimplexCategory.toTop.obj); `off` never. The published bundle
                Definitions.Def_OAIStdSimplexCompat is imported when it is in the workspace
                (Definitions/Def_OAIStdSimplexCompat.lean, published c7014b9a, the same text as
                lean/StdSimplexCompat.lean), else the shim is inlined; --stdsimplex-inline
                always inlines

Steps: merge the closure (build_solution's closure and merge.py, each module section-wrapped);
inline tactic macros; strip universe lists merge.py already declares; drop the bundles'
declarations; rename OpenAI's copy of the target `<name>_oai`; core rewrites, compat rewrites, guard renames (`prelude` -> `prelude_`),
the StdSimplex shim and patches; prepend the compatibility block; append `theorem solution : type_of% @T_oai := @T_oai`;
then (unless --no-check) compile the verifier's form (the statement imported, `theorem _check`),
-j1, and write OUT_DIR/result.json {secs (CPU), wall, errors, axioms, unknown, bytes, dropped}.
Rough rule: up to ~70–80 s local CPU passes the 300 s verifier; 90 s and slower timed out.
"""
import json
import os
import re
import resource
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import oaiport as O  # noqa: E402
from p2mlib.workspace import workspace  # noqa: E402

COMPAT = os.path.join(os.path.dirname(HERE), 'lean', 'compat_4_34.lean')


def port_text(target, root, src, bundles, patches=(), compat_ns='OAI', ws=None, stdsimplex='auto',
              stdsimplex_inline=False):
    """(solution text, number of modules, dropped declarations)."""
    import build_solution as BS
    from p2mlib.leantext import inline_tactic_macros
    ws = ws or workspace()
    mods = BS.closure(src, 'OAI', root.replace('.', '/') + '.lean', ['OAI'])
    import tempfile
    with tempfile.TemporaryDirectory() as work:
        wrapped = []
        for i, m in enumerate(mods):
            body = BS.module_body(open(m, encoding='utf-8').read())
            p = os.path.join(work, '%03d_%s' % (i, os.path.basename(m)))
            # merge.py parses the modules: without the import, Mathlib syntax fails to parse
            open(p, 'w', encoding='utf-8').write('import Mathlib\nsection\n' + body.rstrip() + '\nend\n')
            wrapped.append(p)
        merged = os.path.join(work, 'merged.lean')
        subprocess.run([sys.executable, os.path.join(HERE, 'merge.py'), merged] + wrapped,
                       check=True, capture_output=True)
        text = BS.module_body(open(merged, encoding='utf-8').read())
    text, _ = inline_tactic_macros(text)
    text = O.strip_declared_universes(text)
    names, anon = set(), set()
    for b in bundles:
        n, a = O.bundle_decl_names(open(os.path.join(ws, 'Definitions', b + '.lean'), encoding='utf-8').read())
        names |= n
        anon |= a
    text, dropped = O.drop_declarations(text, names, anon)
    text = O.rename_target(text, target)
    block, rewrites = O.compat_block(open(COMPAT, encoding='utf-8').read(), compat_ns)
    text = O.guard_renames(O.apply_rewrites(O.core_rewrites(text), rewrites))
    shim_bundle = os.path.exists(os.path.join(ws, *O.STDSIMPLEX_BUNDLE.split('.')) + '.lean')
    text, shim_imports, shim = O.stdsimplex_single(text, stdsimplex, shim_bundle and not stdsimplex_inline,
                                                   (names, anon))
    text = O.apply_patches(text, patches, route='single')
    t = BS.published(target)
    pre = [l for l in (t.get('preamble') or '').split('\n') if l.startswith('import ')]
    # a preamble may import only a few Mathlib modules; OpenAI's code was written against all of it
    if 'import Mathlib' not in pre:
        pre = ['import Mathlib'] + pre
    pre += [l for l in shim_imports if l not in pre]
    sol = ('\n'.join(pre) + '\n\n' + (shim + '\n' if shim else '') + block + '\n' + text.rstrip() + '\n\n'
           # no `open X in`: type_of% needs none, and a relative X fails at root level
           + 'theorem solution : type_of%% @%s_oai := @%s_oai\n' % (target, target))
    return sol, pre, len(mods), dropped


def check(sol, pre, target, out, ws=None):
    """Compile the verifier's form of `sol`, -j1; returns the result dict (CPU seconds)."""
    ws = ws or workspace()
    mod = 'Theorems.Thm_' + target.replace('.', '_')
    chk = sol.replace(pre[-1] + '\n', pre[-1] + '\nimport ' + mod + '\n', 1) + \
        '\ntheorem _check : type_of%% @%s := @solution\n#print axioms solution\n' % target
    chkp = os.path.join(out, 'Chk_%s.lean' % target.replace('.', '_'))
    open(chkp, 'w', encoding='utf-8').write(chk)
    ru0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.time()
    r = subprocess.run(['lake', 'env', 'lean', '-j1', '-DautoImplicit=false', chkp], cwd=ws,
                       capture_output=True, text=True)
    wall = time.time() - t0
    ru1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    # CPU time: the wall clock also counts time queued for a Lean slot (lean-cap)
    secs = (ru1.ru_utime - ru0.ru_utime) + (ru1.ru_stime - ru0.ru_stime)
    outp = r.stdout + r.stderr
    open(os.path.join(out, 'check.log'), 'w').write(outp)
    errs = [l for l in outp.split('\n') if ': error' in l]
    # A run that died (OOM-killed in lean.slice, signal, timeout) prints no error and no axioms;
    # its CPU time is lost too (systemd stops the whole scope, so lake dies before reaping lean and
    # RUSAGE_CHILDREN sees only lake: 0.9 s for an 800 s ThreeMachine run, 2026-10-23). Report it
    # as a failure, never as 0 errors.
    killed = r.returncode not in (0, 1)
    if killed:
        errs.insert(0, 'check run died: exit %d (OOM-kill in lean.slice? see journalctl --user); '
                    'secs is not its CPU time' % r.returncode)
    ax = [l for l in outp.split('\n') if 'depends on axioms' in l]
    return {'secs': None if killed else round(secs, 1), 'rc': r.returncode, 'wall': round(wall, 1), 'errors': len(errs),
            'axioms': ax[-1] if ax else None, 'error_lines': errs[:8],
            'unknown': sorted(set(re.findall(r'Unknown (?:identifier|constant) `([^`]+)`', outp)))}


def main(argv):
    if len(argv) < 4:
        sys.exit(__doc__)
    target, root, src, out = argv[:4]
    bundles = [argv[i + 1] for i, a in enumerate(argv) if a == '--bundle']
    patches = json.load(open(argv[argv.index('--patches') + 1])) if '--patches' in argv else []
    smode = argv[argv.index('--stdsimplex') + 1] if '--stdsimplex' in argv else 'auto'
    os.makedirs(out, exist_ok=True)
    try:
        sol, pre, nmods, dropped = port_text(target, root, src, bundles, patches,
                                             None if '--root-compat' in argv else 'OAI',
                                             stdsimplex=smode,
                                             stdsimplex_inline='--stdsimplex-inline' in argv)
    except O.PortError as e:
        sys.exit(str(e))
    solp = os.path.join(out, 'Sol_%s.lean' % target.replace('.', '_'))
    open(solp, 'w', encoding='utf-8').write(sol)
    res = {'target': target, 'modules': nmods, 'dropped': len(dropped), 'bytes': len(sol.encode())}
    if '--no-check' not in argv:
        res.update(check(sol, pre, target, out))
    json.dump(res, open(os.path.join(out, 'result.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != 'error_lines'}))
    for l in res.get('error_lines', []):
        print('  ', l[:200])


if __name__ == '__main__':
    main(sys.argv[1:])
