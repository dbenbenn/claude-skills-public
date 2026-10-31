#!/usr/bin/env python3
"""Port openai/math modules into the workspace as Lean modules, for carving (the module route; the
single-file route is oai_port.py).

usage: oai_port_modules.py LEAN_ROOT FOLDER PREFIX [PREFIX ...] [--patches P.json] [--header H.lean]
                           [--compat-ns NS | --root-compat] [--compat FILE] [--ws WORKSPACE]
                           [--stdsimplex auto|structure|subtype|off] [--compat-imports narrow|M1,M2,…]
                           [--unif-integrable on|off]

  LEAN_ROOT   the fetched lean/ tree (oai_fetch.py DEST ROOT_MODULE, then DEST/lean)
  FOLDER      the workspace folder: modules land in Solutions/FOLDER/ as Solutions.FOLDER.*
  PREFIX      OpenAI module prefixes to port (every module under each, e.g. OAI.Analysis.SepQuot);
              a nested Sub/X.lean becomes Sub_X.lean; an import of an OpenAI module under no
              prefix is an error (add its prefix)
  --patches   [{old, new, count, why}]: each applies exactly `count` times over all files (default
              1), every mismatch reported; patches written for the single file: carve_prep.py
              filter-patches first
  --header    extra lines after the imports (after the linter-off lines) of every module
  --compat-ns the namespace of the Compat module's lemmas (default OAI, which every ported module
              is inside); `alias` lines become rewrites of the sources (p2mlib.oaiport.compat_block)
  --root-compat  the old root-level block (two bundles both declaring root `ite_eq_left` clash)
  --compat-imports  Compat imports these Mathlib modules (`narrow`: oaiport.COMPAT_NARROW_IMPORTS) instead of
              all of Mathlib, which puts every instance in scope of every module (CStarMatrix breaks
              Matrix.mul_apply: Problem336 IncidenceCirculation, 2026-10-25)
  --compat    the compatibility block (default lean/compat_4_34.lean in this skill)
  --stdsimplex the StdSimplex shim (p2mlib.oaiport.stdsimplex_mode): auto (default) adds the module
              StdSimplexCompat (lean/StdSimplexCompat.lean: the d13f23b `Convexity.StdSimplex` API
              our Mathlib lacks) and imports it in each module using `Convexity.StdSimplex`;
              `subtype` also renames `Convexity.StdSimplex` to `OAI.SStd` (the subtype
              `stdSimplex`, for SimplexCategory.toTop code); `off` never. Once the shim bundle
              Definitions.Def_OAIStdSimplexCompat is in the workspace, carve_prep.py config makes
              its declarations external, so the carve imports it. carve_prep.py filter-patches
              takes the same option
  --unif-integrable on|off (default off) the uniform integrability shim: `on` adds the module
              UnifIntegrableCompat (lean/UnifIntegrableCompat.lean: d13f23b's `UnifIntegrable`,
              two-component `UniformIntegrable` and ℝ≥0∞-`UnifTight` as OAI.* declarations that shadow
              Mathlib's inside `namespace OAI`, with d13f23b's API) and imports it in each module naming
              them (p2mlib.oaiport.unifint_rewrite). carve_prep.py filter-patches takes the same option

Files are rewritten only when their text changes, so oai_build_modules.py rebuilds only those.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import oaiport as O  # noqa: E402
from p2mlib.workspace import workspace  # noqa: E402

COMPAT = os.path.join(os.path.dirname(HERE), 'lean', 'compat_4_34.lean')


def opt(argv, name, default=None):
    return argv[argv.index(name) + 1] if name in argv else default


def write_changed(out, files):
    """Write each file whose text differs; returns the names written."""
    os.makedirs(out, exist_ok=True)
    changed = []
    for f, t in sorted(files.items()):
        p = os.path.join(out, f)
        if not (os.path.exists(p) and open(p, encoding='utf-8').read() == t):
            open(p, 'w', encoding='utf-8').write(t)
            changed.append(f)
    return changed


def main(argv):
    valued = ('--patches', '--header', '--compat-ns', '--compat', '--ws', '--stdsimplex', '--compat-imports',
              '--unif-integrable')
    skip = {argv.index(o) + 1 for o in valued if o in argv}
    pos = [a for i, a in enumerate(argv) if not a.startswith('--') and i not in skip]
    if len(pos) < 3:
        sys.exit(__doc__)
    lean_root, folder, prefixes = pos[0], pos[1], pos[2:]
    ws = opt(argv, '--ws') or workspace()
    patches = json.load(open(opt(argv, '--patches'))) if '--patches' in argv else []
    header = open(opt(argv, '--header'), encoding='utf-8').read() if '--header' in argv else ''
    ns = None if '--root-compat' in argv else opt(argv, '--compat-ns', 'OAI')
    ci = opt(argv, '--compat-imports')
    cimp = O.COMPAT_NARROW_IMPORTS if ci == 'narrow' else (ci.split(',') if ci else None)
    try:
        files = O.module_files(O.module_sources(lean_root, prefixes), 'Solutions.' + folder, patches,
                               open(opt(argv, '--compat', COMPAT), encoding='utf-8').read(), ns, header,
                               opt(argv, '--stdsimplex', 'auto'), cimp, opt(argv, '--unif-integrable', 'off'))
    except O.PortError as e:
        sys.exit(str(e))
    out = os.path.join(ws, 'Solutions', folder)
    changed = write_changed(out, files)
    print('%d modules -> %s (%d rewritten)' % (len(files), out, len(changed)))


if __name__ == '__main__':
    main(sys.argv[1:])
