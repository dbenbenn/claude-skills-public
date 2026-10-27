#!/usr/bin/env python3
"""Compile ported modules (oai_port_modules.py) one at a time, -j1, in import order, into the
workspace build tree, printing one `lake build`-format line per module with its CPU seconds (what
carve.parse_build_log reads); then write the elaboration log the carve cost model wants.

usage: oai_build_modules.py FOLDER ROOT [--force] [--log BUILD.log] [--elab-log OUT.log]
                            [--overhead 3.0] [--ws WORKSPACE]
       oai_build_modules.py --elab-only BUILD.log OUT.log [--overhead 3.0]

  ROOT        the root module's short name (Main for Solutions.FOLDER.Main); dotted names allowed
              for nested folders
  --force     rebuild every module (default: a module whose source is newer than its .olean, or
              one of whose imports was rebuilt or has a newer .olean)
  --log       also write the build lines to this file (what --elab-log reads)
  --elab-log  the build lines with OVERHEAD seconds (the Mathlib import, about 3 s here) taken off
              each module (floor 0.1 s), for config `build_logs` (module_costs adds a fixed 0.5 s);
              replayed modules have no time, so keep the earlier logs too (carve_prep.py config
              reads every build_elab*.log, later ones winning) or pass --force

One Lean process at a time (the box cap is shared). A failed module's outputs are removed and the
script exits 1 with its first errors.

Each module compiles through the compiled LeanInfo (p2mlib.leaninfo.build_module, 2026-10-27): the
same elaboration writes the .olean/.ilean and caches the reading `carve.py graph` needs, which
before cost a second elaboration of every module. The logged seconds are LeanInfo's build_ms (its
import, elaboration and output writing; about `lean`'s CPU time plus 0.4-1 s). Without the compiled
tool it falls back to `lean -o`."""
import os
import re
import resource
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import leaninfo  # noqa: E402


def opt(argv, name, default=None):
    return argv[argv.index(name) + 1] if name in argv else default


def module_imports(d, pre, m):
    """The modules under `pre` that module m (folder `d`) imports directly."""
    t = open(os.path.join(d, *m.split('.')) + '.lean', encoding='utf-8').read()
    return re.findall(r"^import %s\.([\w.']+)" % re.escape(pre), t, re.M)


def module_order(d, pre, root):
    """The modules ROOT imports under `pre` (folder `d`), dependencies first, ROOT last."""
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for x in module_imports(d, pre, m):
            visit(x)
        order.append(m)
    visit(root)
    return order


def stale(m, src, olean, imports, rebuilt, olean_of):
    """Must module m be compiled again? Its .olean is missing or older than its source, or an
    import of it was rebuilt in this run or has a newer .olean (Problem340 2026-10-24: only a
    module's own source was compared, so its importers kept stale .oleans after a fix)."""
    if not os.path.exists(olean) or os.path.getmtime(olean) <= os.path.getmtime(src):
        return True
    t = os.path.getmtime(olean)
    return any(x in rebuilt or not os.path.exists(olean_of(x)) or os.path.getmtime(olean_of(x)) > t
               for x in imports)


def elab_lines(build_log, overhead=3.0):
    """`lake build` lines with `overhead` seconds off each module's time (floor 0.1 s)."""
    out = []
    for l in build_log.split('\n'):
        m = re.search(r'Built (\S+) \(([\d.]+)s\)', l)
        if m:
            out.append('✔ Built %s (%.2fs)' % (m.group(1), max(float(m.group(2)) - overhead, 0.1)))
    return '\n'.join(out) + '\n'


def build(ws, folder, root, force=False, log=None):
    pre = 'Solutions.' + folder
    d = os.path.join(ws, 'Solutions', folder)
    out_root = os.path.join(ws, '.lake', 'build', 'lib', 'lean')
    order = module_order(d, pre, root)
    lines, total = [], 0.0
    rebuilt = set()

    def olean_of(m):
        return os.path.join(out_root, *(pre + '.' + m).split('.')) + '.olean'

    def say(s):
        print(s, flush=True)
        lines.append(s)
        if log:
            open(log, 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
    for i, m in enumerate(order):
        mod = pre + '.' + m
        out = os.path.join(out_root, *mod.split('.'))
        os.makedirs(os.path.dirname(out), exist_ok=True)
        src = os.path.join(d, *m.split('.')) + '.lean'
        if not force and not stale(m, src, out + '.olean', module_imports(d, pre, m), rebuilt, olean_of):
            say('✔ [%d/%d] Replayed %s' % (i + 1, len(order), mod))
            continue
        res = leaninfo.build_module(src, mod, out + '.olean', out + '.ilean', ws=ws)
        if res is not None:
            ok, cpu, errs = res
            total += cpu
            if not ok:
                say('✖ [%d/%d] FAILED %s (%.1fs)' % (i + 1, len(order), mod, cpu))
                print('\n'.join(errs[:10]))
                return False, lines
            rebuilt.add(m)
            say('✔ [%d/%d] Built %s (%.1fs)' % (i + 1, len(order), mod, cpu))
            continue
        ru0 = resource.getrusage(resource.RUSAGE_CHILDREN)
        r = subprocess.run(['lake', 'env', 'lean', '-j1', '-DautoImplicit=false', '-R', ws,
                            '-o', out + '.olean', '-i', out + '.ilean', src], cwd=ws,
                           capture_output=True, text=True)
        ru1 = resource.getrusage(resource.RUSAGE_CHILDREN)
        cpu = (ru1.ru_utime - ru0.ru_utime) + (ru1.ru_stime - ru0.ru_stime)
        total += cpu
        o = r.stdout + r.stderr
        errs = [l for l in o.split('\n') if ': error' in l]
        if r.returncode or errs:
            say('✖ [%d/%d] FAILED %s (%.1fs)' % (i + 1, len(order), mod, cpu))
            print('\n'.join((errs or [o[-2000:]])[:10]))
            for f in (out + '.olean', out + '.ilean'):
                if os.path.exists(f):
                    os.remove(f)
            return False, lines
        rebuilt.add(m)
        say('✔ [%d/%d] Built %s (%.1fs)' % (i + 1, len(order), mod, cpu))
    print('total CPU %.1f s over %d modules' % (total, len(order)))
    return True, lines


def main(argv):
    oh = float(opt(argv, '--overhead', 3.0))
    if '--elab-only' in argv:
        i = argv.index('--elab-only')
        src, out = argv[i + 1:i + 3]
        open(out, 'w', encoding='utf-8').write(elab_lines(open(src, encoding='utf-8').read(), oh))
        return
    valued = ('--log', '--elab-log', '--overhead', '--ws')
    skip = {argv.index(o) + 1 for o in valued if o in argv}
    pos = [a for i, a in enumerate(argv) if not a.startswith('--') and i not in skip]
    if len(pos) != 2:
        sys.exit(__doc__)
    from p2mlib.workspace import workspace
    from p2mlib import runlock
    ws = opt(argv, '--ws') or workspace()
    runlock.hold(runlock.build_key(ws, pos[0]), 'oai_build_modules.py ' + ' '.join(argv))
    ok, lines = build(ws, pos[0], pos[1], '--force' in argv,
                      opt(argv, '--log'))
    if ok and '--elab-log' in argv:
        open(opt(argv, '--elab-log'), 'w', encoding='utf-8').write(elab_lines('\n'.join(lines), oh))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main(sys.argv[1:])
