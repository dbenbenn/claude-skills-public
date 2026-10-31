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
              a replayed module keeps its time from the previous --elab-log or --log, else from the
              LeanInfo cache entry its compile wrote (so `--redo build` restores a log an older
              version cut short); carve_prep.py config reads every
              build_elab*.log, later ones winning

One Lean process at a time (the box cap is shared). A failed module's outputs are removed and its
first errors printed; the build goes on with every module that does not import a failed one (those
are listed as skipped), so one run reports every failing module, and the script then exits 1
(oaiq-038/048: stopping at the first failure cost a 5-13 min rebuild per drift fix).

A failed module whose errors carry the "not type-correct under the `implicit` transparency level" note
is compiled once more as a temporary copy with try_module.py's module-scope `set_option
backward.isDefEq.respectTransparency false`; when that copy builds, its .olean stands in for the
module's (marked by a `.transparency` file beside it, so it is never replayed), its importers build in
the same run, and the module is listed last as building only with the option: the port still needs
that patch, so the run still exits 1 (q128-finitistic-retry: 15 such modules surfaced one round at a
time, over seven rounds and ~3 h, since a failed module skips its importers).

Each module compiles through the compiled LeanInfo (p2mlib.leaninfo.build_module, 2026-10-27): the
same elaboration writes the .olean/.ilean and caches the reading `carve.py graph` needs, which
before cost a second elaboration of every module. The logged seconds are LeanInfo's build_ms (its
import, elaboration and output writing; about `lean`'s CPU time plus 0.4-1 s). Without the compiled
tool it falls back to `lean -o`."""
import json
import os
import re
import resource
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import leaninfo  # noqa: E402
sys.path.insert(0, HERE)
import try_module  # noqa: E402


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


BUILT = re.compile(r'Built (\S+) \(([\d.]+)s\)')


def previous_times(log, elab_log, overhead=3.0):
    """{module: seconds, overhead off} from an earlier run's elab log and build log (a failed run
    writes only the build log; it is the newer one when both exist)."""
    t = {}
    for f, raw in ((elab_log, False), (log, True)):
        if f and os.path.exists(f):
            text = open(f, encoding='utf-8').read()
            for m, secs in BUILT.findall(elab_lines(text, overhead) if raw else text):
                t[m] = float(secs)
    return t


def cached_build_secs(ws, folder):
    """mod -> the build seconds LeanInfo recorded when it compiled the module (its cache entry,
    p2mlib.leaninfo.build_module), or None."""
    def f(mod):
        src = os.path.join(ws, *mod.split('.')) + '.lean'
        try:
            key = leaninfo._key(src, False, ws, (), True, mod, True, leaninfo.BUILD_OPTIONS)
            ms = json.load(open(os.path.join(leaninfo.CACHE, key + '.json'))).get('build_ms')
        except (OSError, ValueError):
            return None
        return ms / 1000.0 if ms else None
    return f


def merged_elab_lines(lines, previous, overhead=3.0, cached=None):
    """elab_lines of this run, with a replayed module's time from `previous`, else from `cached`
    (2026-10-29: a resumed build wrote only what it rebuilt, and config costed every other module at
    the default 2 s)."""
    out = []
    for l in lines:
        m = BUILT.search(l)
        if m:
            out.append('✔ Built %s (%.2fs)' % (m.group(1), max(float(m.group(2)) - overhead, 0.1)))
            continue
        m = re.search(r'Replayed (\S+)', l)
        if not m:
            continue
        if m.group(1) in previous:
            out.append('✔ Built %s (%.2fs)' % (m.group(1), previous[m.group(1)]))
            continue
        secs = cached(m.group(1)) if cached else None
        if secs:
            out.append('✔ Built %s (%.2fs)' % (m.group(1), max(secs - overhead, 0.1)))
    return '\n'.join(out) + '\n'


TRANSPARENCY_NOTE = 'not type-correct under the `implicit` transparency level'
STAND_IN = '.transparency'      # beside an .olean built from the option copy: compile the module again


def drop_outputs(out):
    for ext in ('.olean', '.ilean', STAND_IN):
        if os.path.exists(out + ext):
            os.remove(out + ext)


def build_with_option(ws, src, mod, out):
    """q128-finitistic-retry (2026-10-30): compile a temporary copy of `src` with try_module's
    module-scope transparency option as `mod`, writing out.olean/.ilean (then marked as a stand-in).
    Returns (built, CPU seconds, the copy's errors)."""
    text, _ = try_module.with_option(open(src, encoding='utf-8').read())
    root = tempfile.mkdtemp(prefix='oai_build_option_')
    try:
        copy = os.path.join(root, *mod.split('.')) + '.lean'      # -R root names it `mod`
        os.makedirs(os.path.dirname(copy))
        open(copy, 'w', encoding='utf-8').write(text)
        drop_outputs(out)
        ru0 = resource.getrusage(resource.RUSAGE_CHILDREN)
        o = try_module.compile_(copy, ws, run=subprocess.run,
                                extra=['-R', root, '-o', out + '.olean', '-i', out + '.ilean'])
        ru1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    finally:
        shutil.rmtree(root, ignore_errors=True)
    cpu = (ru1.ru_utime - ru0.ru_utime) + (ru1.ru_stime - ru0.ru_stime)
    errs = [e for _, e in try_module.errors(o)]
    if errs or not os.path.exists(out + '.olean'):       # no .olean and no error: the run died
        drop_outputs(out)
        return False, cpu, errs or [o[-2000:]]
    open(out + STAND_IN, 'w').write('built from a copy with `%s`; the port needs that patch\n' % try_module.OPT)
    return True, cpu, []


def build(ws, folder, root, force=False, log=None):
    pre = 'Solutions.' + folder
    d = os.path.join(ws, 'Solutions', folder)
    out_root = os.path.join(ws, '.lake', 'build', 'lib', 'lean')
    order = module_order(d, pre, root)
    lines, total = [], 0.0
    rebuilt = set()
    failed, skipped = [], set()       # keep going past a failure (oaiq-038/048): report them all
    with_option = []                  # built only from the transparency-option copy (q128)

    def olean_of(m):
        return os.path.join(out_root, *(pre + '.' + m).split('.')) + '.olean'

    def say(s):
        print(s, flush=True)
        lines.append(s)
        if log:
            open(log, 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
    def fail(i, mod, cpu, errs, src, out, log_text=''):
        """Report a failed module, unless it fails only the transparency check (q128): then its
        option copy stands in. Returns the CPU seconds of that extra compile."""
        if TRANSPARENCY_NOTE in '\n'.join(errs) + log_text:
            built, ocpu, oerrs = build_with_option(ws, src, mod, out)
            if built:
                say('✖ [%d/%d] OPTION %s (%.1fs + %.1fs): builds only with the transparency option (`%s` '
                    'at module scope); needs a patch' % (i + 1, len(order), mod, cpu, ocpu, try_module.OPT))
                with_option.append(mod)
                return ocpu
            say('✖ [%d/%d] FAILED %s (%.1fs; with the transparency option too, %d error%s)' % (
                i + 1, len(order), mod, cpu, len(oerrs), '' if len(oerrs) == 1 else 's'))
        else:
            ocpu = 0.0
            say('✖ [%d/%d] FAILED %s (%.1fs)' % (i + 1, len(order), mod, cpu))
        print('\n'.join(errs[:10]), flush=True)
        failed.append(mod)
        return ocpu
    for i, m in enumerate(order):
        mod = pre + '.' + m
        out = os.path.join(out_root, *mod.split('.'))
        os.makedirs(os.path.dirname(out), exist_ok=True)
        src = os.path.join(d, *m.split('.')) + '.lean'
        bad = [x for x in module_imports(d, pre, m) if x in skipped or pre + '.' + x in failed]
        if bad:
            skipped.add(m)
            say('- [%d/%d] Skipped %s (imports %s, which did not build)' % (i + 1, len(order), mod, pre + '.' + bad[0]))
            continue
        # a stand-in .olean from the option copy (q128) never replays: the module is compiled again
        if not force and not os.path.exists(out + STAND_IN) and \
                not stale(m, src, out + '.olean', module_imports(d, pre, m), rebuilt, olean_of):
            say('✔ [%d/%d] Replayed %s' % (i + 1, len(order), mod))
            continue
        if os.path.exists(out + STAND_IN):
            drop_outputs(out)          # the real compile's outcome alone decides what is left
        res = leaninfo.build_module(src, mod, out + '.olean', out + '.ilean', ws=ws)
        if res is not None:
            ok, cpu, errs = res
            total += cpu
            if not ok:
                total += fail(i, mod, cpu, errs, src, out)
                if mod in with_option:
                    rebuilt.add(m)
                continue
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
            drop_outputs(out)
            # the note is on a later line than `: error`, so the whole output is searched
            total += fail(i, mod, cpu, errs or [o[-2000:]], src, out, o)
            if mod in with_option:
                rebuilt.add(m)
            continue
        rebuilt.add(m)
        say('✔ [%d/%d] Built %s (%.1fs)' % (i + 1, len(order), mod, cpu))
    print('total CPU %.1f s over %d modules' % (total, len(order)))
    if failed:
        print('%d modules failed: %s; %d skipped because they import one' % (
            len(failed), ', '.join(failed), len(skipped)), flush=True)
    if with_option:
        # last, so the pipeline's failure message (the log's tail) shows it
        print('%d module%s build only with the transparency option (`%s` at module scope, before `namespace '
              'OAI`; their importers built against that copy), needs a patch each: %s' % (
                  len(with_option), '' if len(with_option) == 1 else 's', try_module.OPT, ', '.join(with_option)),
              flush=True)
    return not (failed or with_option), lines


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
    prev = previous_times(opt(argv, '--log'), opt(argv, '--elab-log'), oh)
    ok, lines = build(ws, pos[0], pos[1], '--force' in argv,
                      opt(argv, '--log'))
    if '--elab-log' in argv:          # a failed round too: the next one replays what this one built
        open(opt(argv, '--elab-log'), 'w', encoding='utf-8').write(
            merged_elab_lines(lines, prev, oh, cached_build_secs(ws, pos[0])))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main(sys.argv[1:])
