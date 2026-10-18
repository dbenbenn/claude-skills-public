#!/usr/bin/env python3
"""Compile every generated bundle, statement stub and piece of a carve (carve.py gen), one Lean at
a time, -j1, in publish order (p2mlib.carve.publish_order), and record CPU seconds and errors.

usage: carve_measure.py CONFIG.json [--force] [--keep-going] [--dir D] [--no-repair]
  -> <work>/times.json, the input of `carve.py split CONFIG.json TIMES.json`

Bundles and stubs compile to .olean files in D/olean (D defaults to the config's directory), which
LEAN_PATH searches before the workspace, standing in for publishing; the workspace's Definitions/
and Theorems/ folders are never touched. Pieces compile in the verifier's form: solution + the
statement + `theorem _check : type_of% @T := @solution` (p2mlib.localcheck.server_check_text),
written to D/chk/. An `external` target's statement is the workspace's Theorems file.

Lean looks up `Definitions.X` only in the first LEAN_PATH entry holding a Definitions/ folder, so
every published module the carve imports is copied from the workspace build into D/olean: the
modules of config/plan `external_defs` and `external_theorems`, the external targets' statements,
and config `extra_olean_modules` (their own imports, when those are not in the workspace build).
A module missing from the workspace build that is already in D/olean is left alone (a carve's own
core split, measured first into the same D/olean).

A file that fails on a context command (a `variable` binder, `open`, `include`, ...) is repaired by
cutting it (p2mlib.repair, up to 20 cuts); the cuts are recorded in <work>/repairs.json and
re-applied on every later run, since `carve.py gen` rewrites the files. A result is reused while the
file's text (sha1) is unchanged and it passed. Stops at the first failure unless --keep-going.
"""
import hashlib
import importlib.util
import json
import os
import resource
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import carve as C, localcheck as L, repair as RP  # noqa: E402

_spec = importlib.util.spec_from_file_location('carve_cli', os.path.join(HERE, 'carve.py'))
CLI = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(CLI)


def opt(argv, name, default=None):
    return argv[argv.index(name) + 1] if name in argv else default


def imported_modules(cfg, plan):
    """The published modules the carve's files import, to copy into the private olean dir."""
    ext = set(plan.get('external', []))
    mods = set((plan.get('external_defs') or cfg.get('external_defs') or {}).values())
    mods |= set((plan.get('external_theorems') or cfg.get('external_theorems') or {}).values())
    mods |= set(cfg.get('extra_olean_modules') or [])
    mods |= {'Theorems.Thm_' + C.slug(n) for n in ext}
    return sorted(mods)


def copy_published(ws, olean, mods):
    wb = os.path.join(ws, '.lake', 'build', 'lib', 'lean')
    for m in mods:
        for ext in ('.olean', '.ilean'):
            src, dst = os.path.join(wb, *m.split('.')) + ext, os.path.join(olean, *m.split('.')) + ext
            if not os.path.exists(src) and os.path.exists(dst):
                continue
            if not os.path.exists(src):
                sys.exit('%s is not built in the workspace (fetch_theorems.py, then lake build %s)' % (src, m))
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy(src, dst)


class Measure:
    def __init__(self, cfg_path, d=None):
        self.cfg = CLI.load_config(cfg_path)
        self.ws = self.cfg['src']
        self.d = os.path.abspath(d or os.path.dirname(os.path.abspath(cfg_path)))
        self.plan = json.load(open(CLI.plan_path(self.cfg)))
        self.lib = os.path.join(self.cfg['out'], 'lib')
        self.sol = os.path.join(self.cfg['out'], 'solutions')
        self.olean, self.chk, self.stage = (os.path.join(self.d, x) for x in ('olean', 'chk', 'stage'))
        for x in (self.olean, self.chk, self.stage):
            os.makedirs(x, exist_ok=True)
        self.ext = set(self.plan.get('external', []))
        self.times_path = os.path.join(self.cfg['work'], 'times.json')
        self.times = json.load(open(self.times_path)) if os.path.exists(self.times_path) else {}
        self.rp_path = os.path.join(self.cfg['work'], 'repairs.json')
        self.repairs = json.load(open(self.rp_path)) if os.path.exists(self.rp_path) else {}

    def env(self):
        lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=self.ws,
                            capture_output=True, text=True).stdout.strip()
        return dict(os.environ, LEAN_PATH=self.olean + ':' + lp)

    def run(self, path, module, env):
        args = ['lean', '-j1', '-DautoImplicit=false']
        if module:
            out = os.path.join(self.olean, *module.split('.'))
            os.makedirs(os.path.dirname(out), exist_ok=True)
            sp = os.path.join(self.stage, *module.split('.')) + '.lean'
            os.makedirs(os.path.dirname(sp), exist_ok=True)
            shutil.copy(path, sp)
            path = sp
            args += ['-R', self.stage, '-o', out + '.olean', '-i', out + '.ilean']
        r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
        r = subprocess.run(args + [path], cwd=self.ws, env=env, capture_output=True, text=True)
        r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
        cpu = r1.ru_utime - r0.ru_utime + r1.ru_stime - r0.ru_stime
        o = r.stdout + r.stderr
        errs = [l for l in o.split('\n') if ': error' in l] or ([o[-1500:]] if r.returncode else [])
        return {'secs': round(cpu, 1), 'ok': r.returncode == 0 and not errs, 'errors': errs[:8],
                'axioms': [l for l in o.split('\n') if 'depends on axioms' in l]}, o

    def apply_recorded(self, src):
        name = os.path.basename(src)
        text = open(src, encoding='utf-8').read()
        new, _, stale = RP.apply_cuts(text, self.repairs.get(name, []))
        if new != text:
            open(src, 'w', encoding='utf-8').write(new)
        for c in stale:
            print('STALE REPAIR', name, '|', c[:120], flush=True)

    def record(self, src, cuts):
        self.repairs.setdefault(os.path.basename(src), []).extend(cuts)
        json.dump(self.repairs, open(self.rp_path, 'w'), indent=1, ensure_ascii=False)
        for c in cuts:
            print('REPAIR', os.path.basename(src), '|', c.replace('\n', ' ')[:160], flush=True)

    def chk_text(self, n):
        name = C.statement_name(self.plan, n)
        sol = open(os.path.join(self.sol, 'Sol_%s.lean' % C.slug(name)), encoding='utf-8').read()
        sp = os.path.join(self.ws, 'Theorems', 'Thm_%s.lean' % C.slug(name)) if n in self.ext else \
            os.path.join(self.lib, 'Thm_%s.lean' % C.slug(name))
        stub = open(sp, encoding='utf-8').read().split('\n')
        pre = ''.join(l + '\n' for l in stub if l.startswith('import '))
        body = '\n'.join(l for l in stub if not l.startswith('import '))
        return L.server_check_text(sol, pre, body, name) + '#print axioms solution\n'

    def item_files(self, kind, n):
        """(source file, module or None for a piece)."""
        if kind == 'bundle':
            return os.path.join(self.lib, 'Def_%s.lean' % n), 'Definitions.Def_' + n
        s = C.slug(C.statement_name(self.plan, n))
        if kind == 'statement':
            return os.path.join(self.lib, 'Thm_%s.lean' % s), 'Theorems.Thm_' + s
        return os.path.join(self.sol, 'Sol_%s.lean' % s), None

    def measure(self, item, env, force=False, repair=True):
        kind, n = item.split(':', 1)
        src, mod = self.item_files(kind, n)
        self.apply_recorded(src)
        r = None
        for _ in range(21):
            if mod:
                path = src
            else:
                path = os.path.join(self.chk, 'Chk_%s.lean' % C.slug(C.statement_name(self.plan, n)))
                open(path, 'w', encoding='utf-8').write(self.chk_text(n))
            k = hashlib.sha1(open(path, 'rb').read()).hexdigest()
            old = self.times.get(item)
            if old and old.get('key') == k and old.get('ok') and not force:
                return old
            r, out = self.run(path, mod, env)
            r['key'] = k
            if r['ok'] or not repair:
                break
            rp = RP.repair(open(path, encoding='utf-8').read(), out, statement=(kind == 'statement'))
            if not rp:
                break
            new, cut = rp
            if mod:
                open(src, 'w', encoding='utf-8').write(new)
            else:
                sol_new, applied, _ = RP.apply_cuts(open(src, encoding='utf-8').read(), cut)
                if not applied:
                    break
                open(src, 'w', encoding='utf-8').write(sol_new)
            self.record(src, cut)
        return r

    def run_all(self, force=False, keep_going=False, repair=True):
        copy_published(self.ws, self.olean, imported_modules(self.cfg, self.plan))
        env = self.env()
        ok = True
        for wave in C.publish_order(self.plan, self.ext)['waves']:
            for item in wave:
                kind, n = item.split(':', 1)
                if kind == 'statement' and n in self.ext:
                    continue
                r = self.measure(item, env, force, repair)
                self.times[item] = r
                json.dump(self.times, open(self.times_path, 'w'), indent=1)
                print('%-9s %6.1f s %s %s %s' % (kind, r['secs'], 'ok' if r['ok'] else 'FAIL', n,
                                                 (r['errors'][:1] or [''])[0][-200:]), flush=True)
                if not r['ok']:
                    ok = False
                    if not keep_going:
                        return False
        return ok


def main(argv):
    pos = [a for i, a in enumerate(argv) if not a.startswith('--') and (i == 0 or argv[i - 1] != '--dir')]
    if len(pos) != 1:
        sys.exit(__doc__)
    m = Measure(pos[0], opt(argv, '--dir'))
    ok = m.run_all('--force' in argv, '--keep-going' in argv, '--no-repair' not in argv)
    print('done' if ok else 'FAILED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main(sys.argv[1:])
