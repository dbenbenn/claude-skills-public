#!/usr/bin/env python3
"""Compile every generated bundle, statement stub and piece of a carve (carve.py gen), one Lean at
a time, -j1, in publish order (p2mlib.carve.publish_order), and record CPU seconds and errors.

usage: carve_measure.py CONFIG.json [--force] [--keep-going] [--dir D] [--no-repair]
                         [--no-edge-check] [--drop-false-edges] [--allow-false-edges]
                         [--kinds bundle,statement|piece]
  -> <work>/times.json, the input of `carve.py split CONFIG.json TIMES.json`,
     <work>/edges.json and <work>/false_edges.json (the edge check)

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
file's text (sha1), and that of every carve module it imports (transitively), is unchanged and it passed. Stops at the first failure unless --keep-going.

The edge check (on by default; --no-edge-check skips it) runs after each file compiles: every
`import Theorems.*` of a bundle, statement or piece, and every `import Definitions.*` of a bundle
naming another bundle of this carve, must be used (p2mlib.edgecheck: lean/EdgeUses.lean reads
the compiled .olean -- a piece compiles as module EdgeChk.Chk_<name> for this -- and lists the
constants of each import that the declarations use, from `solution` for a piece; each import it
finds unused is confirmed by one compile without it, which catches a use that leaves no constant,
such as `dsimp only [rfl_lemma]`). The
carver infers edges partly from source text, and a false one compiles fine and goes into the
published graph (PosteriorReplicas 2026-10-23). Results are cached by the file's text and its
checked imports in <work>/edges.json; <work>/false_edges.json lists each false edge (item, file,
import, the statement it names, a bundle to import instead if any) and the statements no file
imports any more (orphaned: not a target or forced, so drop them from the plan). A false theorem
import (`import Theorems.*`, a theorem-graph edge) fails the run unless --allow-false-edges; a false
definitions import is reported and kept (cutting one broke dependants, oaiq-039/075).
--drop-false-edges cuts each false theorem import that needs no replacement, records the cut in <work>/repairs.json (re-applied after every `carve.py gen`, like
the context-command repairs) and re-measures the file.

--kinds measures only those items (carve_pipeline's overlap mode: bundles and statements first, which
freeze at publish, then the pieces against their .olean files from the first run in D/olean). Without
pieces, no statement is reported orphaned (nothing that imports one has been read yet).
"""
import hashlib
import importlib.util
import json
import os
import re
import resource
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import carve as C, edgecheck as EC, leaninfo, localcheck as L, repair as RP  # noqa: E402

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



def reapply(text, cuts):
    """(text with the recorded cuts made, the cuts that are stale). `carve.py gen` already makes
    them, so a cut whose text is gone counts as made; stale is one still there that no longer
    matches as a command or binder group."""
    new, _, stale = RP.apply_cuts(text, cuts)
    return new, [c for c in stale if c in text]

class Measure:
    def __init__(self, cfg_path, d=None):
        self.cfg = CLI.load_config(cfg_path)
        self.ws = self.cfg['src']
        # Lean runs from a Lake workspace: the carve's source, or (a fixture development with no
        # toolchain of its own) the prove2me workspace
        self.lean_ws = self.ws if os.path.exists(os.path.join(self.ws, 'lean-toolchain')) \
            else leaninfo.workspace()
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
        self.edges_path = os.path.join(self.cfg['work'], 'edges.json')
        self.edges = json.load(open(self.edges_path)) if os.path.exists(self.edges_path) else {}
        self.bundle_names = [b['name'] for b in self.plan.get('bundles', [])]
        self.edge_dir = os.path.join(self.d, 'edge')
        self.allow_false = False

    def env(self):
        lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=self.lean_ws,
                            capture_output=True, text=True).stdout.strip()
        return dict(os.environ, LEAN_PATH=self.olean + ':' + lp)

    def run(self, path, module, env):
        args = ['lean', '-j1', '-DautoImplicit=false']
        if module:
            out = os.path.join(self.olean, *module.split('.'))
            os.makedirs(os.path.dirname(out), exist_ok=True)
            # a failed compile must not leave an earlier plan's module of this name behind for later
            # files to import (oaiq-065: a re-plan's Sa010 failed, the old Sa010 .olean stayed)
            for ext in ('.olean', '.ilean'):
                if os.path.exists(out + ext):
                    os.remove(out + ext)
            sp = os.path.join(self.stage, *module.split('.')) + '.lean'
            os.makedirs(os.path.dirname(sp), exist_ok=True)
            shutil.copy(path, sp)
            path = sp
            args += ['-R', self.stage, '-o', out + '.olean', '-i', out + '.ilean']
        r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
        r = subprocess.run(args + [path], cwd=self.lean_ws, env=env, capture_output=True, text=True)
        r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
        cpu = r1.ru_utime - r0.ru_utime + r1.ru_stime - r0.ru_stime
        o = r.stdout + r.stderr
        errs = [l for l in o.split('\n') if ': error' in l] or ([o[-1500:]] if r.returncode else [])
        return {'secs': round(cpu, 1), 'ok': r.returncode == 0 and not errs, 'errors': errs[:8],
                'axioms': [l for l in o.split('\n') if 'depends on axioms' in l]}, o

    def apply_recorded(self, src):
        name = os.path.basename(src)
        text = open(src, encoding='utf-8').read()
        new, stale = reapply(text, self.repairs.get(name, []))
        if new != text:
            open(src, 'w', encoding='utf-8').write(new)
        for c in stale:
            print('STALE REPAIR', name, '|', c[:120], flush=True)

    def record(self, src, cuts):
        self.repairs.setdefault(os.path.basename(src), []).extend(cuts)
        json.dump(self.repairs, open(self.rp_path, 'w'), indent=1, ensure_ascii=False)
        for c in cuts:
            print('REPAIR', os.path.basename(src), '|', c.replace('\n', ' ')[:160], flush=True)

    def chk_text(self, n, sol=None):
        name = C.statement_name(self.plan, n)
        if sol is None:
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

    def cache_key(self, path, seen=None):
        """sha1 of the file and, transitively, of the carve's own modules it imports (out/lib): a re-plan
        that changes an imported bundle invalidates the cached result (oaiq-010: `holderShift` moved out
        of a bundle's reach, three statements kept their old "ok" and failed to publish)."""
        seen = {} if seen is None else seen
        if path in seen:
            return seen[path]
        seen[path] = ''
        text = open(path, 'rb').read()
        parts = [hashlib.sha1(text).hexdigest()]
        for line in text.decode('utf-8', 'replace').split('\n'):
            mm = re.match(r'import\s+(?:Definitions|Theorems)\.(\S+)\s*$', line)
            if mm:
                dep = os.path.join(self.lib, mm.group(1) + '.lean')
                if os.path.exists(dep):
                    parts.append(self.cache_key(dep, seen))
        k = parts[0] if len(parts) == 1 else hashlib.sha1('\0'.join(parts).encode()).hexdigest()
        seen[path] = k
        return k

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
            k = self.cache_key(path)
            old = self.times.get(item)
            if old and old.get('key') == k and old.get('ok') and not force:
                return old
            # a piece compiles to an .olean too (EdgeChk.*), which the edge check reads
            r, out = self.run(path, mod or self.chk_module(n), env)
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

    # ------------------------------------------------------------ the edge check

    def module_file(self, m):
        """The source of a module a carved file imports: this carve's out/lib, else the workspace."""
        rel = m.split('.', 1)[1] if '.' in m else m
        p = os.path.join(self.lib, rel + '.lean')
        return p if os.path.exists(p) else os.path.join(self.ws, *m.split('.')) + '.lean'

    def imports_of(self, m):
        p = self.module_file(m)
        return EC.imports(open(p, encoding='utf-8').read()) if os.path.exists(p) else []

    def compiles(self, item, text, env):
        """Does this variant of the item's file compile (a piece: in the verifier's form)?"""
        kind, n = item.split(':', 1)
        if kind == 'piece':
            text = self.chk_text(n, sol=text)
        os.makedirs(self.edge_dir, exist_ok=True)
        path = os.path.join(self.edge_dir, 'Edge_%s.lean' % C.slug(n))
        open(path, 'w', encoding='utf-8').write(text)
        r, _ = self.run(path, None, env)
        self.edge_compile_secs += r['secs']
        return r['ok']

    def chk_module(self, n):
        return 'EdgeChk.Chk_' + C.slug(C.statement_name(self.plan, n))

    def compiled_module(self, item, env):
        """(module, roots) whose .olean the edge check reads; a piece's verifier-form file is
        recompiled when a cached measurement left no .olean behind."""
        kind, n = item.split(':', 1)
        _, mod = self.item_files(kind, n)
        if mod:
            return mod, []
        mod = self.chk_module(n)
        if not os.path.exists(os.path.join(self.olean, *mod.split('.')) + '.olean'):
            path = os.path.join(self.chk, 'Chk_%s.lean' % C.slug(C.statement_name(self.plan, n)))
            open(path, 'w', encoding='utf-8').write(self.chk_text(n))
            self.run(path, mod, env)
        return mod, ['solution']

    def edge_check(self, item, env, force=False):
        """The cached verdict on the file's graph edges (p2mlib.edgecheck.check), or a fresh one."""
        kind, n = item.split(':', 1)
        src, _ = self.item_files(kind, n)
        text = open(src, encoding='utf-8').read()
        cands = EC.candidates(text, kind, self.bundle_names)
        key = hashlib.sha1((text + '\0' + ' '.join(cands)).encode()).hexdigest()
        old = self.edges.get(item)
        if old and old.get('key') == key and not force:
            return old
        uses, secs = None, 0.0
        if cands:
            r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
            uses = EC.scan(*self.compiled_module(item, env), env, self.lean_ws)
            r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
            secs = r1.ru_utime - r0.ru_utime + r1.ru_stime - r0.ru_stime
        self.edge_compile_secs = 0.0
        res = EC.check(text, cands, uses, lambda t: self.compiles(item, t, env), self.imports_of)
        res.update(key=key, file=os.path.basename(src), scan_secs=round(secs, 1),
                   compile_secs=round(self.edge_compile_secs, 1))
        self.edges[item] = res
        json.dump(self.edges, open(self.edges_path, 'w'), indent=1)
        return res

    def drop_edges(self, item, res):
        """Cut the item's false imports (when no bundle must replace them) and record the cuts."""
        cuts = drop_cuts(res)
        if not cuts:
            return False
        kind, n = item.split(':', 1)
        src, _ = self.item_files(kind, n)
        new, applied, _ = RP.apply_cuts(open(src, encoding='utf-8').read(), cuts)
        if not applied:
            return False
        open(src, 'w', encoding='utf-8').write(new)
        self.record(src, applied)
        return True

    def run_all(self, force=False, keep_going=False, repair=True, edges=True, drop=False, kinds=None):
        copy_published(self.ws, self.olean, imported_modules(self.cfg, self.plan))
        env = self.env()
        ok = True
        for wave in C.publish_order(self.plan, self.ext)['waves']:
            for item in wave:
                kind, n = item.split(':', 1)
                if kind == 'statement' and n in self.ext:
                    continue
                if kinds and kind not in kinds:
                    continue
                for attempt in range(2):
                    r = self.measure(item, env, force, repair)
                    self.times[item] = r
                    json.dump(self.times, open(self.times_path, 'w'), indent=1)
                    print('%-9s %6.1f s %s %s %s' % (kind, r['secs'], 'ok' if r['ok'] else 'FAIL', n,
                                                     (r['errors'][:1] or [''])[0][-200:]), flush=True)
                    if not (r['ok'] and edges):
                        break
                    e = self.edge_check(item, env, force)
                    for m, v in e['imports'].items():
                        if v != 'used':
                            print('  edge  %-7s %s -> %s%s' % (v.upper(), n, m, (
                                ' (import %s instead)' % ', '.join(e['restore'][m])) if m in e['restore'] else ''),
                                flush=True)
                    if not (e['false'] and drop and attempt == 0 and self.drop_edges(item, e)):
                        break
                if not r['ok']:
                    ok = False
                    if not keep_going:
                        return False
        if edges:
            rep = edge_report(self.plan, {i: e for i, e in self.edges.items() if i in self.times})
            if kinds and 'piece' not in kinds:
                rep['orphaned_statements'] = []
            json.dump(rep, open(os.path.join(self.cfg['work'], 'false_edges.json'), 'w'), indent=1)
            print_edge_report(rep)
            if failing_false_edges(rep) and not self.allow_false:
                ok = False
        return ok


def drop_cuts(res):
    """The repair cuts that remove a file's false theorem imports (`import Theorems.*`, the
    theorem-graph edges). A false definitions import is left in place: cutting or replacing it broke
    files that used it transitively or named its instances in `attribute [-instance]` lines (oaiq-039,
    oaiq-075), and it is no graph edge. A statement import that needs a bundle in its place is left to
    a person (None)."""
    graph = [m for m in res.get('false') or () if m.startswith('Theorems.')]
    if not graph:
        return None
    cuts = []
    for m in graph:
        if res.get('restore', {}).get(m):
            return None
        cuts.append('import ' + m)
    return cuts


def failing_false_edges(rep):
    """The false edges that fail a measure: theorem-graph edges only (definitions imports are
    reported and kept, 2026-10-28)."""
    return [f for f in rep['false_edges'] if f.get('graph_edge')]


def edge_report(plan, edges):
    """{'false_edges': [...], 'dead_imports': [...], 'orphaned_statements': [...]} from the
    edge-check records. A dead import (only declarations `solution` never reaches use it) is not a
    false edge yet: prune the file (prune_solution.py) and measure again."""
    by_module = {}
    for n in list(plan.get('stubs', {})) + list(plan.get('external', [])):
        by_module['Theorems.Thm_' + C.slug(C.statement_name(plan, n))] = n
    out, dead, imported = [], [], set()
    for item in sorted(edges):
        e = edges[item]
        for m, v in e.get('imports', {}).items():
            if m in e.get('false', []):
                fix = ('replace it by `import %s`' % ', '.join(e['restore'][m])) if e.get('restore', {}).get(m) \
                    else 'drop the import line (--drop-false-edges)'
                graph = m.startswith('Theorems.')
                if not graph:
                    fix = 'none needed: a definitions import is no theorem-graph edge (kept)'
                out.append({'item': item, 'file': e.get('file'), 'import': m, 'verdict': v,
                            'statement': by_module.get(m), 'restore': e.get('restore', {}).get(m, []),
                            'fix': fix, 'graph_edge': graph})
            else:
                imported.add(m)
                if v == 'dead':
                    dead.append({'item': item, 'file': e.get('file'), 'import': m,
                                 'statement': by_module.get(m)})
    keep = set(plan.get('targets', [])) | set(plan.get('forced', [])) | set(plan.get('external', []))
    orphans = sorted(n for n in plan.get('stubs', {})
                     if n not in keep and 'Theorems.Thm_' + C.slug(C.statement_name(plan, n)) not in imported)
    return {'false_edges': out, 'dead_imports': dead, 'orphaned_statements': orphans}


def print_edge_report(rep):
    if not rep['false_edges']:
        print('edge check: no false edges', flush=True)
    for f in rep['false_edges']:
        print('%s %s (%s): import %s [%s]; fix: %s' % ('FALSE EDGE' if f.get('graph_edge') else 'unused definitions import',
                                                    f['item'], f['file'], f['import'], f['verdict'], f['fix']), flush=True)
    for f in rep.get('dead_imports', []):
        print('DEAD IMPORT %s (%s): import %s is used only by declarations `solution` never reaches;'
              ' prune them (prune_solution.py)' % (f['item'], f['file'], f['import']), flush=True)
    for n in rep['orphaned_statements']:
        print('ORPHANED STATEMENT %s: no file imports it; drop it from the plan' % n, flush=True)


def main(argv):
    pos = [a for i, a in enumerate(argv) if not a.startswith('--') and (i == 0 or argv[i - 1] not in ('--dir', '--kinds'))]
    if len(pos) != 1:
        sys.exit(__doc__)
    from p2mlib import runlock
    runlock.hold(runlock.dir_key('measure', pos[0]), 'carve_measure.py ' + ' '.join(argv))
    m = Measure(pos[0], opt(argv, '--dir'))
    m.allow_false = '--allow-false-edges' in argv
    kinds = [k for k in (opt(argv, '--kinds') or '').split(',') if k] or None
    ok = m.run_all('--force' in argv, '--keep-going' in argv, '--no-repair' not in argv,
                   '--no-edge-check' not in argv, '--drop-false-edges' in argv, kinds)
    print('done' if ok else 'FAILED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main(sys.argv[1:])
