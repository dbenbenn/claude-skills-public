#!/usr/bin/env python3
"""Compile every generated bundle, statement stub and piece of a carve (carve.py gen), one Lean at
a time, -j1, in publish order (p2mlib.carve.publish_order), and record CPU seconds and errors. Lean
runs with the verifier's options (p2mlib.localcheck.VERIFIER_FLAGS): autoImplicit off and synchronous
elaboration (Elab.async=false; q128: heartbeat timeouts the verifier reported showed only so).

usage: carve_measure.py CONFIG.json [--force] [--keep-going] [--dir D] [--no-repair] [--jobs N]
                         [--no-edge-check] [--drop-false-edges] [--allow-false-edges]
                         [--kinds bundle,statement|piece] [--only ITEM,...]
       carve_measure.py CONFIG.json --profile bundle:NAME[,statement:NAME ...] [--dir D]
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
file's text (sha1), and that of every carve module it imports (transitively), is unchanged and it passed,
and the Lean options are the same (a result from before Elab.async=false is measured once more). Stops at the first failure unless --keep-going.

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

--profile bundle:NAME[,...] compiles each once more with Lean's profiler (into D/profile, not D/olean) and
records the diagnosis (serialization-, kernel- or elaboration-bound, naming the declaration) in
<work>/profiles.json: carve_pipeline's calibrate asks for it when splitting cannot shrink a bundle.

--only ITEM[,...] measures only those items (carve_pipeline: the pieces of statements bundles wait for, first).
--kinds measures only those items (carve_pipeline's overlap mode: bundles and statements first, which
freeze at publish, then the pieces against their .olean files from the first run in D/olean). Without
pieces, no statement is reported orphaned (nothing that imports one has been read yet).

Each times.json record also holds the item's import closure: closure_bytes, the .olean bytes of its
transitive Solutions/Definitions/Theorems imports (not Mathlib, not its own .olean; a piece's are those
of its verifier-form file), closure_modules, and closure_missing (imports with no .olean found). One
over CLOSURE_WARN_BYTES is reported with a WARNING line and in a summary at the end; it never fails
the run (q149/oaiq-106).

Each record also holds rss_mib, the run's own peak memory (os.wait4; run_lean): carve_pipeline holds a piece over
PIECE_RSS_LIMIT back and splits it (q153 2026-11-08: the verifier's workers kill files peaking over ~7 GiB, and
`import Mathlib` alone takes 6.5). A cached piece record without it, of RSS_REMEASURE_SECS or more, is measured
again unless the verifier accepted the piece (publish/run_state.json). --jobs N measures the pieces of each wave N
at a time (nothing imports a piece; the lean-cap wrapper queues the Lean runs); everything else stays in order.

The JSON state files (times.json, repairs.json, edges.json, false_edges.json, profiles.json) are
written atomically (write_json). One found cut off mid-entry (q149: a disk-full crash) keeps its
complete entries; the original is kept as <file>.truncated, and the dropped items are measured again.
"""
import contextlib
import hashlib
import importlib.util
import json
import os
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import carve as C, edgecheck as EC, leaninfo, localcheck as L, repair as RP  # noqa: E402

_spec = importlib.util.spec_from_file_location('carve_cli', os.path.join(HERE, 'carve.py'))
CLI = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(CLI)


RSS_REMEASURE_SECS = 15   # a piece measured before peak memory was recorded (rss_mib) is measured again from this
                          # many seconds: q153 (2026-11-08) pieces under 20 s peaked under 7,000 MiB, all of them


from p2mlib.localcheck import run_lean  # noqa: E402  (tests patch carve_measure.run_lean)


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


def published_closure(ws, mods):
    """`mods` with every Definitions/Theorems module their workspace sources import, transitively (sorted). q227
    (2026-11): the carve imported Def_CKSBondiPenrose_002, which imports Def_CKSBondiPenrose; only the first was
    copied, and every file importing it failed on the missing .olean. A module without a workspace source (a
    carve's own core split, already in D/olean) adds nothing."""
    out, todo = set(), list(mods)
    while todo:
        m = todo.pop()
        if m in out:
            continue
        out.add(m)
        p = os.path.join(ws, *m.split('.')) + '.lean'
        if os.path.exists(p):
            for line in open(p, encoding='utf-8', errors='replace'):
                mm = re.match(r'import\s+((?:Definitions|Theorems)\.\S+)', line)
                if mm:
                    todo.append(mm.group(1))
    return sorted(out)


def copy_published(ws, olean, mods):
    wb = os.path.join(ws, '.lake', 'build', 'lib', 'lean')
    for m in published_closure(ws, mods):
        for ext in ('.olean', '.ilean'):
            src, dst = os.path.join(wb, *m.split('.')) + ext, os.path.join(olean, *m.split('.')) + ext
            if not os.path.exists(src) and os.path.exists(dst):
                continue
            if not os.path.exists(src):
                sys.exit('%s is not built in the workspace (fetch_theorems.py, then lake build %s)' % (src, m))
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy(src, dst)



# q149/oaiq-106 (2026-11): every bundle the platform published had an import closure of at most
# 0.74 GB (OAIQ106D199); D186 (0.87 GB, 17 MB itself) timed out ("Module compilation timed out after
# 300s") 30+ times. One carve's correlation, not a confirmed platform limit: reported, never enforced.
CLOSURE_WARN_BYTES = 700 * 10 ** 6
CLOSURE_ROOTS = ('Solutions.', 'Definitions.', 'Theorems.')


def write_json(path, obj, **kw):
    """json.dump through a temporary file in the same directory, fsync'd, then os.replace: a crash
    mid-write (q149: disk full) leaves the previous file whole, never one cut mid-entry."""
    tmp = '%s.tmp%d' % (path, os.getpid())
    try:
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(obj, f, **kw)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)


def _skip_ws(text, i):
    while i < len(text) and text[i] in ' \t\r\n':
        i += 1
    return i


def recover_object(text):
    """The complete top-level entries of a JSON object cut off mid-way ({} if none), or None when the
    text is no object."""
    dec = json.JSONDecoder()
    i = _skip_ws(text, 0)
    if text[i:i + 1] != '{':
        return None
    out, i = {}, i + 1
    while True:
        try:
            k, i = dec.raw_decode(text, _skip_ws(text, i))
            i = _skip_ws(text, i)
            if not isinstance(k, str) or text[i:i + 1] != ':':
                return out
            v, i = dec.raw_decode(text, _skip_ws(text, i + 1))
        except ValueError:
            return out
        out[k] = v
        i = _skip_ws(text, i)
        if text[i:i + 1] != ',':
            return out
        i += 1


def load_json(path, default):
    """A JSON state file, or `default` when there is none. One cut off mid-entry (q149: a disk-full
    crash truncated times.json) keeps its complete entries: the original is kept as
    <path>.truncated (.1, .2, ... beside an earlier one) and the repaired file written in its place."""
    if not os.path.exists(path):
        return default
    text = open(path, encoding='utf-8').read()
    try:
        return json.loads(text)
    except ValueError:
        got = recover_object(text)
    if got is None:
        sys.exit('%s is not valid JSON and holds no object to recover; repair it by hand (drop the partial '
                 'entry and close the JSON) or delete it to measure everything again' % path)
    keep, k = path + '.truncated', 0
    while os.path.exists(keep):
        k += 1
        keep = '%s.truncated.%d' % (path, k)
    shutil.copy(path, keep)
    write_json(path, got, indent=1)
    print('WARNING %s was cut off mid-entry: kept its %d complete entries and dropped the partial one '
          '(original kept as %s)' % (path, len(got), keep), file=sys.stderr, flush=True)
    return got


def import_closure(text, imports_of, olean_of):
    """{closure_bytes, closure_modules[, closure_missing]} for a file's text: the .olean bytes of its
    transitive Solutions/Definitions/Theorems imports, each once (imports_of(module) -> its imports,
    olean_of(module) -> its .olean path or None)."""
    seen, todo = set(), [m for m in EC.imports(text) if m.startswith(CLOSURE_ROOTS)]
    while todo:
        m = todo.pop()
        if m not in seen:
            seen.add(m)
            todo.extend(x for x in imports_of(m) if x.startswith(CLOSURE_ROOTS) and x not in seen)
    size, missing = 0, 0
    for m in seen:
        p = olean_of(m)
        if p:
            size += os.path.getsize(p)
        else:
            missing += 1
    rec = {'closure_bytes': size, 'closure_modules': len(seen)}
    if missing:
        rec['closure_missing'] = missing
    return rec


def gb(n):
    return '%.2f GB' % (n / 1e9)


def reapply(text, cuts):
    """(text with the recorded cuts made, the cuts that are stale). `carve.py gen` already makes
    them, so a cut whose text is gone counts as made; stale is one still there that no longer
    matches as a command or binder group."""
    new, _, stale = RP.apply_cuts(text, cuts)
    return new, [c for c in stale if c in text]

class Measure:
    jobs = 1        # --jobs: pieces of one wave measured at once (nothing imports a piece); Lean's own cap queues them

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
        self.times = load_json(self.times_path, {})
        self.rp_path = os.path.join(self.cfg['work'], 'repairs.json')
        self.repairs = load_json(self.rp_path, {})
        self.edges_path = os.path.join(self.cfg['work'], 'edges.json')
        self.edges = load_json(self.edges_path, {})
        self.bundle_names = [b['name'] for b in self.plan.get('bundles', [])]
        self.edge_dir = os.path.join(self.d, 'edge')
        self.allow_false = False

    def env(self):
        lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=self.lean_ws,
                            capture_output=True, text=True).stdout.strip()
        return dict(os.environ, LEAN_PATH=self.olean + ':' + lp)

    def run(self, path, module, env):
        args = ['lean', '-j1', *L.VERIFIER_FLAGS]       # the verifier's elaboration (q128)
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
        with self.unlocked():
            rc, o, cpu, rss = run_lean(args + [path], self.lean_ws, env)
        errs = [l for l in o.split('\n') if ': error' in l] or ([o[-1500:]] if rc else [])
        return {'secs': round(cpu, 1), 'rss_mib': rss, 'ok': rc == 0 and not errs, 'errors': errs[:8],
                'axioms': [l for l in o.split('\n') if 'depends on axioms' in l]}, o

    # -- parallel pieces: one lock serializes everything but the Lean runs themselves (run() lets it go)
    def _par(self):
        if not hasattr(self, '_lock'):
            self._lock, self._tls = threading.Lock(), threading.local()
        return self._lock, self._tls

    @contextlib.contextmanager
    def unlocked(self):
        lock, tls = self._par()
        held = getattr(tls, 'held', False)
        if held:
            tls.held = False
            lock.release()
        try:
            yield
        finally:
            if held:
                lock.acquire()
                tls.held = True

    @contextlib.contextmanager
    def locked(self):
        lock, tls = self._par()
        with lock:
            tls.held = True
            try:
                yield
            finally:
                tls.held = False

    def one(self, item, env, force, repair, edges, drop):
        """Measure one item (and its edge check), record it in times.json; returns its record."""
        kind, n = item.split(':', 1)
        for attempt in range(2):
            r = self.measure(item, env, force, repair)
            self.times[item] = r
            write_json(self.times_path, self.times, indent=1)
            print('%-9s %6.1f s %s %s %s%s' % (kind, r['secs'], 'ok' if r['ok'] else 'FAIL', n,
                                               (r['errors'][:1] or [''])[0][-200:],
                                               ' %d MiB' % r['rss_mib'] if r.get('rss_mib') else ''), flush=True)
            if attempt == 0 and r.get('closure_bytes', 0) > CLOSURE_WARN_BYTES:
                print('  WARNING import closure %s over the %.1f GB soft limit: %s (%d modules); '
                      'q149/oaiq-106 bundles over ~0.74 GB timed out publishing (report only)' % (
                          gb(r['closure_bytes']), CLOSURE_WARN_BYTES / 1e9, item,
                          r.get('closure_modules', 0)), flush=True)
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
        return r

    def needs_rss(self, item, old):
        """Is a cached piece from before peak memory was recorded to be measured again? (A bundle or statement
        is frozen once published; a fast piece cannot be near the verifier's memory.)"""
        return (item.startswith('piece:') and 'rss_mib' not in old and (old.get('secs') or 0) >= RSS_REMEASURE_SECS
                and item not in self.live_pieces())

    def live_pieces(self):
        """The pieces the verifier accepted (publish/run_state.json `live`): their peak no longer matters."""
        if '_live' not in self.__dict__:
            try:
                st = json.load(open(os.path.join(self.d, 'publish', 'run_state.json')))
                self._live = {x for x, v in st.items() if x.startswith('piece:') and v.get('state') == 'live'}
            except (OSError, ValueError):
                self._live = set()
        return self._live

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
        write_json(self.rp_path, self.repairs, indent=1, ensure_ascii=False)
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

    def cache_key(self, path):
        """text_key with the compile flags: q128 (2026-10-30): an "ok" measured before Elab.async=false
        (keyed by the text alone) is no evidence the verifier accepts the file (F028 was one), so it is
        measured once more; each later run reuses it while the text and the flags are unchanged."""
        return hashlib.sha1((self.text_key(path) + '\0' + ' '.join(L.VERIFIER_FLAGS)).encode()).hexdigest()

    def text_key(self, path, seen=None):
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
                    parts.append(self.text_key(dep, seen))
        k = parts[0] if len(parts) == 1 else hashlib.sha1('\0'.join(parts).encode()).hexdigest()
        seen[path] = k
        return k

    def olean_path(self, module):
        return os.path.join(self.olean, *module.split('.')) + '.olean'

    def has_olean(self, module):
        """May a cached "ok" stand for a module (a bundle or statement)? Only while its .olean is there:
        `run` deletes it before every compile, and a failed compile, a repair loop whose cut text
        matches an earlier "ok" (oaiq-096: a bundle cut by a repair, the next run took it "ok" from
        times.json), or a deleted olean/ dir leaves the entry without its output, and every importer
        then fails "object file ... does not exist". A piece (module None) has no output of its own. And only
        while it is a whole .olean (leaninfo.olean_ok): q172's power cut left zero-byte ones, and the importers
        of the cached statements failed "invalid header"."""
        return module is None or leaninfo.olean_ok(self.olean_path(module))

    def measure(self, item, env, force=False, repair=True):
        """The item's record (compiled, or cached), with its import closure (import_closure)."""
        r = self._measure(item, env, force, repair)
        if r is not None:
            r.update(self.import_closure(item) or {})
        return r

    def _measure(self, item, env, force=False, repair=True):
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
            if old and old.get('key') == k and old.get('ok') and not force and self.has_olean(mod) \
                    and not self.needs_rss(item, old):
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

    def module_olean(self, m):
        """A module's .olean: this carve's D/olean (its own modules and the published ones copied
        there), else the workspace build; None when neither has it."""
        for root in (self.olean, os.path.join(self.ws, '.lake', 'build', 'lib', 'lean')):
            p = os.path.join(root, *m.split('.')) + '.olean'
            if os.path.exists(p):
                return p
        return None

    def module_imports(self, m):
        """imports_of, cached while the source file is unchanged (closures share most modules)."""
        p = self.module_file(m)
        try:
            st = os.stat(p)
        except OSError:
            return []
        memo = self.__dict__.setdefault('_imports_memo', {})
        k = (p, st.st_mtime_ns, st.st_size)
        if k not in memo:
            memo[k] = EC.imports(open(p, encoding='utf-8').read())
        return memo[k]

    def import_closure(self, item):
        """import_closure of the item's file (a piece: its verifier-form file, D/chk), or None when
        the file is not there."""
        kind, n = item.split(':', 1)
        src, mod = self.item_files(kind, n)
        path = src if mod else os.path.join(self.chk, 'Chk_%s.lean' % C.slug(C.statement_name(self.plan, n)))
        try:
            text = open(path, encoding='utf-8').read()
        except OSError:
            return None
        return import_closure(text, self.module_imports, self.module_olean)

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
        if not leaninfo.olean_ok(self.olean_path(mod)):          # missing, or cut by a crash (q172)
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
        write_json(self.edges_path, self.edges, indent=1)
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

    def scope(self, kinds=None, only=None):
        """The items a run with these --kinds (and --only items) measures: the plan's, of those kinds, less
        the external statements (someone else's)."""
        out = set()
        for wave in C.publish_order(self.plan, self.ext)['waves']:
            for item in wave:
                kind, n = item.split(':', 1)
                if (kind == 'statement' and n in self.ext) or (kinds and kind not in kinds) or \
                        (only is not None and item not in only):
                    continue
                out.add(item)
        return out

    def profile(self, item, env, secs=None):
        """Compile a bundle or statement once more with Lean's profiler (output to D/profile/, never the
        measured .olean), and record {kind, message, profile} in <work>/profiles.json under `item`:
        calibrate's diagnosis of a file that splitting cannot shrink (oaiq-124, oaiq-092)."""
        kind, n = item.split(':', 1)
        src, mod = self.item_files(kind, n)
        if not mod:
            sys.exit('--profile takes a bundle or a statement, not %s' % item)
        sp = os.path.join(self.stage, *mod.split('.')) + '.lean'
        os.makedirs(os.path.dirname(sp), exist_ok=True)
        shutil.copy(src, sp)
        out = os.path.join(self.d, 'profile', *mod.split('.'))
        os.makedirs(os.path.dirname(out), exist_ok=True)
        args = ['lean', '-j1', *L.VERIFIER_FLAGS, '-Dprofiler=true', '-Dtrace.profiler=true',
                '-Dtrace.profiler.threshold=%d' % PROFILE_THRESHOLD_MS, '-R', self.stage,
                '-o', out + '.olean', '-i', out + '.ilean', sp]
        r = subprocess.run(args, cwd=self.lean_ws, env=env, capture_output=True, text=True)
        text = r.stdout + r.stderr
        log = os.path.join(self.cfg['work'], 'profile_%s.log' % C.slug(n))
        open(log, 'w', encoding='utf-8').write(text)
        prof = parse_profile(text)
        nodes = []
        if kind == 'bundle':
            nodes = next((b.get('nodes') or [] for b in self.plan.get('bundles', []) if b['name'] == n), [])
        if secs is None:
            secs = (self.times.get(item) or {}).get('secs')
        k, msg = diagnose_profile(prof, secs, nodes)
        path = os.path.join(self.cfg['work'], 'profiles.json')
        allp = load_json(path, {})
        allp[item] = {'kind': k, 'message': msg, 'secs': secs, 'log': log, 'profile': prof,
                      'key': self.cache_key(src)}
        write_json(path, allp, indent=1)
        print('%s: %s' % (item, msg), flush=True)
        return allp[item]

    def run_all(self, force=False, keep_going=False, repair=True, edges=True, drop=False, kinds=None, only=None):
        copy_published(self.ws, self.olean, imported_modules(self.cfg, self.plan))
        env = self.env()
        ok = True
        scope = self.scope(kinds, only)
        for wave in C.publish_order(self.plan, self.ext)['waves']:
            todo = [item for item in wave if item in scope]
            serial = [i for i in todo if not i.startswith('piece:') or self.jobs <= 1]
            par = [i for i in todo if i not in serial]
            for item in serial:
                if not self.one(item, env, force, repair, edges, drop)['ok']:
                    ok = False
                    if not keep_going:
                        return False
            if par:
                def work(item):
                    with self.locked():
                        return self.one(item, env, force, repair, edges, drop)
                with ThreadPoolExecutor(self.jobs) as ex:
                    res = list(ex.map(work, par))
                if not all(r['ok'] for r in res):
                    ok = False
                    if not keep_going:
                        return False
        big = sorted((i for i in scope if (self.times.get(i) or {}).get('closure_bytes', 0) > CLOSURE_WARN_BYTES),
                     key=lambda i: -self.times[i]['closure_bytes'])
        if big:
            print('import closure over %.1f GB: %d item%s (%s); report only, see q149/oaiq-106' % (
                CLOSURE_WARN_BYTES / 1e9, len(big), '' if len(big) == 1 else 's',
                ', '.join('%s %s' % (i, gb(self.times[i]['closure_bytes'])) for i in big[:10])), flush=True)
        if edges:
            # only this run's items: with --kinds, another kind's records (a piece's, from an earlier
            # full measure) are not this run's to judge (oaiq-081: phase 1 failed on stale piece edges)
            failed = {i for i in scope if i in self.times and not self.times[i].get('ok')}
            texts = {}
            for i in failed:
                kind, n = i.split(':', 1)
                try:
                    texts[i] = open(self.item_files(kind, n)[0], encoding='utf-8').read()
                except OSError:
                    pass
            rep = edge_report(self.plan, {**{i: e for i, e in self.edges.items()
                                             if i in self.times and i in scope and i not in failed},
                                          **unchecked_records(texts)})
            if (kinds and 'piece' not in kinds) or only is not None:
                rep['orphaned_statements'] = []
            write_json(os.path.join(self.cfg['work'], 'false_edges.json'), rep, indent=1)
            print_edge_report(rep)
            if failing_false_edges(rep) and not self.allow_false:
                ok = False
        return ok


PROFILE_THRESHOLD_MS = 1000     # trace.profiler: the declarations and kernel checks over this


def _secs(num, unit):
    return float(num) * {'ns': 1e-9, 'us': 1e-6, '\u03bcs': 1e-6, 'ms': 1e-3, 's': 1.0, 'min': 60.0}[unit]


def parse_profile(text):
    """What `lean -o X.olean -Dprofiler=true -Dtrace.profiler=true` printed: {'categories': {name:
    seconds} (the cumulative profile, `.olean serialization` and `type checking` among them),
    'kernel': [[seconds, declarations]] (each `[Kernel] ... typechecking declarations [X]`), 'commands':
    [[seconds, first line]] (each top-level `[Elab.command]`)}, the lists slowest first."""
    cats, kernel, cmds = {}, [], []
    in_cum = False
    for line in text.split('\n'):
        if line.startswith('cumulative profiling times'):
            in_cum = True
            continue
        if in_cum:
            m = re.match(r'^\t(.+?) ([\d.]+)(ns|us|\u03bcs|ms|s|min)\s*$', line)
            if m:
                cats[m.group(1)] = cats.get(m.group(1), 0.0) + _secs(m.group(2), m.group(3))
                continue
            in_cum = False
        m = re.search(r'\[Kernel\] \[([\d.]+)\].*?typechecking declarations \[(.*)\]\s*$', line)
        if m:
            kernel.append([float(m.group(1)), m.group(2)])
            continue
        m = re.match(r'^\[Elab\.command\] \[([\d.]+)\]\s*(?:\S+\s+)?(.*)$', line)
        if m:
            cmds.append([float(m.group(1)), m.group(2).strip()[:120]])
    return {'categories': cats, 'kernel': sorted(kernel, reverse=True), 'commands': sorted(cmds, reverse=True)}


def diagnose_profile(prof, secs=None, nodes=()):
    """(kind, message) for a file that splitting cannot shrink, from parse_profile's result: kind is
    'serialization' (oaiq-124: one theorem whose type is huge, `.olean serialization` 91 s of 92),
    'kernel' (oaiq-092: single declarations 23-474 s in the kernel) or 'elaboration'. `secs` is the
    measured time (else the profile's total), `nodes` the file's declarations (named when one)."""
    cats = prof.get('categories') or {}
    total = secs or sum(cats.values()) or 1.0
    ser = cats.get('.olean serialization', 0.0)
    kern = cats.get('type checking', 0.0)
    top_k = prof.get('kernel') or []
    one = ' (its one declaration: %s)' % nodes[0] if len(nodes) == 1 else ''
    if ser >= 0.4 * total:
        return 'serialization', (
            'serialization-bound: `.olean serialization` %.0f s of %.0f s%s. A declaration\'s type is huge '
            '(Expr.sizeWithoutSharing): name the type\'s large sides with `abbrev`s in the same bundle and state it '
            'with them (a post-carve patch, config_set.patches; only declaration types cost, a definition\'s value '
            'is cheap; oaiq-124: 92 s -> 55 s)' % (ser, total, one))
    if top_k and (kern >= 0.4 * total or top_k[0][0] >= 0.4 * total):
        heavy = [k for k in top_k if k[0] >= 0.1 * total][:5] or top_k[:1]
        return 'kernel', (
            'kernel-bound declaration %s: %.0f s in the kernel (type checking %.0f s of %.0f s)%s. Splitting cannot '
            'separate one declaration: rewrite it so the kernel has less to unify (state the function up front, '
            'a post-port patch; oaiq-092), or accept it: pipeline.json `config_set.cost_factors` for it plus '
            '`accept_over`' % (
                heavy[0][1], heavy[0][0], kern, total,
                ''.join('; %s: %.0f s' % (n, t) for t, n in heavy[1:])))
    cmds = (prof.get('commands') or [])[:3]
    return 'elaboration', (
        'elaboration-bound (elaboration %.0f s, type checking %.0f s, serialization %.0f s of %.0f s)%s%s; '
        'find the slow tactic with `-Dtrace.profiler=true -Dtrace.profiler.threshold=20000`' % (
            cats.get('elaboration', 0.0), kern, ser, total, one,
            ''.join('; %.0f s: %s' % (t, c) for t, c in cmds)))


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


def unchecked_records(texts):
    """Edge records for files that failed before their edge check ({item: file text}): each
    `import Theorems.*` line counts as an unchecked import, so the statements only such a file imports
    are not reported orphaned (q129: folding those merged them into the failing piece)."""
    return {item: {'file': None, 'false': [], 'restore': {},
                   'imports': {m: 'unchecked' for m in re.findall(r'^import (Theorems\.\S+)\s*$', t, re.M)}}
            for item, t in texts.items()}


def edge_report(plan, edges):
    """{'false_edges': [...], 'dead_imports': [...], 'orphaned_statements': [...]} from the
    edge-check records. A dead import (only declarations `solution` never reaches use it) is not a
    false edge yet: prune the file (prune_solution.py) and measure again."""
    by_module = {}
    for n in list(plan.get('stubs', {})) + list(plan.get('external', [])):
        by_module['Theorems.Thm_' + C.slug(C.statement_name(plan, n))] = n
    out, dead, importers = [], [], {}
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
                importers.setdefault(m, set()).add(item)
                if v == 'dead':
                    dead.append({'item': item, 'file': e.get('file'), 'import': m,
                                 'statement': by_module.get(m)})
    keep = set(plan.get('targets', [])) | set(plan.get('forced', [])) | set(plan.get('external', []))
    # live: kept, or imported by a file that is not a statement's own (a bundle) or by a live
    # statement's statement or piece file; the rest is orphaned, chains included (q129: orphans
    # used to surface one measure round at a time)
    stubs = list(plan.get('stubs', {}))
    owner = lambda item: item.split(':', 1)[1] if item.split(':', 1)[0] in ('piece', 'statement') else None
    live, grew = set(keep), True
    while grew:
        grew = False
        for n in stubs:
            if n not in live and any(owner(i) is None or owner(i) in live for i in
                                     importers.get('Theorems.Thm_' + C.slug(C.statement_name(plan, n)), ())):
                live.add(n)
                grew = True
    orphans = sorted(n for n in stubs if n not in live)
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
    pos = [a for i, a in enumerate(argv) if not a.startswith('--') and (i == 0 or argv[i - 1] not in ('--dir', '--kinds', '--profile', '--only', '--jobs'))]
    if len(pos) != 1:
        sys.exit(__doc__)
    from p2mlib import runlock
    runlock.hold(runlock.dir_key('measure', pos[0]), 'carve_measure.py ' + ' '.join(argv))
    m = Measure(pos[0], opt(argv, '--dir'))
    if '--profile' in argv:
        for item in opt(argv, '--profile').split(','):
            m.profile(item, m.env())
        return
    m.allow_false = '--allow-false-edges' in argv
    m.jobs = max(1, int(opt(argv, '--jobs') or 1))
    kinds = [k for k in (opt(argv, '--kinds') or '').split(',') if k] or None
    only = {x for x in (opt(argv, '--only') or '').split(',') if x} if '--only' in argv else None
    ok = m.run_all('--force' in argv, '--keep-going' in argv, '--no-repair' not in argv,
                   '--no-edge-check' not in argv, '--drop-false-edges' in argv, kinds, only)
    print('done' if ok else 'FAILED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main(sys.argv[1:])
