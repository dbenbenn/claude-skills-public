"""The carver: split a large ported Lean development into prove2.me Definitions bundles, published
intermediate statements and one carved proof piece per statement (scripts/carve.py is its command
line; read its docstring for the workflow and the lessons behind each rule).

Inputs, both from Lean:
* lean/DeclGraph.lean on the compiled development: every constant, its declaration range, and the
  project constants its type and value use (`load_decl_graph`);
* lean/LeanInfo.lean --idents, elaborating each module (`module_info`): its commands, scopes,
  every identifier with its role, and what Lean resolved: each identifier token's constant (or a
  local), and the instances each command's elaboration used (`Graph.reading`, `Node.ideps`).

`Graph` joins them. A node is a declaration COMMAND (its constants: a structure with its fields,
constructor and recursor, a def with its equation lemmas). Its dependencies are the owners of the
constants its constants use (`term`), plus every project constant Lean resolved an identifier of
its source to (`simp only [h]` with an `rfl` lemma `h` leaves no trace in the term), plus the
instances instance search used (a `Fact` instance is a theorem used silently), plus what the
`local notation`s in force before it name. Every question "what does this identifier mean" is
answered from Lean's record; the text reading (namespaces and opens) is only the fallback for a
token Lean recorded nothing for, and those are logged (`Graph.fallbacks`). `make_plan` chooses
bundles (every reachable non-theorem and its closure, cut along the module DAG under time and size
budgets) and nodes (targets, plus theorems promoted bottom-up until each piece fits). `Carver`
cuts module text by Lean's own command ranges (p2mlib.leanedit) and rewrites the context commands
the cut affects (`variable` groups, `include`/`omit`, `attribute`, `open`, notation, empty
namespace blocks). `generate` writes lib/Def_*.lean, lib/Thm_*.lean and solutions/Sol_*.lean;
`publish_order` gives the import DAG as waves of items that may publish concurrently.
"""
import bisect
import collections
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field

from . import leanedit, leaninfo
from .leantext import import_names
from . import repair as RP
from .leantext import guard_message, guard_problems, strip

HERE = os.path.dirname(os.path.abspath(__file__))
DECLGRAPH = os.path.join(os.path.dirname(HERE), 'lean', 'DeclGraph.lean')
SIZE_CAP = 1 << 20                     # prove2.me refuses a solution or statement over 1 MiB

NOTATION = {'notation', 'mixfix', 'notation3'}
# the platform refuses these in any submitted file (prove2me SKILL: "notation ok, macros refused")
REFUSED = {'macro', 'syntax', 'macro_rules', 'elab', 'elab_rules', 'syntaxAbbrev', 'syntaxCat',
           'declare_syntax_cat'}
COERCION_CLASSES = {'Coe', 'CoeTC', 'CoeOut', 'CoeOTC', 'CoeHead', 'CoeHTC', 'CoeTail', 'CoeHTCT', 'CoeDep',
                    'CoeT', 'CoeFun', 'CoeSort'}
# attributes Lean lets only the file declaring the target set ("failed to set reducibility status
# … has not been defined in this file"; "Cannot add attribute `[inline]` … because it is in an
# imported module"), measured on Lean 4.33.1; simp, instance, ext, coe, default_instance are free
RESTRICTED_ATTRIBUTES = {'reducible', 'irreducible', 'semireducible', 'instance_reducible', 'inline',
                         'noinline', 'macro_inline', 'always_inline', 'specialize', 'nospecialize',
                         'never_extract', 'match_pattern', 'elab_as_elim', 'export', 'unbox',
                         'implemented_by', 'extern', 'computed_field'}


def attribute_entries(txt):
    """The comma-separated entries of an `attribute [...] targets` command's list, or None."""
    m = re.search(r'\battribute\s*\[', txt)
    if not m:
        return None
    depth, start, out = 1, m.end(), []
    for j in range(m.end(), len(txt)):
        ch = txt[j]
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
            if depth == 0:
                out.append(txt[start:j].strip())
                return [e for e in out if e]
        elif ch == ',' and depth == 1:
            out.append(txt[start:j].strip())
            start = j + 1
    return None


# attributes that declare new constants from their target (`foo_assoc`, `Foo.ext`, `bar_apply`,
# the additive copy): applied a second time, in a file importing the first application, Lean
# reports "has already been declared" (SimpleAmenable oaiq-065: `attribute [reassoc]
# Data.s₀_comp_δ₁` kept in a bundle importing Data's bundle)
GENERATING_ATTRIBUTES = {'reassoc', 'elementwise', 'simps', 'to_additive', 'to_dual', 'mk_iff', 'ext'}


def generating_attribute(txt):
    """Does an `attribute [...]` command set an attribute that declares new constants?"""
    return any(e.split()[0] in GENERATING_ATTRIBUTES for e in attribute_entries(txt) or ()
               if e.split())


def restricted_attribute(txt):
    """Does an `attribute [...]` command set, globally, an attribute only the declaring file may?"""
    return any(e.split()[0] in RESTRICTED_ATTRIBUTES for e in attribute_entries(txt) or ()
               if e.split())
DIAGNOSTIC = {'check', 'eval', 'print', 'printAxioms', 'reduce', 'check_failure', 'synth',
              'evalBang', 'exit'}
OPENERS = {'namespace', 'section', 'noncomputableSection'}


# a simp attribute entry (`simp`, `local simp`, `simp ←`; not `-simp`, `simps`)
_SIMP_ATTR = re.compile(r'(?:(?:local|scoped)\s+)?simp(?![\w\-])')
# a proof by `rfl`: `:= rfl`, `:= by rfl`, `:= by exact rfl`, `:= Eq.refl _`
_RFL_VALUE = re.compile(r'\s*(?::=)?\s*(?:by\s+(?:exact\s+)?)?(?:rfl|Eq\.refl\b[^\n]*|\(rfl\))\s*$')
# a tactic using the default simp set, and what follows it up to its lemma list or line end
_SIMP_CALL = re.compile(r"(?<![\w.'])(?:simp|simpa|simp_all|dsimp|simp_arith|norm_num|field_simp|aesop)"
                        r"[?!]*(?![\w'])([^\[\n]*)")


def _default_simp_call(text):
    """Does Lean source call simp with its default simp set (no `only`)?"""
    return any(not re.search(r'\bonly\b', mt.group(1)) for mt in _SIMP_CALL.finditer(text))


class CarveError(Exception):
    pass


def pubname(n):
    """`_private.M.0.A.b` -> `A.b`; other names unchanged."""
    return n.split('.0.', 1)[1] if n.startswith('_private.') else n


def slug(n):
    return pubname(n).replace('.', '_')


def prefixes(ns):
    """`A.B` -> ['A.B', 'A', ''] (innermost first, the root last)."""
    parts = ns.split('.') if ns else []
    return ['.'.join(parts[:i]) for i in range(len(parts), -1, -1)]


def ns_prefixes(name):
    """Proper prefixes of a name: `A.B.c` -> ['A', 'A.B']."""
    p = name.split('.')
    return ['.'.join(p[:i]) for i in range(1, len(p))]


def join(p, tok):
    return p + '.' + tok if p else tok


# ================================================================ Lean runs

def run_decl_graph(out, prefix, roots, ws=None, timeout=7200, also=()):
    """lean/DeclGraph.lean on the compiled ROOT modules (their .olean must be built). `also`:
    modules outside PREFIX whose constants are reported as nodes too (the Theorems modules of
    config `external_theorems`), so the carver sees which declarations use them."""
    ws = ws or leaninfo.workspace()
    extra = [a for m in also for a in ('--also', m)]
    r = subprocess.run(['lake', 'env', 'lean', '--run', DECLGRAPH] + extra + [out, prefix] + list(roots),
                       cwd=ws, capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise CarveError('DeclGraph failed:\n' + (r.stdout + r.stderr)[-3000:])
    return out


def module_path(src_root, m):
    return os.path.join(src_root, *m.split('.')) + '.lean'


def module_info(src_root, m, ws=None, use_cache=True):
    """LeanInfo of module m under src_root, elaborated (its imports must be built), with its
    identifiers, what Lean resolved each to and the instances each command used; cached (usually
    already, by the build: oai_build_modules.py compiles through leaninfo.build_module with the
    same options, so the module is not elaborated twice)."""
    return leaninfo.run(module_path(src_root, m), idents=True, module=m, no_decls=True, ws=ws,
                        use_cache=use_cache, options=leaninfo.BUILD_OPTIONS)


def module_info_cached(src_root, m, ws=None):
    """Is module_info(src_root, m) in the LeanInfo cache?"""
    return leaninfo.is_cached(module_path(src_root, m), idents=True, module=m, no_decls=True, ws=ws,
                              options=leaninfo.BUILD_OPTIONS)


def compile_file(path, module, olean_dir, ws=None, timeout=3000):
    """Compile one file with `lake env lean`, its imports found in olean_dir first; with `module`,
    write its .olean there so later files can import it (the tests' stand-in for publishing).
    The verifier has autoImplicit off; `lake env lean` ignores the lakefile's options, so say so."""
    ws = ws or leaninfo.workspace()
    env = dict(os.environ)
    # olean_dir must come FIRST: Lean resolves `Definitions.X` in the first search-path entry
    # holding a `Definitions` directory, and `lake env` would put the workspace's own first
    env['LEAN_PATH'] = olean_dir + ':' + _lake_lean_path(ws)
    args = ['lean', '-DautoImplicit=false']
    if module:
        out = os.path.join(olean_dir, *module.split('.')) + '.olean'
        os.makedirs(os.path.dirname(out), exist_ok=True)
        rel = os.path.join(*module.split('.')) + '.lean'
        p = os.path.abspath(path)
        root = p[:-len(rel)] if p.endswith(rel) else os.path.dirname(p)
        args += ['-R', root, '-o', out]
    r = subprocess.run(args + [os.path.abspath(path)], cwd=ws, env=env, capture_output=True,
                       text=True, timeout=timeout)
    if r.returncode or 'error' in r.stdout:
        raise CarveError('%s does not compile:\n%s' % (path, (r.stdout + r.stderr)[-4000:]))
    return r.stdout


_LAKE_PATH = {}


def _lake_lean_path(ws):
    if ws not in _LAKE_PATH:
        env = {k: v for k, v in os.environ.items() if k != 'LEAN_PATH'}
        r = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ws, env=env,
                           capture_output=True, text=True, timeout=600)
        _LAKE_PATH[ws] = r.stdout.strip()
    return _LAKE_PATH[ws]


def record_fixture(src_root, prefix, roots, olean_dir, out_dir, ws=None):
    """Compile a fixture development (core Lean only) into olean_dir, then record DeclGraph and
    every module's LeanInfo under out_dir (tests/record_fixtures.py carve). Returns the recorded
    paths, relative to out_dir."""
    mods, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for imp in import_names(open(module_path(src_root, m)).read()):
            if imp.split('.')[0] == prefix.split('.')[0] and os.path.exists(module_path(src_root, imp)):
                visit(imp)
        mods.append(m)
    for r in roots:
        visit(r)
    for m in mods:
        compile_file(module_path(src_root, m), m, olean_dir, ws)
    os.makedirs(out_dir, exist_ok=True)
    old = os.environ.get('LEAN_PATH')
    os.environ['LEAN_PATH'] = olean_dir + (':' + old if old else '')
    try:
        dg = os.path.join(out_dir, 'decl_graph.jsonl')
        run_decl_graph(dg, prefix, roots, ws)
        # one line per declaration, sorted, so the recording diffs
        lines = open(dg, encoding='utf-8').read().split('\n')
        decls = sorted(l for l in lines if l.startswith('{') and '"n":' in l)
        rest = [l for l in lines if l and l not in decls]
        open(dg, 'w', encoding='utf-8').write('\n'.join(decls + sorted(rest[:-1]) + rest[-1:]) + '\n')
        out = ['decl_graph.jsonl']
        for m in mods:
            data = leaninfo.raw(module_path(src_root, m), ws=ws, idents=True, module=m, no_decls=True)
            data.pop('build_ms', None)        # a timing: never the same twice, so never recorded
            data['file'] = os.path.relpath(module_path(src_root, m), src_root)
            rel = os.path.relpath(module_path(src_root, m), src_root)[:-5] + '.info.json'
            os.makedirs(os.path.dirname(os.path.join(out_dir, rel)), exist_ok=True)
            with open(os.path.join(out_dir, rel), 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=1, sort_keys=True)
            out.append(rel)
    finally:
        if old is None:
            os.environ.pop('LEAN_PATH', None)
        else:
            os.environ['LEAN_PATH'] = old
    return out


# ================================================================ the graph

@dataclass
class Node:
    key: str                  # the env name of its primary constant
    module: str
    cmd: int                  # index of its command in the module's LeanInfo
    names: list               # every constant it owns (env names)
    kind: str                 # DeclGraph kind of the primary constant
    theorem: bool
    instance: bool
    sorry: bool
    univ: list
    size: int                 # bytes of the command with its trailing trivia
    private: bool
    attributed: bool = False  # attributes on it, or named by an `attribute` command
    term: set = field(default_factory=set)    # owners of what its constants' types and values use
    tdeps: set = field(default_factory=set)   # owners of what its declared constants' types use
    sdeps: set = field(default_factory=set)   # what its source names (resolved)
    ndeps: set = field(default_factory=set)   # what the notations in force before it name
    ideps: set = field(default_factory=set)   # the project instances its elaboration used
    sig: set = field(default_factory=set)     # what its statement needs: tdeps + names before `:=`
    deps: set = field(default_factory=set)    # term | sdeps | ndeps | ideps


def load_decl_graph(path, dups=None):
    """(constants, module imports, external namespaces) of a DeclGraph recording. A `dup` record
    (another module's copy of a theorem two modules declare) goes into the list `dups` if given,
    never over the environment's record of the name."""
    consts, imports, ext = {}, {}, set()
    for line in open(path, encoding='utf-8'):
        if not line.strip():
            continue
        x = json.loads(line)
        if x.get('dup'):
            if dups is not None:
                dups.append(x)
        elif 'n' in x:
            consts[x['n']] = x
        elif 'module' in x:
            imports[x['module']] = list(dict.fromkeys(x['imports']))
        elif 'ext_namespaces' in x:
            ext = set(x['ext_namespaces'])
    return consts, imports, ext


def _is_decl_command(c):
    return bool(c.decl_kind) and c.decl_kind != 'example' or c.short_kind in ('mutual', 'alias', 'deriving') or \
        (bool(c.names) and c.short_kind not in NOTATION | REFUSED)


SCOPED_NS = re.compile(r'\s*(?:/--.*?-/\s*)?scoped\[\s*(?:_root_\.)?([^\]\s]+)\s*\]', re.S)
SCOPED_CORE = re.compile(r'\s*(?:/--.*?-/\s*)?(?:@\[[^\]]*\]\s*)?scoped\s', re.S)


def scoped_scope(text, namespace, short_kind):
    """The namespace a scoped notation lives in, or None for any other command: Mathlib's
    `scoped[X] cmd` names X from the root, core `scoped notation` uses the current namespace."""
    if short_kind == 'scopedNS':
        m = SCOPED_NS.match(text)
        return m.group(1) if m else None
    if short_kind in NOTATION and SCOPED_CORE.match(text):
        return namespace
    return None


def _is_local(text):
    """A `local`/`scoped` notation, or an `attribute [local …]`: it lasts to the end of its scope."""
    return bool(re.match(r'\s*(?:/--.*?-/\s*)?(?:@\[[^\]]*\]\s*)?(?:local|scoped)\b', text, re.S)) or \
        '[local ' in text or '[scoped ' in text


# a `local instance` command, anonymous when the next token opens its binders or type
LOCAL_INSTANCE = re.compile(rb'(?:/--.*?-/\s*)?(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?'
                            rb'local\s+instance(?:\s*\(priority\s*:=[^)]*\))?', re.S)


_PRIORITY = re.compile(rb'\binstance\s*\(priority\s*:=\s*([^)]*?)\s*\)')


def _instance_priority(text):
    """The `(priority := p)` an instance command's text gives (bytes), as text, else None."""
    mt = LOCAL_INSTANCE.match(text)
    mp = _PRIORITY.search(text, 0, mt.end()) if mt else None
    return mp.group(1).decode('utf-8') if mp else None


def _local_instance(info, c):
    """(is a `local instance`, byte offset where an anonymous one's name goes or None)."""
    t = info.text_bytes
    mt = LOCAL_INSTANCE.match(t, c.start.byte, c.end.byte)
    if not mt:
        return False, None
    nxt = t[_skip_ws(t, mt.end()):_skip_ws(t, mt.end()) + 3].decode('utf-8', 'ignore')[:1]
    return True, (mt.end() if nxt in ':([{⦃' else None)


ANY_INSTANCE = re.compile(rb'(?:/--.*?-/\s*)?(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?'
                          rb'(?:(?:local|scoped)\s+)?instance(?:\s*\(priority\s*:=[^)]*\))?', re.S)


def _anonymous_instance(info, c):
    """Byte offset where an anonymous `instance` command's name goes, else None."""
    t = info.text_bytes
    mt = ANY_INSTANCE.match(t, c.start.byte, c.end.byte)
    if not mt:
        return None
    nxt = t[_skip_ws(t, mt.end()):_skip_ws(t, mt.end()) + 3].decode('utf-8', 'ignore')[:1]
    return mt.end() if nxt in ':([{⦃' else None


def _notation_tokens(text):
    """The literal tokens a notation command declares (`local notation "O" => …` -> {'O'})."""
    head = text.split('=>', 1)[0]
    return {x.strip() for x in re.findall(r'"((?:[^"\\]|\\.)*)"', head) if x.strip()}


def _in_scope(info, vi, c):
    """Is command vi (a notation, a local instance) still in force at command c: earlier, and
    its enclosing scopes all still open there?"""
    if vi >= c.index:
        return False
    a = [o for o, _ in info.commands[vi].context]
    b = [o for o, _ in c.context]
    return b[:len(a)] == a


# the characters Lean reads inside an identifier (Lean.isIdRest: ASCII letters and digits, `_ ' ! ?`,
# letter-like symbols, subscripts). Not Python's `\w`, which takes modifier letters too: `Cᵐᵒᵖ` is the
# token `C` and the postfix `ᵐᵒᵖ` (Auslander–Reiten oaiq-031: a bundle whose first declarations were
# written `Cᵐᵒᵖ` lost `local notation "C"`)
_ID = (r"A-Za-z0-9_'!?\u03b1-\u03ba\u03bc-\u03c9\u0391-\u03a0\u03a2-\u03a9\u03ca-\u03fb"
       r"\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c")


def _uses_token(text, tok):
    if re.match(r"^[%s.]+$" % _ID, tok):
        return re.search(r"(?<![%s.])%s(?![%s])" % (_ID, re.escape(tok), _ID), text) is not None
    return tok in text


def decl_ns(c):
    """The namespace a command's body is read in: declaring `A.B.f` in namespace N reads the body
    in N.A.B (Erdős 3 v2 B188: `simp only [tensorPower_eval]` inside
    `NativeMultidegreeNilcharacter.mixedPermutationProduct_tensorPower`, declared in namespace
    Erdos3, named NativeMultidegreeNilcharacter.tensorPower_eval)."""
    if c.names and '.' in c.names[0]:
        p = c.names[0].rsplit('.', 1)[0]
        if not c.namespace or p == c.namespace or p.startswith(c.namespace + '.'):
            return p
    return c.namespace


def is_field(info, idn):
    """Is identifier idn (a LeanInfo ident) a field, `(e).f`, `e |>.f` or `.f`? Lean's tokenizer
    reads `a.b` as one identifier, so an identifier starting right after a `.` is the field part
    of a projection (or a dot-identifier): it names `T.f` for a type T, never what the bare token
    reads as lexically."""
    return info.text_bytes[idn['start'] - 1:idn['start']] == b'.'


def _head_kind(h):
    return h['kind'].rsplit('.', 1)[-1]


@dataclass
class Reading:
    """What Lean resolved one identifier token to, from the elaborated port (LeanInfo `resolved`).
    `head`: the constants the token's name part denotes (empty for a local: a bound or section
    variable, a hypothesis), `span` its byte range; `consts`: every constant recorded inside the
    token, fields included (`A.coord_eq` with `A : Space`: head local, consts {Space.coord_eq});
    `entries`: [(start, end, name)] ('' for a local)."""
    head: tuple
    span: tuple
    consts: set
    entries: list
    field: bool = False       # the head is a structure-instance field name (`{ w := 0 }`)
    binder: bool = False      # the token declares or binds its name (a declId, a constructor)

    @property
    def local(self):
        return not self.head


def _alternative_name(info, idn):
    """Is identifier idn the name of a case alternative (`| zero =>` or `| @inv h … =>` of
    `induction … with`, `case succ =>`), where Lean accepts no qualified name ("Invalid
    alternative name")? Also true of a `match` pattern's constructor, where a pin is never needed."""
    before = info.text_bytes[max(0, idn['start'] - 40):idn['start']].rstrip()
    if before.endswith(b'@'):          # `| @inv h a … =>` (RationalHitting list_hits)
        before = before[:-1].rstrip()
    return before.endswith(b'|') or re.search(rb'(?:^|\s)(?:case|next)$', before) is not None


def last_component(text_bytes, a, b):
    """Byte range of the last component of the name written at [a, b) (`Space.size_eq` ->
    `size_eq`; a `«…»` component may contain dots)."""
    t = text_bytes[a:b]
    stop = t.rfind(b'\xc2\xab') if t.endswith(b'\xc2\xbb') else len(t)
    i = t.rfind(b'.', 0, stop if stop >= 0 else len(t))
    return a + i + 1, b


class Graph:
    """The declaration graph of a development: nodes (declaration commands), module DAG, name
    resolution. `Graph.load(decl_graph.jsonl, src_root)` reads the module infos (recorded
    `<module>.parse.json` beside the source if present, else LeanInfo, cached)."""

    def __init__(self, consts, imports, ext_ns, infos, dups=()):
        self.consts, self.imports, self.ext_ns, self.infos = consts, imports, ext_ns, infos
        self.modules = sorted(infos)
        self._closure_cache = {}
        self._readings = {}
        # local instances a kept declaration used that a carved file could not put back in force
        # (they name a declaration the file lacks): (module, instance line, declaration line)
        self.lost_instances = []
        # identifier tokens read from text because Lean recorded nothing for them, that the
        # text-based reading took for project constants: (module, line, token)
        self.fallbacks = []
        self._build_modules()
        self._split_duplicates(dups)
        self._build_nodes()
        self._build_names()
        self._add_coercion_instances()
        self._build_deps()

    @classmethod
    def load(cls, decl_graph, src_root, ws=None):
        dups = []
        consts, imports, ext = load_decl_graph(decl_graph, dups)
        infos = {}
        todo = [m for m in imports if not os.path.exists(module_path(src_root, m)[:-5] + '.info.json')]
        # oaiq-047: after LeanInfo.lean changed (the cache is keyed by it), loading the graph re-ran
        # LeanInfo on 1259 modules one at a time, ~3 h with no output: say so, and count
        miss = {m for m in todo if not module_info_cached(src_root, m, ws)}
        if miss:
            print('%d of %d modules are not in the LeanInfo cache (LeanInfo.lean changed, or their imports were '
                  'rebuilt): elaborating them one at a time, about their build time each (`carve.py graph` '
                  'does it in parallel)' % (len(miss), len(imports)), file=sys.stderr, flush=True)
        done = 0
        for m in imports:
            rec = module_path(src_root, m)[:-5] + '.info.json'
            if os.path.exists(rec):
                infos[m] = leaninfo.parse(json.load(open(rec, encoding='utf-8')),
                                          open(module_path(src_root, m), 'rb').read())
            else:
                infos[m] = module_info(src_root, m, ws)
                if m in miss:
                    done += 1
                    print('LeanInfo %d/%d %s' % (done, len(miss), m), file=sys.stderr, flush=True)
        return cls(consts, imports, ext, infos, dups)

    # ---------------------------------------------------------- modules
    def _build_modules(self):
        self.mod_index = {m: i for i, m in enumerate(self.modules)}
        self.order = self.topo(self.modules)
        mask = {}
        for m in self.order:       # imports first
            k = 1 << self.mod_index[m]
            for imp in self.imports.get(m, []):
                if imp in mask:
                    k |= mask[imp]
            mask[m] = k
        self.closure_mask = mask

    def importers(self, d):
        """How many project modules see module d (d included)."""
        bit = self.mod_index[d]
        return sum(1 for m in self.modules if self.closure_mask[m] >> bit & 1)

    def _split_duplicates(self, dups):
        """A theorem two modules declare under the same full name: Lean imports both into the root
        when their types agree, and keeps one constant, so DeclGraph saw one, and a carved piece
        holding modules that used the other copy failed "Unknown identifier" at measure (oaiq-088
        `blockSlope_mul_gap`, oaiq-090 `lineConvolution_bound`, oaiq-095 `additiveFourier_conj`,
        oaiq-096: three more; each renamed by a port patch, hours later). Each copy becomes a node:
        the one most modules see keeps the name, every other one is `<name>_dup<i>` (DeclGraph's
        `dup` records give its own value's dependencies; a recording without them is read from the
        commands, value dependencies unknown), and in a module that sees a renamed copy but not the
        kept one, what Lean resolved to the name means the renamed copy (its references, its
        constants' dependencies, its instance records). `collision_renames` renames the declaration
        and those references in every carved file. Sets `duplicates` [(name, kept module,
        [(module, new name)], guessed modules)] and `dup_alias` {module: {name: new name}}."""
        self.duplicates, self.dup_alias = [], {}
        copies = collections.defaultdict(dict)       # name -> {module: record}
        for x in dups or ():
            if x['m'] in self.infos and x['n'] in self.consts and x['m'] != self.consts[x['n']]['m']:
                copies[x['n']][x['m']] = dict(x)
        guessed = collections.defaultdict(list)
        for m, info in self.infos.items():
            for c in info.commands:
                if not _is_decl_command(c) or c.private:
                    continue
                for nm in c.names or ():
                    x = self.consts.get(nm)
                    if x and x['m'] != m and x['m'] in self.infos and x['k'] in ('theorem', 'axiom') \
                            and m not in copies.get(nm, {}):
                        copies[nm][m] = dict(x, m=m, v=[], r=None, dup=True)
                        guessed[nm].append(m)
        renamed = {}                                 # name -> {module: new name}
        for nm in sorted(copies):
            env_m = self.consts[nm]['m']
            # only theorems a command declares by name: identical anonymous (or named) local
            # instances of a Prop class in sibling modules share one constant too (Problem340:
            # `local instance : Fact ((0 : ℝ) < 100)` in 28 modules), and the carver emits another
            # module's copy again where it is used (Carver._reactivate), so they stay one node
            if not all(self._declaring_command(d, nm) for d in set(copies[nm]) | {env_m}):
                continue
            mods = sorted(set(copies[nm]) | {env_m},
                          key=lambda d: (-self.importers(d), d != env_m, d))
            keep, others = mods[0], mods[1:]
            recs = dict(copies[nm])
            recs[env_m] = self.consts[nm]
            if keep != env_m:
                self.consts[nm] = self._dup_record(recs[keep], nm, keep, nm)
            new, i = {}, 1
            for d in others:
                while nm + '_dup%d' % i in self.consts:
                    i += 1
                new[d] = nm + '_dup%d' % i
                self.consts[new[d]] = self._dup_record(recs[d], new[d], d, nm)
                i += 1
            renamed[nm] = new
            self.duplicates.append((nm, keep, sorted(new.items()), sorted(guessed.get(nm, ()))))
        if not renamed:
            return
        for m in self.infos:
            alias = {}
            for nm, new in renamed.items():
                keep = self.consts[nm]['m']
                if m == keep or self.sees(m, keep):
                    continue
                seen = [d for d in sorted(new) if d == m or self.sees(m, d)]
                if seen:
                    alias[nm] = new[seen[0]]
            if alias:
                self.dup_alias[m] = alias
        by_m = collections.defaultdict(list)
        for x in self.consts.values():
            if x['m'] in self.dup_alias:
                by_m[x['m']].append(x)
        for m, alias in self.dup_alias.items():
            a = lambda n, alias=alias: alias.get(n, n)
            for x in by_m[m]:
                x['t'] = [a(y) for y in x['t']]
                x['v'] = [a(y) for y in x['v']]
            for c in self.infos[m].commands:
                c.names = [a(n) for n in c.names or ()]
                if c.resolved:
                    c.resolved = [[x[0], x[1], a(x[2])] + list(x[3:]) for x in c.resolved]
                if c.insts:
                    c.insts = [a(n) for n in c.insts]
                if c.sig_insts:
                    c.sig_insts = [a(n) for n in c.sig_insts]
                if c.declares:
                    c.declares = [[a(x[0])] + list(x[1:]) for x in c.declares]

    def _declaring_command(self, m, nm):
        """The declaration command of module m that declares `nm` by name and is not an instance."""
        info = self.infos[m]
        for c in info.commands:
            if _is_decl_command(c) and nm in (c.names or ()):
                if c.decl_kind == 'instance' or ANY_INSTANCE.match(info.text_bytes, c.start.byte, c.end.byte):
                    return None
                return c
        return None

    def _dup_record(self, rec, name, m, orig):
        """Copy `rec` of a duplicated theorem `orig` as constant `name` of module m, its range that of
        the command of m declaring `orig` when the recording has none for this copy."""
        rec = dict(rec, n=name, m=m)
        rec.pop('dup', None)
        if not rec.get('r'):
            for c in self.infos[m].commands:
                if _is_decl_command(c) and orig in (c.names or ()):
                    rec['r'] = [c.start.line, c.start.col, c.end.line, c.end.col]
                    break
        return rec

    def project_imports(self, m):
        return [x for x in self.imports.get(m, []) if x in self.infos]

    def sees(self, m, d):
        """Was module d imported (transitively) by m, or is it m?"""
        return bool(self.closure_mask[m] >> self.mod_index[d] & 1)

    def topo(self, mods):
        """mods in import order (DFS, sorted, so deterministic)."""
        out, seen = [], set()
        for r in sorted(mods):
            if r in seen:
                continue
            seen.add(r)
            stack = [(r, iter(sorted(self.project_imports(r))))]
            while stack:
                m, it = stack[-1]
                nx = next(it, None)
                if nx is None:
                    out.append(m)
                    stack.pop()
                elif nx not in seen:
                    seen.add(nx)
                    stack.append((nx, iter(sorted(self.project_imports(nx)))))
        want = set(mods)
        return [m for m in out if m in want]

    def ext_imports(self, mods):
        """Non-project imports of mods and of the project modules they import. An external
        theorem's module (`Theorems.…`, reported by DeclGraph through --also) is neither walked
        nor listed: files import it only where they use the theorem (the external map)."""
        seen, out, todo = set(), [], list(mods)
        while todo:
            m = todo.pop()
            if m in seen:
                continue
            seen.add(m)
            for x in self.imports.get(m, []):
                if x in self.infos and x.startswith('Theorems.'):
                    continue
                if x in self.infos:
                    todo.append(x)
                elif x not in out and x != 'Init':
                    out.append(x)
        return sorted(out)

    # ---------------------------------------------------------- nodes
    def _build_nodes(self):
        self.nodes, self.owner, self.cmd_node = {}, {}, {}
        starts = {}
        for m, info in self.infos.items():
            starts[m] = [(c.start.line, c.start.col) for c in info.commands]
        ranged = collections.defaultdict(list)          # (module, cmd) -> constants
        for n, x in self.consts.items():
            m = x['m']
            if m not in self.infos or not x.get('r'):
                continue
            pos = (x['r'][0], x['r'][1])
            i = bisect.bisect_right(starts[m], pos) - 1
            if i < 0:
                continue
            c = self.infos[m].commands[i]
            if (c.end.line, c.end.col) < pos or not _is_decl_command(c):
                continue                                 # a notation's parser constants, …
            ranged[(m, i)].append(n)
        for (m, i), ns in ranged.items():
            info = self.infos[m]
            c = info.commands[i]
            want = c.names[0] if c.names else None
            prim = next((n for n in sorted(ns) if pubname(n) == want), None) or \
                min(ns, key=lambda n: (self.consts[n]['r'][0], self.consts[n]['r'][1], n))
            x = self.consts[prim]
            a, b = info.command_span(i)
            node = Node(prim, m, i, sorted(ns), x['k'], x['k'] == 'theorem', x['i'],
                        any(self.consts[n]['s'] for n in ns), x['u'], b - a,
                        prim.startswith('_private.'), attributed=bool(c.attrs))
            self.nodes[prim] = node
            self.cmd_node[(m, i)] = prim
            for n in ns:
                self.owner[n] = prim
        # generated constants without a range (`foo.proof_1`, `Foo.mk.injEq`): their name's owner
        for n, x in self.consts.items():
            if n in self.owner or x['m'] not in self.infos:
                continue
            p = n
            while '.' in p:
                p = p.rsplit('.', 1)[0]
                if p in self.owner and self.consts.get(p, {}).get('m') == x['m']:
                    self.owner[n] = self.owner[p]
                    self.nodes[self.owner[p]].names.append(n)
                    self.nodes[self.owner[p]].sorry |= x['s']
                    break
        # a scoped notation is a node of its own: it must sit in exactly one bundle, which every
        # file opening its scope imports (Erdős 3 v2, 2026-10-16: "unknown namespace `Indicator`")
        self.scoped = {}                                 # pseudo-node key -> scope namespace
        for m, info in self.infos.items():
            for c in info.commands:
                x = scoped_scope(leanedit.text(info, c.index), c.namespace, c.short_kind)
                if x is None:
                    continue
                key = '«notation»:%s:%d' % (m, c.index)
                a, b = info.command_span(c.index)
                self.nodes[key] = Node(key, m, c.index, [], 'notation', False, False, False, [],
                                       b - a, False)
                self.cmd_node[(m, c.index)] = key
                self.scoped[key] = x
        self._scoped_cmds = {(self.nodes[k].module, self.nodes[k].cmd) for k in self.scoped}
        self.by_module = collections.defaultdict(list)
        for k, nd in self.nodes.items():
            self.by_module[nd.module].append(k)
        for m in self.by_module:
            self.by_module[m].sort(key=lambda k: self.nodes[k].cmd)

    # ---------------------------------------------------------- names and namespaces
    def _build_names(self):
        self.pub = collections.defaultdict(list)       # public form -> env names
        self.short = collections.defaultdict(list)     # last component -> env names
        for n in self.owner:
            self.pub[pubname(n)].append(n)
            self.short[pubname(n).rsplit('.', 1)[-1]].append(n)
        self.all_pub = set(self.pub)
        # project namespaces, with the modules that bring each into existence
        nsmods = collections.defaultdict(int)
        first = {}                          # (module, namespace) -> first command creating it

        def note(m, p, i):
            if i < first.get((m, p), 1 << 30):
                first[(m, p)] = i
        for n in self.owner:
            m = self.consts[n]['m']
            bit = 1 << self.mod_index[m]
            i = self.nodes[self.owner[n]].cmd
            for p in ns_prefixes(pubname(n)):
                nsmods[p] |= bit
                note(m, p, i)
        for m, info in self.infos.items():
            bit = 1 << self.mod_index[m]
            for c in info.commands:
                if c.short_kind == 'namespace':
                    tok = leanedit.text(info, c.index).split()[1]
                    full = join(c.namespace, tok)
                    for p in ns_prefixes(full + '.x'):
                        nsmods[p] |= bit
                        note(m, p, c.index)
        for k, x in self.scoped.items():
            for p in ns_prefixes(x + '.x'):
                nsmods[p] |= 1 << self.mod_index[self.nodes[k].module]
                note(self.nodes[k].module, p, self.nodes[k].cmd)
        self.ns_mask = dict(nsmods)
        self.ns_first = first
        self.proj_ns = set(nsmods)

    def ns_existed(self, ns, m, before=None):
        """Did project namespace ns exist when module m was elaborated (from m's imports or m)?
        With `before` (a command index of m): at that command, so m's own contribution counts only
        if made earlier (Erdős 3 v2 B172: `open MvPolynomial` came before the module's own
        `namespace OAI.MvPolynomial`, and meant only Lean's)."""
        mask = self.ns_mask.get(ns, 0) & self.closure_mask[m]
        if before is None:
            return bool(mask)
        own = 1 << self.mod_index[m]
        return bool(mask & ~own) or self.ns_first.get((m, ns), 1 << 30) < before

    def visible(self, n, m):
        """May module m name constant n (a private one only in its own module)?"""
        d = self.consts[n]['m']
        return d == m if n.startswith('_private.') else self.sees(m, d)

    def open_targets(self, tok, ns, m):
        """The project namespaces `open tok`, written in namespace ns of module m, opened."""
        if tok.startswith('_root_.'):
            cands = [tok[len('_root_.'):]]
        else:
            cands = [join(p, tok) for p in prefixes(ns)]
        return [c for c in cands if self.ns_existed(c, m)]

    def scope_opens(self, info, c, m):
        """The project namespaces open at command c: the `open` commands in its scopes and its own
        `open … in` heads, resolved as Lean resolved them in module m."""
        out = []
        cmds = [info.commands[i] for _, cs in c.context for i in cs]
        for oc in cmds:
            if oc.short_kind == 'open':
                for idn in oc.idents or []:
                    if idn['role'] == 'open':
                        out += self.open_targets(idn['name'], oc.namespace, m)
        for h in c.heads or []:
            if _head_kind(h) == 'open':
                for idn in c.idents or []:
                    if idn['role'] == 'open' and h['start'] <= idn['start'] < h['end']:
                        out += self.open_targets(idn['name'], c.namespace, m)
        return list(dict.fromkeys(out))

    def scope_vars(self, info, c):
        """The names the `variable` commands in force at command c bind."""
        key = ('vars', info.path, c.index)
        if key not in self._readings:
            out = set()
            for _, cs in c.context:
                for vi in cs:
                    vc = info.commands[vi]
                    if vc.short_kind == 'variable':
                        out.update(n for grp in vc.binders or () for n in grp['names'])
            self._readings[key] = out
        return self._readings[key]

    def reading(self, info, c, idn):
        """What Lean resolved identifier idn of command c to (a Reading), or None when the
        elaborated port recorded nothing there (a module read without elaborating, a command
        that failed, a token that is not a term: then the text-based reading is the fallback).
        In a notation's body, a token whose head is a section variable in force is that local:
        LeanInfo resolves the body without the section's variables (oaiq-081: `local notation
        "seeded" => … run.output`, recorded as the theorem `run` of an opened namespace, so the
        statement's stub dropped the notation and the `run_oai` rename gave `run.run_oai`)."""
        if c.resolved is None:
            return None
        if c.short_kind in NOTATION and idn['name'].split('.')[0] in self.scope_vars(info, c):
            a = idn['start']
            return Reading((), (a, a + len(idn['name'].split('.')[0].encode('utf-8'))), set(), [])
        key = (info.path, c.index)
        idx = self._readings.get(key)
        if idx is None:
            # [a, b, name] for a term, + 'f' for a structure-instance field, 'b' for a binder
            ents = sorted((x[0], x[1], x[2], x[3] if len(x) > 3 else '') for x in c.resolved)
            idx = self._readings[key] = ([(a, b, n) for a, b, n, _ in ents], [a for a, _, _, _ in ents],
                                         {(a, b): k for a, b, _, k in ents if k})
        ents, starts, kinds = idx
        s0, e0 = idn['start'], idn['end']
        lo = bisect.bisect_left(starts, s0 - 1)
        hi = bisect.bisect_left(starts, e0)
        mine = [x for x in ents[lo:hi] if x[1] <= e0 and x[1] > s0]
        if not mine:
            return None
        # a name the token declares or binds is not a use of it: read the uses when there are any
        uses = [x for x in mine if kinds.get((x[0], x[1])) != 'b']
        binder = not uses
        if uses:
            mine = uses
        at = [x for x in mine if x[0] <= s0]
        if not at:
            return None
        hb = min(b for _, b, _ in at)
        hs = min(a for a, b, _ in at if b == hb)
        head = tuple(sorted({n for a, b, n in at if b == hb and n}))
        return Reading(head, (hs, hb), {n for _, _, n in mine if n} if not binder else set(), mine,
                       kinds.get((hs, hb)) == 'f', binder)

    def is_project(self, n):
        return n in self.owner

    def note_fallback(self, info, c, idn):
        self.fallbacks.append((info.path, c.start.line, idn['name']))

    def resolve(self, tok, ns, opens, m, used=None, field=False):
        """The project constants (env names) identifier `tok` may denote in module m, namespace ns,
        with project namespaces `opens` open. Over-approximates: every reading Lean could take,
        and when none, the reading with trailing fields (`h.mp`, `foo.1`) stripped. `field`: the
        token is a field (`(e).f`, `e |>.f`, `.f`; see is_field), never read lexically."""
        root = tok.startswith('_root_.')
        body = tok[len('_root_.'):] if root else tok
        for strip in range(0 if field else 3):
            # strip the token's own trailing fields, never the namespace's: inside namespace
            # `…Niltest`, `T.UnitIntervalValued` stripped as a whole name read as the structure
            # `Niltest` itself, so a binder needing a gone declaration looked satisfied (Erdős 3
            # v2 B109, B170)
            parts = body.split('.')
            if strip and len(parts) <= strip:
                break
            t = '.'.join(parts[:len(parts) - strip])
            cands = [t] if root else [join(p, t) for p in prefixes(ns)] + [join(o, t) for o in opens]
            alias = self.dup_alias.get(m, {})
            hits = [n for c in cands for n in self.pub.get(alias.get(c, c), ()) if self.visible(n, m)]
            if hits:
                return list(dict.fromkeys(hits))
        # dot notation on a local (`A.coord_eq` with `A : Space`, Erdős 3 B024), or a field
        # (`(E.rules ω).fixed_quadratic_memory`): read by its short name when that is (nearly)
        # unambiguous. `x.f` means `T.f` for the head T of x's type, so with `used` (the
        # declaration's compiled constants) a reading needs T.f or T among them (UniversalFInfinity
        # 2026-10-18: `w.support` read as Higman.RecognizingStack.support, `Subtype.val` as a
        # project structure's field `val`). That holds in a namespace shared with an external
        # bundle too (PosteriorReplicas 2026-10-23: OAI.PosteriorRegression was one, and the field
        # `fixed_quadratic_memory` became a false import of the theorem of that name); a project
        # lemma about a Mathlib type (`Finset.foo` on `s : Finset α`) has its type in the term
        if field or ('.' in tok and not tok.startswith('_root_.')):
            hits = [n for n in self.short.get(tok.rsplit('.', 1)[-1], ()) if self.visible(n, m)]
            if used is not None:
                hits = [n for n in hits if '.' in n and (n in used or n.rsplit('.', 1)[0] in used)]
            if 0 < len(hits) <= 2:
                return hits
        return []

    def resolve_lean(self, tok, ns, opens, m):
        """The reading Lean itself takes (ResolveName.resolveGlobalName): a match in the current
        namespace or an enclosing one, innermost first, wins over the root and the open namespaces;
        only without one are the root and the opens read together. Used to decide whether a
        context line still means what it meant (Hecke 7/8 B000, 2026-10-08: `variable (p : ι → O)`
        in namespace SecondPassArithmetic meant its own `O`; with it carved away, the opened
        `EisensteinEmbedding.O` and `ActualEisensteinCubic.O` became an ambiguous reading)."""
        if tok.startswith('_root_.'):
            return self.resolve(tok, ns, opens, m)
        hits, _ = self.lean_hits(tok, ns, opens, lambda n: self.visible(n, m))
        return hits or self.resolve(tok, ns, opens, m)

    def lean_hits(self, tok, ns, opens, ok):
        """resolve_lean's search over the constants n with ok(n): (hits, fields stripped)."""
        for strip in range(3):
            parts = tok.split('.')
            if strip and len(parts) <= strip:
                break
            t = '.'.join(parts[:len(parts) - strip])
            for p in prefixes(ns)[:-1]:
                hits = [n for n in self.pub.get(join(p, t), ()) if ok(n)]
                if hits:
                    return hits, strip
            hits = [n for c in [t] + [join(o, t) for o in opens]
                    for n in self.pub.get(c, ()) if ok(n)]
            if hits:
                return list(dict.fromkeys(hits)), strip
        return [], 0

    # ---------------------------------------------------------- dependencies
    def _owners(self, names, self_key):
        out = set()
        for n in names:
            o = self.owner.get(n)
            if o and o != self_key:
                out.add(o)
        return out

    def _source_refs(self, info, c, m, me, before=None):
        """Owners of the project names command c's source refers to (role `ref`), restricted to
        what module m could see: imported modules, or earlier commands of m."""
        opens = self.scope_opens(info, c, m)
        out = set()
        used = None
        if me in self.nodes:
            used = set()
            for n in self.nodes[me].names:
                x = self.consts.get(n)
                if x:
                    used.update(x['t'])
                    used.update(x['v'])
        for idn in c.idents or []:
            if idn['role'] not in ('ref', 'dot') or (before is not None and idn['start'] >= before):
                continue
            r = self.reading(info, c, idn)
            if r is not None:
                names = sorted(r.consts)
            elif idn['role'] != 'ref':
                continue
            else:
                names = self.resolve(idn['name'], decl_ns(c), opens, m, used,
                                     field=is_field(info, idn))
                if names:
                    self.note_fallback(info, c, idn)
            for n in names:
                o = self.owner.get(n)
                if not o or o == me:
                    continue
                on = self.nodes[o]
                if on.module == m and on.cmd >= c.index:
                    continue
                out.add(o)
        return out

    def _build_deps(self):
        self._variable_insts = {m: [(c.index, c.insts) for c in info.commands
                                    if c.short_kind == 'variable' and c.insts]
                                for m, info in self.infos.items()}
        for k, nd in self.nodes.items():
            info = self.infos[nd.module]
            c = info.commands[nd.cmd]
            if k in self.scoped:
                nd.sdeps = nd.sig = self._source_refs(info, c, nd.module, k)
                continue
            declared = set(c.names)
            for n in nd.names:
                x = self.consts[n]
                nd.term |= self._owners(x['t'] + x['v'], k)
                if n == k or pubname(n) in declared:
                    nd.tdeps |= self._owners(x['t'], k)
            nd.sdeps = self._source_refs(info, c, nd.module, k)
            vs = c.value_start.byte if c.value_start else None
            nd.sig = set(nd.tdeps) | self._source_refs(info, c, nd.module, k, before=vs)
            # the instances instance search used (a Prop instance such as `Fact`/`NeZero` is a
            # theorem whose use need not show anywhere else)
            nd.ideps = self.inst_owners(c.insts or (), k, nd.module, c.index)
            nd.sig |= self.inst_owners(c.sig_insts or (), k, nd.module, c.index)
            # a `variable` binder in scope stays in the carved file even when this declaration does
            # not use it, and elaborating it may need an instance that nothing else names
            # (Kirchberg–Rørdam: `variable (h0 : W.x 0 0 * v = v)` needs `NeZero rankNum`)
            for vi, vnames in self._variable_insts.get(nd.module, ()):
                if vi < c.index and _in_scope(info, vi, c):
                    owners = self.inst_owners(vnames, k, nd.module, vi)
                    nd.ideps |= owners
                    nd.sig |= owners
        # `attribute [simp] foo` marks foo; a notation in force is a dependency of what follows
        # that uses it: by Lean's record, the commands whose syntax contains the notation's kind
        # (and, through a notation written with another, that one's too); without a record, of
        # everything that follows in its scope (a false `import Theorems.*` edge when the piece
        # never used it: `local notation "DE" => double_eq` made size_zero, after it, need
        # double_eq, 2026-10-24)
        for m, info in self.infos.items():
            notations = []              # (opener, refs, kinds or None)
            by_kind = {}                # kind -> refs, transitively through notations it uses
            for c in info.commands:
                if c.short_kind == 'attribute':
                    for o in self._source_refs(info, c, m, None):
                        self.nodes[o].attributed = True
                elif c.short_kind in NOTATION and (m, c.index) not in self._scoped_cmds:
                    inner = c.context[-1][0] if c.context else None
                    refs = self._source_refs(info, c, m, None)
                    for kd in c.kinds_used or ():
                        refs |= by_kind.get(kd, set())
                    kinds = set(c.declares_kinds) if c.declares_kinds is not None else None
                    for kd in kinds or ():
                        by_kind[kd] = refs
                    notations.append((inner, refs, kinds))
                key = self.cmd_node.get((m, c.index))
                if key:
                    openers = {o for o, _ in c.context}
                    used = set(c.kinds_used) if c.kinds_used is not None else None
                    for inner, refs, kinds in notations:
                        if inner is not None and inner not in openers:
                            continue
                        if kinds is not None and used is not None and not kinds & used:
                            continue
                        self.nodes[key].ndeps |= refs - {key}
        self._add_default_simp_deps()
        for k, nd in self.nodes.items():
            nd.deps = nd.term | nd.sdeps | nd.ndeps | nd.ideps
        self._build_scoped_deps()

    def _add_default_simp_deps(self):
        """A declaration whose proof calls the default simp set (`simp`, `simpa`, `simp_all`,
        `dsimp`, `norm_num`, … without `only`) depends on its module's earlier `@[simp]` lemmas
        proved by `rfl`: simp uses such a lemma by definitional rewriting, which leaves no constant
        in the term (a lemma proved otherwise shows in the term when simp uses it). PeriodicLattice
        oaiq-067: `@[simp] encode_int_ofNat : encode (n : ℤ) = 2 * n := rfl` (library constants
        only, so no implicit_deps link either) and `simp [Nat.bodd]` proofs, carved into a bundle
        that did not import the lemmas ("unsolved goals"). An over-estimate: every such lemma of
        the module counts for every such call after it."""
        for m, info in self.infos.items():
            lemmas = []                  # (command index from which it is a simp lemma, node)
            for c in info.commands:
                k = self.cmd_node.get((m, c.index))
                if c.short_kind == 'attribute':
                    if any(_SIMP_ATTR.match(e) for e in attribute_entries(leanedit.text(info, c.index)) or ()):
                        lemmas += [(c.index, o) for o in self._source_refs(info, c, m, None)
                                   if self._rfl_theorem(o)]
                    continue
                if not k:
                    continue
                nd = self.nodes[k]
                if any(_SIMP_ATTR.match(a) for a in c.attrs or ()) and self._rfl_theorem(k):
                    lemmas.append((c.index, k))
                if lemmas and _default_simp_call(strip(leanedit.text(info, c.index))):
                    nd.sdeps |= {o for i, o in lemmas if i < c.index and o != k}

    def _rfl_theorem(self, k):
        """Is node k a theorem whose proof is `rfl` (simp then uses it as a dsimp lemma)?"""
        nd = self.nodes.get(k)
        if nd is None or not nd.theorem:
            return False
        info = self.infos[nd.module]
        c = info.commands[nd.cmd]
        if c.value_start is None:
            return False
        v = strip(info.text_bytes[c.value_start.byte:c.end.byte].decode('utf-8', 'replace'))
        return bool(_RFL_VALUE.match(v))

    def _add_coercion_instances(self):
        """Record the uses of coercion instances that elaborate away. `↑p` with `CoeSort Pack Type`
        becomes `p.carrier`, `f n` with a `CoeFun` instance `f.toFun n`: Lean unfolds the instance,
        so no constant and no `insts` entry names it (Kirchberg–Rørdam, batch 3: "Function
        expected" in the bundles). The coercion function stays, so a declaration whose constants
        name one that an instance of a coercion class wraps (its value's project constants other
        than its own type's) is taken to use that instance. An over-estimate when the function is
        also written out: the instance then comes along, which costs nothing."""
        wraps = {}
        for k, nd in self.nodes.items():
            cls = self.instance_class(k) if nd.instance else None
            if not cls or cls[0] not in COERCION_CLASSES:
                continue
            ts, vs = set(), set()
            for n in nd.names:
                x = self.consts.get(n) or {}
                ts.update(x.get('t', ()))
                vs.update(x.get('v', ()))
            w = vs - ts - set(nd.names)
            if not w:
                # the wrapped function is a projection of the type's own structure
                # (`⟨fun f => f.val⟩` on `abbrev Test := {f // …}`): the instance is then used by every
                # declaration that mentions the type (Elasticity, oaiq-006)
                w = {t for t in ts - set(nd.names) if t in self.owner}
            if w:
                wraps[k] = w
        if not wraps:
            return
        for k, nd in self.nodes.items():
            c = self.infos[nd.module].commands[nd.cmd]
            if c.insts is None or k in wraps:
                continue
            tc, vc = set(), set()
            for n in nd.names:
                x = self.consts.get(n) or {}
                tc.update(x.get('t', ()))
                vc.update(x.get('v', ()))
            for ik, w in wraps.items():
                if w & set(nd.names):      # the declaration of the wrapped type needs no instance on it
                    continue
                if w & (tc | vc):
                    c.insts = list(c.insts) + [n for n in self.nodes[ik].names if n not in c.insts]
                    if w & tc:
                        c.sig_insts = list(c.sig_insts or ()) + \
                            [n for n in self.nodes[ik].names if n not in (c.sig_insts or ())]

    def is_local_instance(self, k):
        """Is node k a `local instance` (visible only in the rest of its own section)? Read from its
        command's text alone: DeclGraph's instance flag (Meta.isInstance on the compiled
        environment) is False for every local instance, whose attribute ends with its section, so
        requiring it made this always False (2026-10-27)."""
        nd = self.nodes[k]
        if nd.cmd is None:
            return False
        return _local_instance(self.infos[nd.module], self.infos[nd.module].commands[nd.cmd])[0]

    def inst_problems(self, k):
        """[(class, {argument heads})]: what instance search solved in node k's elaboration
        (LeanInfo `inst_keys`); None without a record."""
        nd = self.nodes[k]
        keys = self.infos[nd.module].commands[nd.cmd].inst_keys
        if keys is None:
            return None
        return [(x.split()[0], set(x.split()[1:])) for x in keys]

    def instance_class(self, k):
        """(class, [argument heads]) of instance node k's conclusion (LeanInfo `declares`), or None."""
        nd = self.nodes[k]
        names = set(nd.names)
        for x in self.infos[nd.module].commands[nd.cmd].declares or ():
            if x[0] in names and x[1]:
                return x[1], x[2]
        return None

    def inst_owners(self, names, me, m, idx):
        """The nodes of the instances `names` (LeanInfo `insts`) that command idx of module m
        could have used: earlier in m, or a global or scoped one of a module m imports. Sibling
        modules' identical anonymous local instances share one generated name and one node
        (Problem340); another module's local instance is never the one used: the command that
        declared it in m is emitted again by the carver instead (Carver._reactivate)."""
        out = set()
        own = set(self.nodes[me].names) if me in self.nodes else set()
        for n in names:
            o = self.owner.get(n)
            if not o or o == me or n in own:
                continue
            on = self.nodes[o]
            if on.module == m:
                if on.cmd < idx:
                    out.add(o)
            elif self.sees(m, on.module) and not self.is_local_instance(o):
                out.add(o)
        return out

    def _scope_targets(self, tok, ns):
        """The namespaces `open tok`, written in namespace ns, may name (no existence check: a
        scope holding only notations has no constants)."""
        if tok.startswith('_root_.'):
            return {tok[len('_root_.'):]}
        return {join(p, tok) for p in prefixes(ns)}

    def _build_scoped_deps(self):
        """Every node that opens a scoped notation's scope (an `open` in its scopes or block, an
        `open … in` head, being inside the namespace, or following a core `scoped notation` in its
        block) and can see its module depends on it, statement included: the carved file repeats
        the `open`, which fails without the notation's bundle."""
        if not self.scoped:
            return
        by_scope = collections.defaultdict(list)
        for s, x in self.scoped.items():
            by_scope[x].append(s)

        def reach(a):
            seen, todo = set(), [a]
            while todo:
                for d in self.nodes[todo.pop()].deps:
                    if d not in seen and d in self.nodes:
                        seen.add(d)
                        todo.append(d)
            return seen
        reaches = {s: reach(s) for s in self.scoped}

        def sees(k, s):
            a, b = self.nodes[k], self.nodes[s]
            return a.cmd > b.cmd if a.module == b.module else self.sees(a.module, b.module)
        for m, info in self.infos.items():
            keys = [k for k in self.by_module.get(m, []) if k not in self.scoped]
            if not keys:
                continue
            blocks = collections.defaultdict(set)        # opener -> scopes opened somewhere in it
            for c in info.commands:
                if c.short_kind != 'open':
                    continue
                inner = c.context[-1][0] if c.context else None
                for idn in c.idents or []:
                    if idn['role'] == 'open':
                        blocks[inner] |= self._scope_targets(idn['name'], c.namespace) & set(by_scope)
            for k in keys:
                nd = self.nodes[k]
                c = info.commands[nd.cmd]
                want = set()
                for o, _ in c.context:
                    want |= blocks.get(o, set())
                want |= blocks.get(None, set())
                for h in c.heads or []:
                    if _head_kind(h) == 'open':
                        for idn in c.idents or []:
                            if idn['role'] == 'open' and h['start'] <= idn['start'] < h['end']:
                                want |= self._scope_targets(idn['name'], c.namespace) & set(by_scope)
                want |= {x for x in by_scope if c.namespace == x or c.namespace.startswith(x + '.')}
                got = {s for x in want for s in by_scope[x]}
                openers = {o for o, _ in c.context}
                for s in self.scoped:
                    sn = self.nodes[s]
                    sc = self.infos[sn.module].commands[sn.cmd]
                    if sn.module == m and sc.short_kind != 'scopedNS' and sc.context and \
                            sc.context[-1][0] in openers:
                        got.add(s)
                got = {s for s in got if sees(k, s) and k not in reaches[s]}
                if got:
                    nd.ndeps |= got
                    nd.sig |= got
                    nd.deps |= got

    # ---------------------------------------------------------- queries
    def closure(self, roots, stop=()):
        """roots and everything they depend on, not entering `stop` (except roots)."""
        s, todo, roots = set(), list(roots), set(roots)
        while todo:
            c = todo.pop()
            if c in s:
                continue
            s.add(c)
            if c in stop and c not in roots:
                continue
            todo += self.nodes[c].deps
        return s

    def extra_roots(self, keep, avail):
        """Instances and attributed declarations of the modules keep's modules see, whose
        dependencies are all present: typeclass search and `simp` use them with no trace in the
        term (Space.size_eq under `by simp`). Returns those to add."""
        have = set(keep) | set(avail)
        mask = 0
        for k in keep:
            mask |= self.closure_mask[self.nodes[k].module]
        cand = [k for k, nd in self.nodes.items()
                if (nd.instance or nd.attributed) and k not in have
                and mask >> self.mod_index[nd.module] & 1]
        added, changed = set(), True
        while changed:
            changed = False
            for k in cand:
                if k not in have and self.nodes[k].deps <= have:
                    have.add(k)
                    added.add(k)
                    changed = True
        return added

    def collision_renames(self):
        if getattr(self, '_collision_renames', None) is None:
            self._collision_renames = collision_renames(self)
        return self._collision_renames

    def have_names(self, keys):
        """The public names a set of nodes declares (what a file keeping or importing them has)."""
        out = {pubname(n) for k in keys for n in self.nodes[k].names}
        # a collided private declaration is deprivatized under its rename (`helper_p3`)
        ren = self.collision_renames()
        out |= {instance_ref(n, {}, ren) for k in keys for n in self.nodes[k].names if n in ren}
        # a scoped notation's scope exists where the notation does (`open scoped X` needs it)
        return out | {self.scoped[k] + '.«notation»' for k in keys if k in self.scoped}


def instance_ref(ik, inst_names, rename):
    """The name a file uses for the local instance node ik: the name Lean gave it in a bundle that
    kept it anonymous, else its public name under any collision rename."""
    if ik in inst_names:
        return inst_names[ik]
    pn = pubname(ik)
    if ik in rename:
        return pn.rsplit('.', 1)[0] + '.' + rename[ik] if '.' in pn else rename[ik]
    return pn


def instance_imported(ik, have, rename):
    """Does an imported file carry the local instance node ik as a plain constant? Not when its
    public name is shared by collided copies (rename): `have` holds public names, so another
    copy's bundle would stand in for this one; its renamed name is in `have` only with its own."""
    if ik in rename:
        return instance_ref(ik, {}, rename) in have
    return pubname(ik) in have


def collision_renames(g):
    """Private declarations whose public names collide (two modules' `private theorem helper`, in
    one carved file or deprivatized): {env name: new short name}, the same in every file. Also each
    renamed copy of a theorem two modules declare (`Graph._split_duplicates`): its declaration and
    the references meaning it get its new name (`bound_dup1`)."""
    out = {}
    for _, _, new, _ in getattr(g, 'duplicates', ()):
        for _, n in new:
            out[n] = n.rsplit('.', 1)[-1]
    for p, ns in g.pub.items():
        decl = sorted({g.owner[n] for n in ns if n == g.owner[n]})
        if len(decl) > 1 and any(n.startswith('_private.') for n in decl):
            for i, n in enumerate(sorted(decl, key=lambda n: (g.consts[n]['m'], n))):
                if n.startswith('_private.'):
                    out[n] = p.rsplit('.', 1)[-1] + '_p%d' % i
    return out


# ================================================================ costs

def parse_build_log(text):
    """{module: seconds} from `lake build` output (`✔ [3/9] Built M (1.5s)`, `(820ms)`)."""
    out = {}
    for m in re.finditer(r'Built (\S+) \(([\d.]+)(m?s)\)', text):
        out[m.group(1)] = float(m.group(2)) / (1000 if m.group(3) == 'ms' else 1)
    return out


def module_costs(g, times, scale=1.5, default=2.0, overhead=0.5):
    """Each module's elaboration time (from build logs; `default` when unknown), times `scale`,
    less the import overhead, shared among its declarations by text size."""
    cost = {}
    for m, keys in g.by_module.items():
        tot = sum(g.nodes[k].size for k in keys) or 1
        tm = max(times.get(m, default) * scale - overhead, 0.05)
        for k in keys:
            cost[k] = tm * g.nodes[k].size / tot
    return cost


def bundle_time(times, name):
    """A bundle's measurement in a times.json: carve_measure.py keys it `bundle:<name>`; older
    files used the bare name."""
    return times.get('bundle:' + name) or times.get(name)


def slow_bundles(bundles, times, limit):
    """The bundles measured (and compiled) over `limit` seconds, in plan order."""
    out = []
    for b in bundles:
        t = bundle_time(times, b['name'])
        if t and t.get('ok') and t['secs'] > limit:
            out.append(b['name'])
    return out


def calibrate_costs(cost, bundles, times, scale=1.5, overhead=5.0, floor=0.5):
    """Estimates corrected by measurement: each bundle built locally at -j1 in `secs` gets its
    declarations' costs rescaled (shares kept) to (secs - overhead) * scale, the import overhead
    being what an empty file of the same imports takes. Failed or unmeasured bundles keep their
    estimates. A re-plan on these costs splits exactly what measured heavy (Erdős 3 v2: build-log
    estimates put every bundle at 60 s; measured, 5 of 132 ran over 40 s local, up to 69 s)."""
    out = dict(cost)
    for b in bundles:
        t = bundle_time(times, b['name'])
        if not t or not t.get('ok'):
            continue
        est = sum(cost.get(k, 0.0) for k in b['nodes'])
        target = max(t['secs'] - overhead, floor) * scale
        for k in b['nodes']:
            if est > 0:
                out[k] = cost.get(k, 0.0) * target / est
            else:
                out[k] = target / len(b['nodes'])
    return out


def size_costs(g, bytes_per_second=2000):
    """Cost by size alone, when there are no build times."""
    return {k: nd.size / bytes_per_second for k, nd in g.nodes.items()}


# ================================================================ the plan

def ascii_ok(n):
    p = pubname(n)
    return all(ord(ch) < 128 for ch in p) and "'" not in p and '«' not in p


def bundle_name(prefix, i):
    return '%s%03d' % (prefix, i)


def _reduce(g_imports, ks):
    """Drop bundles implied by importing another one of ks."""
    reach = {}

    def r(k):
        if k not in reach:
            reach[k] = set()
            for j in g_imports[k]:
                reach[k] |= {j} | r(j)
        return reach[k]
    ks = set(ks)
    out = set(ks)
    for k in ks:
        out -= r(k)
    return out


def chunk_bundles(g, B, cost, bundle_budget, bundle_size, band_width=4.0, frozen=()):
    """Cut bundle material B into bundles that can publish in parallel.

    A unit is one module's bundle material (it keeps the module's scopes, variables and notations
    together). Units are layered by depth in the unit dependency DAG; consecutive layers form a
    band of cost about bundle_budget * band_width, and each band is split into bundles of cost at
    most bundle_budget along the connected components of its internal dependencies (the Erdős 3
    split's scheme, 2026-10-08). `frozen`: bundles already published, [[node, ...], ...], kept
    first and unchanged. Returns [[node, ...], ...] in an order where imports come first."""
    chunks = [list(f) for f in frozen]
    done = {k for f in frozen for k in f}
    rest = set(B) - done
    U = collections.defaultdict(list)
    for k in rest:
        U[g.nodes[k].module].append(k)
    ucost = {m: sum(cost[k] for k in ks) for m, ks in U.items()}
    usize = {m: sum(g.nodes[k].size for k in ks) for m, ks in U.items()}
    udeps = {m: set() for m in U}
    for m, ks in U.items():
        for k in ks:
            for d in g.nodes[k].deps:
                if d in rest and g.nodes[d].module != m:
                    udeps[m].add(g.nodes[d].module)
    lv = {}
    for m in g.topo(list(U)):
        lv[m] = 1 + max([lv[d] for d in udeps[m] if d in lv], default=0)
    bylv = collections.defaultdict(list)
    for m in U:
        bylv[lv[m]].append(m)
    bands, cur, c = [], [], 0.0
    for level in sorted(bylv):
        lc = sum(ucost[m] for m in bylv[level])
        if cur and c + lc > bundle_budget * band_width:
            bands.append(cur)
            cur, c = [], 0.0
        cur += bylv[level]
        c += lc
    if cur:
        bands.append(cur)
    for band in bands:
        bs = set(band)
        parent = {m: m for m in band}

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        for m in band:
            for d in udeps[m]:
                if d in bs:
                    parent[find(m)] = find(d)
        comps = collections.defaultdict(list)
        for m in band:
            comps[find(m)].append(m)
        packs = []
        for comp in sorted(comps.values(), key=lambda cc: (-sum(ucost[m] for m in cc), sorted(cc))):
            cc = sum(ucost[m] for m in comp)
            if cc > bundle_budget:
                part, pc = [], 0.0
                for m in sorted(comp, key=lambda m: (lv[m], m)):
                    if part and pc + ucost[m] > bundle_budget and lv[m] > lv[part[-1]]:
                        packs.append(part)
                        part, pc = [], 0.0
                    part.append(m)
                    pc += ucost[m]
                if part:
                    packs.append(part)
                continue
            for p in packs:
                if sum(ucost[m] for m in p) + cc <= bundle_budget and \
                        sum(usize[m] for m in p) + sum(usize[m] for m in comp) <= bundle_size:
                    p += comp
                    break
            else:
                packs.append(list(comp))
        # a pack's own order: by level, so a pack never precedes one it depends on
        packs.sort(key=lambda p: min(lv[m] for m in p))
        chunks += [sorted(k for m in p for k in U[m]) for p in packs]
    return _order_chunks(g, chunks, len(frozen))


def implicit_deps(g, keys, B):
    """{k: attributed bundle declarations k may use with no trace in its term}: those of B visible
    from k's module (an imported module, or earlier in its own) whose statement mentions a constant
    k uses, and that do not themselves need k. `simp`/`dsimp` use rfl lemmas and `@[simps]` lemmas
    silently, so list scheduling by recorded dependencies alone could put such a lemma where k's
    bundle cannot see it (Erdős 3 v2: six bundles failed with "simp made no progress")."""
    B = set(B)
    attr = [a for a in B if g.nodes[a].attributed and not g.nodes[a].instance]
    about = collections.defaultdict(set)
    for a in attr:
        for x in g.nodes[a].sig:
            about[x].add(a)
    needs = {}

    def closure_in_b(a):
        if a not in needs:
            seen, todo = set(), [a]
            while todo:
                c = todo.pop()
                for d in g.nodes[c].deps:
                    if d in B and d not in seen:
                        seen.add(d)
                        todo.append(d)
            needs[a] = seen
        return needs[a]
    out = {}
    for k in keys:
        nd = g.nodes[k]
        mask = g.closure_mask[nd.module]
        cand = set()
        for x in nd.deps | nd.sig:
            cand |= about.get(x, set())
        got = set()
        for a in cand:
            if a == k or a in nd.deps:
                continue
            an = g.nodes[a]
            if an.module == nd.module:
                if an.cmd >= nd.cmd:
                    continue
            elif not (mask >> g.mod_index[an.module] & 1):
                continue
            if k in closure_in_b(a):
                continue
            got.add(a)
        if got:
            out[k] = got
    return out


def chunk_bundles_schedule(g, B, cost, bundle_budget, bundle_size, frozen=(), extra=None):
    """Cut bundle material B into bundles by list scheduling at the declaration level.

    Declarations go in DFS post-order (a dependency first, and a module's material mostly
    together). A declaration joins the bundle of its dependencies when they all sit in one bundle
    of the highest level that still has room; otherwise it goes one level up, into the fullest
    bundle there with room, or a new one. A bundle's level is its import depth, so the depth stays
    near the dependency critical path divided by the budget instead of following the module DAG
    (Erdős 3: bands over modules gave depth 92; this gives about 16 on the same material,
    2026-10-16). `frozen` bundles come first, unchanged."""
    chunks = [list(f) for f in frozen]
    done = {k for f in frozen for k in f}
    rest = set(B) - done
    extra = extra or {}
    deps = {k: sorted(d for d in g.nodes[k].deps | extra.get(k, set()) if d in rest and d != k) for k in rest}
    order, seen = [], set()
    for r in sorted(rest):
        if r in seen:
            continue
        seen.add(r)
        stack = [(r, iter(deps[r]))]
        while stack:
            n, it = stack[-1]
            nx = next(it, None)
            if nx is None:
                order.append(n)
                stack.pop()
            elif nx not in seen:
                seen.add(nx)
                stack.append((nx, iter(deps[nx])))
    level, bcost, bsize, members = [], [], [], []
    where = {}
    room = collections.defaultdict(list)          # level -> bundles that may still take more
    for k in order:
        c, sz = cost.get(k, 0.0), g.nodes[k].size
        ds = {where[d] for d in deps[k] if d in where}
        top = max((level[b] for b in ds), default=0)
        tops = [b for b in ds if level[b] == top]
        b = None
        if len(tops) == 1 and bcost[tops[0]] + c <= bundle_budget and bsize[tops[0]] + sz <= bundle_size:
            b = tops[0]
        if b is None:
            lv = top + 1
            fits = [x for x in room[lv] if bcost[x] + c <= bundle_budget and bsize[x] + sz <= bundle_size]
            if fits:
                b = max(fits, key=lambda x: (bcost[x], -x))
            else:
                level.append(lv); bcost.append(0.0); bsize.append(0); members.append([])
                b = len(level) - 1
                room[lv].append(b)
        where[k] = b
        bcost[b] += c
        bsize[b] += sz
        members[b].append(k)
    for b in sorted(range(len(members)), key=lambda b: (level[b], b)):
        chunks.append(sorted(members[b]))
    return _order_chunks(g, chunks, len(frozen))


def _order_chunks(g, chunks, nfrozen):
    """Chunks topologically sorted by their dependencies (frozen ones first, as given)."""
    where = {k: i for i, ch in enumerate(chunks) for k in ch}
    deps = [{where[d] for k in ch for d in g.nodes[k].deps if d in where} - {i}
            for i, ch in enumerate(chunks)]
    order, state = list(range(nfrozen)), {}

    def visit(i):
        if state.get(i) == 2 or i < nfrozen:
            return
        if state.get(i) == 1:
            raise CarveError('bundle dependency cycle through %s' % chunks[i][:3])
        state[i] = 1
        for j in sorted(deps[i]):
            visit(j)
        state[i] = 2
        order.append(i)
    for i in range(nfrozen, len(chunks)):
        visit(i)
    return [chunks[i] for i in order]


def _bundle_reason(g, seeds, t):
    """Why theorem `t` is bundle material: the definition (a bundle seed) whose dependency chain
    reaches it, with the chain (StrictInverseFirstPower: the instance CompactSpace DiskFamily that
    several definitions need rests on the distortion theorem and Bieberbach's |a₂| ≤ 2). Only an
    error with `bundles_import_statements` off: on, `t` is published as a statement and the
    bundles import it."""
    parent, todo = {}, []
    for s in sorted(seeds):
        if not g.nodes[s].theorem and s not in parent:
            parent[s] = None
            todo.append(s)
    i = 0
    while i < len(todo):
        x = todo[i]
        i += 1
        if x == t:
            break
        for d in sorted(g.nodes[x].deps):
            if d in g.nodes and d not in parent:
                parent[d] = x
                todo.append(d)
    if t not in parent:
        return 'it is bundle material (a definition needs it)'
    chain = [t]
    while parent[chain[-1]] is not None:
        chain.append(parent[chain[-1]])
    return ('it is bundle material, because the definition %s needs it (%s); with '
            'bundles_import_statements off the bundle proves it itself. Turn that on (the default) '
            'to publish it as a statement the bundles import' % (chain[-1], ' -> '.join(reversed(chain))))


def _pin_chunks(g, pinned, B, taken, extra):
    """make_plan's `pinned` groups as bundle chunks: each group's names (owners), closed under
    dependencies and implicit dependencies within B, less what frozen bundles and earlier groups
    hold. Refuses an unknown name or one that is not bundle material."""
    if not pinned:
        return []
    groups = list(pinned.items()) if isinstance(pinned, dict) else [(str(i), grp) for i, grp in enumerate(pinned)]
    taken = set(taken)
    out = []
    for label, grp in groups:
        keys = []
        for x in grp:
            k = g.owner.get(x, x)
            if k not in g.nodes:
                raise CarveError('pinned group %s: unknown declaration %s' % (label, x))
            if k not in B:
                raise CarveError('pinned group %s: %s is not bundle material (%s)' % (
                    label, x, 'a theorem no definition needs' if g.nodes[k].theorem else
                    'not reachable from the targets'))
            keys.append(k)
        cl, todo = set(), list(keys)
        while todo:
            k = todo.pop()
            if k in cl or k in taken or k not in B:
                continue
            cl.add(k)
            todo += [d for d in g.nodes[k].deps | extra.get(k, set()) if d in g.nodes]
        taken |= cl
        out.append(sorted(cl))
    return out


def make_plan(g, targets, forced=(), budget=60.0, piece_size=700_000, bundle_budget=90.0,
              bundle_size=650_000, band_width=4.0, cost=None, frozen=None, bundle_prefix='Bundle',
              external_defs=None, statement_suffix='', external=(), chunker='bands', pinned=None,
              bundles_import_statements=True, promote_private=()):
    """The split: bundles, nodes (published statements) and each node's piece.

    - Bundle material B: every reachable non-theorem, what reachable statements need, their
      closure (a theorem a definition uses is proved inside the bundle, unless it is a target or
      forced and `bundles_import_statements` makes it a statement the bundle imports), and the
      instances and attributed declarations whose dependencies
      are then present.
    - Nodes: targets and `forced`, plus theorems promoted greedily, bottom-up, until each piece
      (its closure over non-node theorems) costs at most `budget` seconds and `piece_size` bytes.
      A node needs an ASCII public name and a statement that only uses bundle material; a private
      theorem is promoted only when listed in `promote_private` (a forced one always is a node).
    - `frozen`: (old plan, [bundle names]) of bundles already published, kept as they are.
    - `external_defs`: {declaration: module} provided by someone else's published Definitions bundle
      (Erdős 3: the target's own definitions in marwahaha's Def_ErdosReciprocal). They stay out of
      bundles and pieces; files that use them import the module. Someone else's published
      standalone *theorems* go here too (carve.py's `external_theorems`, module `Theorems.Thm_…`):
      never carved or republished, available everywhere, imported where used.
    - `statement_suffix`: published statement names are `<name><suffix>` (a fresh split of a
      development whose first split already took the names), except `external` statements,
      published by someone else under their own names.
    - `pinned`: groups of definitions ([[names]] or {label: [names]}), each its own bundle right
      after the frozen ones, closed under dependencies within the bundle material (earlier groups
      and frozen bundles excepted). A statement whose definitions are all pinned imports only those
      small bundles (UniversalFInfinity: Higman's, Whitehead's and Milnor's statements, which the
      scheduler had put into an 850-declaration bundle). A name that is not bundle material is
      refused.
    - `bundles_import_statements` (default on): a target or forced theorem that definitions need
      (bundle material) is published as a statement, and the bundles whose members need it import
      that statement (`statements` in the bundle) instead of proving it: prove.md's Platform
      Imports allow `import Theorems.Thm_…` in /submit-definition (a definition built by
      Classical.choose from an imported statement published, 2026-10-18), but only once that
      theorem is Proved ("Imported platform theorems must be Proved at submission time"). So what
      its statement and proof need from the bundles is pinned into bundles of its own, and the
      order is: those bundles, the statement, its proof (accepted), then the bundles importing it.
      The stub's `sorry` shows in those bundles' axioms locally, as in a piece's. Off, such a
      theorem is a CarveError, as before."""
    cost = cost if cost is not None else size_costs(g)
    targets, forced = list(targets), list(forced)
    for t in targets + forced:
        if t not in g.nodes:
            raise CarveError('unknown target %s' % t)
    reach = g.closure(targets + forced)
    seeds = {k for k in reach if not g.nodes[k].theorem}
    for k in reach:
        seeds |= g.nodes[k].sig
    fz_chunks = []
    if frozen:
        old, names = frozen
        byname = {b['name']: b for b in old['bundles']}
        fz_chunks = [[k for k in byname[n]['nodes'] if k in g.nodes] for n in names]
    ext = {g.owner.get(k, k): m for k, m in (external_defs or {}).items()}
    if frozen:
        # the frozen bundles import what their own carve took from someone else's published
        # bundles (its `external_defs`), so this carve does too: otherwise those declarations
        # become bundle material of this carve, a frozen bundle "needs" them from a new bundle
        # and the plan has a cycle (oaiq-057: DimensionTen Channel extending oaiq-033's carve,
        # whose Def_DimensionTenPair this carve's targets do not import; "needs krausMap from
        # bundle OAIQ033D009, not imported")
        conflicts = {}
        for k, m in (old.get('external_defs') or {}).items():
            k = g.owner.get(k, k)
            if k in g.nodes and k not in ext:
                ext[k] = m
            elif k in ext and ext[k] != m:
                # this carve takes k from another bundle than the frozen ones did: fine when one
                # imports the other, fatal when both declare it (w2/oaiq-113: Def_BassTrace vs
                # Def_BassTorsionFree); check_plan names it if a frozen bundle then breaks
                conflicts.setdefault(m, set()).add(ext[k])
    for k in ext:
        if k not in g.nodes:
            raise CarveError('unknown external definition %s' % k)
    B = g.closure(seeds) | {k for ch in fz_chunks for k in ch}
    B |= g.extra_roots(B, set())
    B -= set(ext)
    stmts = set()
    for t in targets + forced:
        if t in B:
            if not bundles_import_statements or not g.nodes[t].theorem:
                raise CarveError('%s cannot be a published statement: %s' % (t, _bundle_reason(g, seeds, t)))
            stmts.add(t)
    if stmts:
        # the bundles import these statements instead of proving them
        B = g.closure(seeds, stop=stmts) | {k for ch in fz_chunks for k in ch}
        B |= g.extra_roots(B, set())
        B -= set(ext) | stmts
    extra = implicit_deps(g, B, B) if chunker == 'schedule' else {}
    for ch in fz_chunks:
        # a published bundle's imports are fixed: implicit dependencies are for new material only
        # (oaiq-088: a frozen member 'used' a lemma of a new bundle that needs the frozen bundle)
        for k in ch:
            extra.pop(k, None)
    pin_chunks = _pin_chunks(g, pinned, B, {k for ch in fz_chunks for k in ch}, extra)
    if stmts:
        taken = {k for ch in fz_chunks + pin_chunks for k in ch}
        groups = []
        for t in sorted(stmts):
            # what t's statement and its whole proof need from the bundles: a bundle may import t
            # only once t is Proved ("Imported platform theorems must be Proved at submission
            # time", 2026-10-18), so t's piece must not need a bundle that imports t
            reach_t = g.closure([t], stop=B | (stmts - {t}))
            need_t = set(g.nodes[t].sig)
            for x in reach_t:
                need_t |= g.nodes[x].sig if x in stmts and x != t else g.nodes[x].deps
            need_t = sorted(d for d in need_t if d in B and d not in taken)
            grp = _pin_chunks(g, [need_t], B, taken, extra)[0] if need_t else []
            bad = sorted(k for k in grp if t in g.nodes[k].deps)
            if bad:
                raise CarveError('%s cannot be proved before the bundles importing it: its '
                                 'statement or proof uses %s, which needs it' % (t, bad))
            taken |= set(grp)
            if grp:
                groups.append(grp)
        pin_chunks = pin_chunks + groups
    T = reach - B - set(ext)
    kids = {k: [d for d in g.nodes[k].deps if d in T] for k in T}
    order, seen = [], set()
    for r in sorted(T):
        if r in seen:
            continue
        seen.add(r)
        stack = [(r, iter(sorted(kids[r])))]
        while stack:
            n, it = stack[-1]
            nx = next(it, None)
            if nx is None:
                order.append(n)
                stack.pop()
            elif nx not in seen:
                seen.add(nx)
                stack.append((nx, iter(sorted(kids[nx]))))
    nodes = set(targets) | set(forced)
    renames = collision_renames(g)

    b_or_ext = B | set(ext)

    def ok_node(k):
        nd = g.nodes[k]
        # not a statement whose universes occur only under `max`: the verifier's statement check can
        # get "stuck at solving universe constraint" there (oaiq-124); it stays in its importers'
        # pieces, as `fold` would put it
        return nd.theorem and not nd.private and ascii_ok(k) and nd.sig <= b_or_ext and \
            k not in renames and not max_only_universes(g, k)

    for t in sorted(nodes):
        if not g.nodes[t].theorem or g.nodes[t].sig - B - set(ext):
            raise CarveError('%s cannot be a published statement: %s' % (
                t, 'not a theorem' if not g.nodes[t].theorem else
                'its statement needs %s' % sorted(g.nodes[t].sig - B - set(ext))))

    if promote_private:
        # the automatic split of a slow piece (carve_pipeline calibrate_pieces) may promote these
        # private lemmas as well, as a `forced` private node name is: published under their public
        # name, deprivatized in the stub (oaiq-091: pieces of 60 and 394 private lemmas, forced by hand)
        public_ok, allowed = ok_node, set(promote_private)

        def ok_node(k):
            nd = g.nodes[k]
            return public_ok(k) or (k in allowed and nd.private and nd.theorem and ascii_ok(k)
                                    and nd.sig <= b_or_ext and k not in renames
                                    and not max_only_universes(g, k))

    def fresh(n):
        s, todo = set(), [n]
        while todo:
            c = todo.pop()
            if c in s:
                continue
            s.add(c)
            todo += [d for d in kids[c] if d not in nodes]
        return s

    def pcost(s):
        return sum(cost.get(x, 0.0) for x in s)

    def psize(s):
        return sum(g.nodes[x].size for x in s)
    over = []
    memo = {}
    for n in order:
        s = fresh(n)
        while pcost(s) > budget or psize(s) > piece_size:
            cand = [k for k in kids[n] if k not in nodes and ok_node(k)] or \
                [x for x in s if x != n and x not in nodes and ok_node(x)]
            if not cand:
                over.append(n)
                break
            k = max(cand, key=lambda k: (pcost(memo.get(k, {k})), k))
            nodes.add(k)
            s = fresh(n)
        memo[n] = s
    if chunker == 'schedule':
        chunks = chunk_bundles_schedule(g, B, cost, bundle_budget, bundle_size, fz_chunks + pin_chunks, extra)
    else:
        chunks = chunk_bundles(g, B, cost, bundle_budget, bundle_size, band_width, fz_chunks + pin_chunks)
    if frozen:
        names = list(frozen[1]) + [None] * (len(chunks) - len(frozen[1]))
    else:
        names = [None] * len(chunks)
    used = {n for n in names if n}
    i = 0
    for j, n in enumerate(names):
        if n is None:
            while bundle_name(bundle_prefix, i) in used:
                i += 1
            names[j] = bundle_name(bundle_prefix, i)
            used.add(names[j])
    bidx = {k: j for j, ch in enumerate(chunks) for k in ch}
    bimp = [set() for _ in chunks]
    nfz = len(fz_chunks)
    for j, ch in enumerate(chunks):
        if j < nfz and 'imports' in byname[names[j]]:
            # a published bundle imports what it was published with, never a new bundle: what its
            # members seem to need beyond that is inferred by newer graph rules (oaiq-120: the
            # published B000 "needed" 37 declarations of new bundles, and two import cycles)
            bimp[j] = {names.index(x) for x in byname[names[j]]['imports'] if x in names[:nfz]}
            continue
        for k in ch:
            for d in g.nodes[k].deps | extra.get(k, set()):
                if d in bidx and bidx[d] != j and not (j < nfz and bidx[d] >= nfz):
                    bimp[j].add(bidx[d])
    red = [_reduce(bimp, bimp[j]) for j in range(len(chunks))]
    bundles = [{'name': names[j], 'nodes': chunks[j], 'imports': [names[i] for i in sorted(red[j])],
                'cost': round(pcost(chunks[j]), 2), 'size': psize(chunks[j])}
               for j in range(len(chunks))]
    for j, b in enumerate(bundles):
        sts = sorted({d for k in chunks[j] for d in g.nodes[k].deps if d in stmts})
        if sts:
            b['statements'] = sts

    def need(keys):
        ex = implicit_deps(g, keys, B) if chunker == 'schedule' else {}
        return {bidx[d] for x in keys for d in g.nodes[x].deps | ex.get(x, set()) | {x} if d in bidx}
    pieces, stubs = {}, {}
    for n in sorted(nodes):
        keep = fresh(n)
        imps = {d for x in keep for d in g.nodes[x].deps if d in nodes and d not in keep}
        bks = need(keep) - {bidx[x] for x in keep if x in bidx}
        avail = {k for k in B if bidx[k] in _bundle_closure(bimp, bks)} | imps | set(ext)
        # an external declaration is imported, never kept (DiamondDistortion 2026-10-19: the
        # published `@[reducible] def Edge` came back as an extra root and clashed)
        keep |= {k for k in g.extra_roots(keep, avail) if k not in nodes and k not in B and k not in ext}
        bks = need(keep - B)
        pieces[n] = {'keep': sorted(keep), 'imports': sorted(imps),
                     'bundles': [names[i] for i in sorted(_reduce(bimp, bks))],
                     'cost': round(pcost(keep), 2), 'size': psize(keep)}
        sb = {bidx[d] for d in g.nodes[n].sig if d in bidx}
        stubs[n] = {'bundles': [names[i] for i in sorted(_reduce(bimp, sb))]}
    plan = {'version': 1, 'targets': targets, 'forced': forced, 'bundle_prefix': bundle_prefix,
            'budget': budget, 'bundles': bundles, 'nodes': sorted(nodes), 'pieces': pieces,
            'stubs': stubs, 'over': sorted(set(over)),
            'external_defs': dict(sorted(ext.items())), 'statement_suffix': statement_suffix,
            'external': sorted(external),
            'sorry': sorted(k for k in reach | B if g.nodes[k].sorry and k not in ext)}
    if frozen:
        plan['frozen'] = list(frozen[1])
    mu = {n: max_only_universes(g, n) for n in sorted(nodes) if max_only_universes(g, n)}
    if mu:
        plan['max_only_universes'] = mu
    if frozen and conflicts:
        plan['frozen_external_conflicts'] = {m: sorted(v) for m, v in sorted(conflicts.items())}
    if stmts:
        for n in resolve_piece_cycles(g, plan):
            plan['pieces'][n]['cost'] = round(pcost(set(plan['pieces'][n]['keep'])), 2)
    return plan


def max_only_universes(g, k):
    """The universe parameters of theorem node k's statement that occur in it only under `max` or
    `imax` (DeclGraph `mu`; oaiq-124: `{σ : Type (max us v)}`, WA "stuck at solving universe
    constraint `max ?u.5 ?u.11 =?= max ?u.10 ?u.11`" though the piece measured ok locally)."""
    return list((g.consts.get(k) or {}).get('mu') or ())


def _needs_piece(plan, bimp, n):
    """Indices of the bundles that wait for piece `n`: those importing statement n, and every
    bundle importing one of them."""
    direct = {i for i, b in enumerate(plan['bundles']) if n in b.get('statements', ())}
    if not direct:
        return set()
    return {i for i in range(len(plan['bundles'])) if _bundle_closure(bimp, [i]) & direct}


def piece_cycles(plan):
    """[(node, bundle)]: a piece that imports (directly, through bundle imports or through a
    statement it imports) a bundle waiting for that piece's own statement to be Proved."""
    pos, bimp, _ = _plan_index(plan)
    out = []
    for n, p in sorted(plan['pieces'].items()):
        tainted = _needs_piece(plan, bimp, n)
        if not tainted:
            continue
        cl = _bundle_closure(bimp, [pos[x] for x in p['bundles'] if x in pos])
        for i in p['imports']:
            cl |= _bundle_closure(bimp, [pos[x] for x in plan['stubs'][i]['bundles'] if x in pos])
        for j in sorted(cl & tainted):
            out.append((n, plan['bundles'][j]['name']))
    return out


def resolve_piece_cycles(g, plan):
    """Make each piece caught in a publish cycle (piece_cycles) self-contained: it imports only
    its own statement's bundles (published before the statement) and statements whose bundles do
    not wait for it, and keeps everything else its proof needs, bundle material included
    (ZeroTemperatureSK 2026-10-18, done by hand there with selfcontained_pieces.py). Edits `plan`
    in place; returns the nodes changed. A statement whose own bundles wait for its proof cannot
    be published at all: CarveError."""
    pos, bimp, _ = _plan_index(plan)
    names = [b['name'] for b in plan['bundles']]
    ext = set(plan.get('external_defs') or {})
    nodes = set(plan['nodes'])

    def cl(bs):
        return _bundle_closure(bimp, [pos[x] for x in bs if x in pos])

    changed = []
    for n in sorted({c[0] for c in piece_cycles(plan)}):
        tainted = _needs_piece(plan, bimp, n)
        own = plan['stubs'].get(n, {}).get('bundles', [])
        if cl(own) & tainted:
            raise CarveError('%s cannot be published: its statement needs bundles that wait for '
                             'its proof (%s)' % (n, ', '.join(names[j] for j in sorted(cl(own) & tainted))))
        safe = {x for x in nodes if x != n and not (cl(plan['stubs'][x]['bundles']) & tainted)}
        have_b = set(cl(own))
        for x in safe:
            have_b |= cl(plan['stubs'][x]['bundles'])
        avail = {k for j in have_b for k in plan['bundles'][j]['nodes']} | ext
        stop = avail | safe
        keep = {k for k in g.closure([n], stop=stop) if k == n or k not in stop}
        keep |= {k for k in g.extra_roots(keep, stop) if k not in stop and k not in nodes}
        bad = sorted(k for k in keep if g.nodes[k].sorry)
        if bad:
            raise CarveError('self-contained piece %s would contain sorry: %s' % (n, bad))
        imps = sorted({d for k in keep for d in g.nodes[k].deps if d in safe and d not in keep})
        p = plan['pieces'][n]
        p.update(keep=sorted(keep), imports=imps, bundles=[names[i] for i in sorted(_reduce(bimp, set(cl(own))))],
                 size=sum(g.nodes[k].size for k in keep), selfcontained=True)
        changed.append(n)
    return changed


def split_bundles(g, plan, names, cost, budget, bundle_prefix=None):
    """The plan with each bundle in `names` cut into balanced parts of cost at most about `budget`
    (in dependency order, so a part rests only on earlier parts), and every other bundle kept as
    it is: same declarations, same name; only import lists and the bundles statements and pieces
    import are recomputed. The first part keeps the bundle's name, the others take new names.
    A measured re-plan reshuffles every bundle; this touches only the slow ones (Erdős 3 v2,
    2026-10-17: 11 of 298 bundles over 60 s local)."""
    prefix = bundle_prefix or plan.get('bundle_prefix', 'Bundle')
    B = {k for b in plan['bundles'] for k in b['nodes']}
    extra = implicit_deps(g, B, B)
    used = {b['name'] for b in plan['bundles']}
    nxt = [0]

    def fresh_name():
        while bundle_name(prefix, nxt[0]) in used:
            nxt[0] += 1
        used.add(bundle_name(prefix, nxt[0]))
        return bundle_name(prefix, nxt[0])
    chunks, cnames = [], []
    for b in plan['bundles']:
        if b['name'] not in names:
            chunks.append(list(b['nodes']))
            cnames.append(b['name'])
            continue
        mine = list(b['nodes'])
        inside = set(mine)
        total = sum(cost.get(k, 0.0) for k in mine)
        k = max(1, -(-int(total * 1000) // int(budget * 1000)))
        if k == 1:
            chunks.append(mine)
            cnames.append(b['name'])
            continue
        target = total / k
        # dependency order (stable): a declaration after everything of this bundle it needs
        order, seen = [], set()

        def visit(x):
            if x in seen:
                return
            seen.add(x)
            for d in sorted(g.nodes[x].deps | extra.get(x, set())):
                if d in inside:
                    visit(d)
            order.append(x)
        for x in mine:
            visit(x)
        parts, cur, cc = [], [], 0.0
        for x in order:
            c = cost.get(x, 0.0)
            if cur and cc + c > target * 1.1 and len(parts) < k - 1:
                parts.append(cur)
                cur, cc = [], 0.0
            cur.append(x)
            cc += c
        parts.append(cur)
        for i, part in enumerate(parts):
            chunks.append(part)
            cnames.append(b['name'] if i == 0 else fresh_name())
    bidx = {k: j for j, ch in enumerate(chunks) for k in ch}
    bimp = [set() for _ in chunks]
    for j, ch in enumerate(chunks):
        for k in ch:
            for d in g.nodes[k].deps | extra.get(k, set()):
                if d in bidx and bidx[d] != j:
                    bimp[j].add(bidx[d])
    # a part may now be needed by a bundle listed before it: order the chunks topologically,
    # keeping the plan's order wherever it is already valid
    order, state = [], {}

    def place(j):
        if state.get(j) == 2:
            return
        if state.get(j) == 1:
            raise CarveError('bundle split made an import cycle at %s' % cnames[j])
        state[j] = 1
        for i in sorted(bimp[j]):
            place(i)
        state[j] = 2
        order.append(j)
    for j in range(len(chunks)):
        place(j)
    remap = {j: i for i, j in enumerate(order)}
    chunks = [chunks[j] for j in order]
    cnames = [cnames[j] for j in order]
    bimp = [{remap[i] for i in bimp[j]} for j in order]
    bidx = {k: j for j, ch in enumerate(chunks) for k in ch}
    red = [_reduce(bimp, bimp[j]) for j in range(len(chunks))]
    old = {b['name']: b for b in plan['bundles']}
    bundles = []
    for j, ch in enumerate(chunks):
        bundles.append({'name': cnames[j], 'nodes': ch, 'imports': [cnames[i] for i in sorted(red[j])],
                        'cost': round(sum(cost.get(k, 0.0) for k in ch), 2),
                        'size': sum(g.nodes[k].size for k in ch)})
    # statements the bundles import (bundles_import_statements): each part keeps those its members need
    sts_all = {s for b in plan['bundles'] for s in b.get('statements', ())}
    for b in bundles:
        sts = sorted({d for k in b['nodes'] for d in g.nodes[k].deps if d in sts_all})
        if sts:
            b['statements'] = sts
    out = dict(plan)
    out['bundles'] = bundles

    def need(keys):
        ex = implicit_deps(g, keys, B)
        return {bidx[d] for x in keys for d in g.nodes[x].deps | ex.get(x, set()) | {x} if d in bidx}
    pieces = {}
    for n, pc in plan['pieces'].items():
        keep = set(pc['keep'])
        pieces[n] = dict(pc, bundles=[cnames[i] for i in sorted(_reduce(bimp, need(keep - B)))])
    stubs = {}
    for n in plan['stubs']:
        sb = {bidx[d] for d in g.nodes[n].sig if d in bidx}
        stubs[n] = {'bundles': [cnames[i] for i in sorted(_reduce(bimp, sb))]}
    out['pieces'], out['stubs'] = pieces, stubs
    return out


def _bundle_closure(bimp, ks):
    out, todo = set(), list(ks)
    while todo:
        k = todo.pop()
        if k in out:
            continue
        out.add(k)
        todo += bimp[k]
    return out


def restore_cut_bundle_imports(plan, real, need=None):
    """`plan` with each bundle's imports as its real text has them (`real`: {bundle: [bundle, ...]}),
    and each stub and piece importing, beside its own bundles, every bundle the plan's import graph
    made it reach that the real one no longer does. A bundle published with a definitions import cut
    (an unused one, by the old --drop-false-edges) otherwise leaves the files that reached a bundle
    through it unable to see it (oaiq-010: "Unknown identifier `holderShift`" on three statements).
    `need(kind, node)` ('stubs' or 'pieces'), when given, is the set of bundles the file uses: only
    those are added, so a published file that never used the lost bundle keeps its frozen text.
    Returns `plan` itself when nothing was cut."""
    names = [b['name'] for b in plan['bundles']]
    pos = {n: i for i, n in enumerate(names)}
    pimp = [[pos[x] for x in b['imports'] if x in pos] for b in plan['bundles']]
    rimp = [[pos[x] for x in real.get(b['name'], b['imports']) if x in pos] for b in plan['bundles']]
    if all(set(pimp[i]) <= set(rimp[i]) for i in range(len(names))):
        return plan

    def fix(kind, n, e):
        ks = [pos[x] for x in e['bundles'] if x in pos]
        want = _bundle_closure(pimp, ks)
        add = want - _bundle_closure(rimp, ks)
        if add and need is not None:
            add &= {pos[x] for x in need(kind, n) if x in pos}
        if not add:
            return e
        return dict(e, bundles=[names[i] for i in sorted(_reduce(rimp, set(ks) | add))])
    out = dict(plan, bundles=[dict(b, imports=[names[i] for i in rimp[j]]) for j, b in enumerate(plan['bundles'])])
    for k in ('stubs', 'pieces'):
        if k in plan:
            out[k] = {n: fix(k, n, e) for n, e in plan[k].items()}
    return out


def fold_statements(plan, nodes):
    """A copy of `plan` in which each of `nodes` is no longer a statement: its piece's declarations,
    statement imports and bundles go into every piece that imported it (transitively, when a folded
    statement imports another), and it leaves `nodes`, `pieces` and `stubs`; `plan['folded']` lists
    every folded node. The importers' statements stay as they are, so a published carve can drop a
    statement nothing can prove and re-prove its importers with self-contained pieces.

    oaiq-039 (2026-10-28): 13 universe-polymorphic statements got WA "failed to synthesize CoeT ...
    (deterministic) timeout at `typeclass`" for every proof. The verifier falls back to a `CoeT`
    search when it compares a polymorphic statement with `solution`, and that search timed out on
    their types (p2mlib.localcheck reproduces it). Refuses a target, an external statement, a node
    that is not a statement of the plan, and one a bundle imports."""
    import copy
    plan = copy.deepcopy(plan)
    fold = set(nodes)
    for n in sorted(fold):
        if n not in plan['pieces']:
            raise CarveError('%s is not a statement of this plan' % n)
        if n in plan.get('targets', ()) or n in plan.get('external', ()):
            raise CarveError('%s is a target: it cannot be folded into another piece' % n)
        users = [b['name'] for b in plan['bundles'] if n in b.get('statements', ())]
        if users:
            raise CarveError('%s is imported by bundle(s) %s: it cannot be folded' % (n, ', '.join(users)))
    pos, bimp, _ = _plan_index(plan)
    names = [b['name'] for b in plan['bundles']]
    changed = True
    while changed:
        changed = False
        for p in plan['pieces'].values():
            for c in sorted(set(p['imports']) & fold):
                q = plan['pieces'][c]
                p['keep'] = sorted(set(p['keep']) | set(q['keep']))
                p['imports'] = sorted((set(p['imports']) - {c}) | set(q['imports']))
                bks = _reduce(bimp, {pos[b] for b in p['bundles'] + q['bundles']})
                p['bundles'] = [names[i] for i in sorted(bks)]
                p['cost'] = round(p.get('cost', 0) + q.get('cost', 0), 2)
                if 'size' in p or 'size' in q:
                    p['size'] = p.get('size', 0) + q.get('size', 0)
                changed = True
    for n in fold:
        del plan['pieces'][n]
        plan['stubs'].pop(n, None)
    plan['nodes'] = [n for n in plan['nodes'] if n not in fold]
    plan['over'] = [n for n in plan.get('over', []) if n not in fold]
    plan['folded'] = sorted(set(plan.get('folded', [])) | fold)
    return plan


def fold_problems(g, before, after):
    """check_plan's reports on the folded plan `after` that the plan `before` did not already have."""
    old = set(check_plan(g, before))
    return [p for p in check_plan(g, after) if p not in old]


def _plan_index(plan):
    pos = {b['name']: i for i, b in enumerate(plan['bundles'])}
    bimp = [[pos[x] for x in b['imports'] if x in pos] for b in plan['bundles']]
    bidx = {k: i for i, b in enumerate(plan['bundles']) for k in b['nodes']}
    return pos, bimp, bidx


def bundle_cycles(g, plan):
    """The import cycles among the plan's bundles, read from what their members need (not from
    their recorded imports, which `_reduce` empties on a cycle): one entry per cyclic strongly
    connected component, [(bundle, member, needed declaration, needed bundle), …] along a cycle
    through it. A cycle cannot be published in any order (UniversalFInfinity 2026-10-18: a pinned
    bundle missed one dependency, and the check said only "not imported")."""
    names = [b['name'] for b in plan['bundles']]
    where = {k: i for i, b in enumerate(plan['bundles']) for k in b['nodes']}
    pos = {n: i for i, n in enumerate(names)}
    frozen = _frozen_bundles(plan)
    why = {}
    for i, b in enumerate(plan['bundles']):
        if b['name'] in frozen:
            # published: its imports are what it was compiled with, its members' needs are inferred
            for x in b['imports']:
                if x in pos:
                    why.setdefault((i, pos[x]), ('(published imports)', x))
            continue
        for k in b['nodes']:
            for d in sorted(g.nodes[k].deps):
                j = where.get(d)
                if j is not None and j != i and (i, j) not in why:
                    why[(i, j)] = (k, d)
    succ = collections.defaultdict(list)
    for i, j in sorted(why):
        succ[i].append(j)
    # Tarjan's strongly connected components, iteratively
    index, low, on, stack, comps, counter = {}, {}, set(), [], [], [0]
    for root in range(len(names)):
        if root in index:
            continue
        work = [(root, iter(succ[root]))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        on.add(root)
        while work:
            v, it = work[-1]
            w = next(it, None)
            if w is None:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    comp = []
                    while True:
                        x = stack.pop()
                        on.discard(x)
                        comp.append(x)
                        if x == v:
                            break
                    if len(comp) > 1:
                        comps.append(sorted(comp))
            elif w not in index:
                index[w] = low[w] = counter[0]
                counter[0] += 1
                stack.append(w)
                on.add(w)
                work.append((w, iter(succ[w])))
            elif w in on:
                low[v] = min(low[v], index[w])
    out = []
    for comp in comps:
        inside = set(comp)
        # one cycle through the component's first bundle, by breadth-first search back to it
        start = comp[0]
        prev, todo = {start: None}, [start]
        end = None
        while todo and end is None:
            v = todo.pop(0)
            for w in succ[v]:
                if w not in inside:
                    continue
                if w == start:
                    end = v
                    break
                if w not in prev:
                    prev[w] = v
                    todo.append(w)
        path = [end]
        while prev[path[-1]] is not None:
            path.append(prev[path[-1]])
        path.reverse()
        cyc = path + [start]
        out.append([(names[a], why[(a, b)][0], why[(a, b)][1], names[b]) for a, b in zip(cyc, cyc[1:])])
    return out


def _frozen_bundles(plan):
    """The plan's frozen (published, compiled) bundles whose members' needs are not checked: all of
    `plan['frozen']`, unless the frozen carve took declarations from another external bundle than
    this one (`frozen_external_conflicts`): then a need is real, and reported with that."""
    if plan.get('frozen_external_conflicts'):
        return set()
    return set(plan.get('frozen') or ())


def check_plan(g, plan):
    """What would not compile: every dependency of a bundle member in its bundle or one it
    imports; of a piece, in the piece, an imported statement or its bundles; of a statement, in
    its bundles. A missing definition is Erdős 3 B006 ("Unknown identifier `A.space`"). The plan's
    `external_defs` (someone else's published bundle) are available to every file. A frozen bundle
    (`plan['frozen']`, published and compiled) is not checked: what its members seem to need beyond
    its published imports is inferred by newer graph rules, not real (oaiq-120). Returns a list
    of problems (empty: the plan is consistent)."""
    pos, bimp, bidx = _plan_index(plan)
    frozen = _frozen_bundles(plan)
    ext = set(plan.get('external_defs') or {})
    probs = []
    # a bundle or a proof piece may not rest on `sorry` (Erdős 3 B022: a port's stubbed proof in a
    # bundle; "declaration uses `sorry`"); only a statement stub's own proof is `sorry`
    for b in plan['bundles']:
        for k in b['nodes']:
            if g.nodes[k].sorry:
                probs.append('bundle %s: %s uses sorry' % (b['name'], k))
    for n, p in plan['pieces'].items():
        for k in p['keep']:
            if g.nodes[k].sorry:
                probs.append('piece %s: %s uses sorry' % (n, k))
    for n, b in piece_cycles(plan):
        probs.append('publish cycle: piece %s imports bundle %s, which waits for statement %s to be '
                     'Proved (resolve_piece_cycles makes the piece self-contained)' % (n, b, n))
    for cyc in bundle_cycles(g, plan):
        probs.append('bundle import cycle %s: %s' % (
            ' -> '.join([c[0] for c in cyc] + [cyc[0][0]]),
            '; '.join('%s in %s needs %s from %s' % (k, a, d, b) for a, k, d, b in cyc)))
    for i, b in enumerate(plan['bundles']):
        late = [x for x in b['imports'] if pos.get(x, len(pos)) >= i]
        if late:
            msg = 'bundle %s imports a later or unknown bundle (%s)' % (b['name'], ', '.join(late))
            cf = plan.get('frozen_external_conflicts')
            if cf:
                msg += ('; the frozen bundles were carved against %s, this carve takes the same '
                        'declarations from %s: if those bundles declare the same names no file can '
                        'import both, so carve fresh (no frozen) with a statement_suffix' % (
                            ', '.join(sorted(cf)), ', '.join(sorted({x for v in cf.values() for x in v}))))
            probs.append(msg)
        cl = _bundle_closure(bimp, [i])
        sts = set(b.get('statements', ()))
        for st in sts:
            cl |= _bundle_closure(bimp, [pos[x] for x in plan['stubs'].get(st, {}).get('bundles', ())])
        if b['name'] in frozen:
            continue
        for k in b['nodes']:
            for d in sorted(g.nodes[k].deps - ext - sts):
                if d not in bidx:
                    probs.append('bundle %s: %s needs %s, which is in no bundle' % (b['name'], k, d))
                elif bidx[d] not in cl:
                    probs.append('bundle %s: %s needs %s from bundle %s, not imported' % (
                        b['name'], k, d, plan['bundles'][bidx[d]]['name']))
    nodes = set(plan['nodes'])
    for n, p in plan['pieces'].items():
        cl = _bundle_closure(bimp, [pos[x] for x in p['bundles']])
        for i in p['imports']:
            cl |= _bundle_closure(bimp, [pos[x] for x in plan['stubs'][i]['bundles']])
        have = set(p['keep']) | set(p['imports']) | ext
        for k in p['keep']:
            for d in sorted(g.nodes[k].deps):
                if d in have or (d in bidx and bidx[d] in cl):
                    continue
                probs.append('piece %s: %s needs %s, neither kept, imported nor in its bundles' % (
                    n, k, d))
        if not set(p['imports']) <= nodes:
            probs.append('piece %s imports a non-node' % n)
    for n, s in plan['stubs'].items():
        cl = _bundle_closure(bimp, [pos[x] for x in s['bundles']])
        for d in sorted(g.nodes[n].sig - ext):
            if not (d in bidx and bidx[d] in cl):
                probs.append('statement %s needs %s, not in its bundles' % (n, d))
    return probs


def _could_match(g, k, i):
    """Could instance i answer an instance problem of declaration k? Its type mentions a project
    declaration k uses, or only library types (a coarse test: types are compared by the project
    declarations they mention), or instance search solved, in k, a problem of i's class whose
    argument heads include i's (LeanInfo `inst_keys`, `declares`): CoulombAtom oaiq-071, the
    instance `MeasurableSpace SpatialRotation` (an abbrev of a subtype, heads `Subtype`) and
    radialAverage_integrable, which mentions no project declaration of its type but solved
    `MeasurableSpace (Subtype …)` problems (SpatialRotation sits inside radialAverage's
    definition); not hidden, the proof found it instead of `Subtype.instMeasurableSpace`."""
    td = g.nodes[i].tdeps - {i}
    if not td or td & (g.nodes[k].deps | g.nodes[k].sig):
        return True
    ci = g.instance_class(i)
    asked = g.inst_problems(k) if ci else None
    if not asked:
        return False
    # a head that is a project abbreviation may show unfolded in the problem (`Subtype`), as it does
    # to instance search: it matches anything
    hs = {h for h in ci[1] or () if not _reducible_decl(g, h)}
    return any(cls == ci[0] and hs <= heads for cls, heads in asked)


def _reducible_decl(g, n):
    """Is n a project `abbrev` or `@[reducible]` declaration (instance search sees through it)?"""
    k = g.owner.get(n)
    if k is None or k not in g.nodes:
        return False
    nd = g.nodes[k]
    c = g.infos[nd.module].commands[nd.cmd]
    return c.decl_kind == 'abbrev' or any(a.split()[-1] == 'reducible' for a in c.attrs or ())


# classes an instance of the key also answers problems of, through a parent projection
# (`BorelSpace.opensMeasurable`: an `OpensMeasurableSpace X` problem is solved by a `BorelSpace X` instance)
_PARENT_CLASSES = {'BorelSpace': ('OpensMeasurableSpace',)}


def _could_answer(inst_cmd, c):
    """Did instance search solve, in command c, a problem that the instance declared by inst_cmd
    could answer: the same class, with the instance's head constants among the problem's? An
    instance can win a subproblem and then be replaced by a defeq one in the final term, leaving no
    constant and no `insts` entry (Kirchberg–Rørdam `local instance : SMul ℂ Defect`, used while
    elaborating `Defect →ₗ[ℂ] A`; carved away, instance search timed out). The class problems are
    LeanInfo's `inst_keys`."""
    asked = [x.split() for x in c.inst_keys or ()]
    for d in inst_cmd.declares or ():
        if not d[1]:
            continue
        heads = set(d[2] or ())                      # none: a fully generic `(β : Type) : DecidableEq β`
        classes = (d[1],) + _PARENT_CLASSES.get(d[1], ())
        if any(p[0] in classes and heads <= set(p[1:]) for p in asked):
            return True
        # a decidability instance can sit in an argument unification assigned (`rw [lemma]`, a `Finset`
        # lemma's `[DecidableEq α]`), so nothing records a `Decidable*` problem; it counts when its
        # type's head constants occur among the command's problems of any class (DilutedSpin
        # `DecidableEq (Edge S)`, whose command asks only `Fintype Edge`)
        if d[1].startswith('Decidable') and heads and any(heads <= set(p[1:]) for p in asked):
            return True
        if d[1].startswith('Decidable') and asked:
            # generic `(β : Type) : DecidableEq β`: in force for every problem of its section. With head
            # constants too: the record may show the type unfolded (`DecidableEq (Block w)` with
            # `abbrev Block := Fin w × Bool` against a `Fintype Prod …` problem, SharpRamsey oaiq-045),
            # and a decidability instance was in force in its section anyway, so keeping it is safe
            return True
    return False


def _global_simp(g, k):
    """Is node k a declaration carrying a global `@[simp]` (not `local`/`scoped`) attribute of its own?"""
    nd = g.nodes[k]
    if k in g.scoped:
        return False
    c = g.infos[nd.module].commands[nd.cmd]
    return any(re.match(r'simp(?![\w\-])', a.strip()) for a in c.attrs or ())


def _global_instance(g, k):
    """Is node k an instance every importer of its file sees (not `local`/`scoped`)?"""
    nd = g.nodes[k]
    if not nd.instance:
        return False
    info = g.infos[nd.module]
    c = info.commands[nd.cmd]
    head = info.text_bytes[c.start.byte:c.end.byte][:400].decode('utf-8', 'ignore')
    return not re.match(r'\s*(?:/--.*?-/\s*)?(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?'
                        r'(?:local|scoped)\b', head, re.S)


def instance_leaks(g, plan):
    """[(item, declaration, instance)]: a file of the plan (`bundle:B`, `statement:N`, `piece:N`)
    makes a global instance visible to a declaration it carves that the declaration's own module
    could not see there: declared later in its own module and imported through a bundle (one from a
    module it does not import is hidden again by `attribute [-instance]`, Carver._unseen_instances), and the
    instance's type mentions something the declaration uses (or only library types). Type class
    search may then take another path: RationalHitting (2026-10-24), the instance witnessCharZero
    of Generator.lean reached the carved list_hits (Certificates.lean) through a bundle, and
    `algebraMap ℚ` elaborated through it, so a `rwa [RingHom.ext_rat …]` no longer matched.
    Reported: an instance whose type mentions something the declaration uses (or only library
    types), and, where the port recorded the problems instance search solved there (LeanInfo
    `inst_keys`), only one of a class it solved some problem of. Not exact, and cannot be: the new
    instance can open a path whose subgoal failed in the original, which leaves no trace (in
    list_hits' `algebraMap ℚ WitnessField` the path through DivisionRing.toRatAlgebra needs a
    `CharZero WitnessField`, which only the carved file has; the original solved only `CharZero ℂ`
    problems). A warning: whether type class search takes the new path there is not known."""
    pos, bimp, _ = _plan_index(plan)
    ext = set(plan.get('external_defs') or {})

    def bundles_have(names):
        cl = _bundle_closure(bimp, [pos[x] for x in names if x in pos])
        return {k for i in cl for k in plan['bundles'][i]['nodes']}
    inst = {k for k in g.nodes if k not in ext and _global_instance(g, k)}

    def saw(k, i):
        # an instance of a module k's module does not import is hidden again in every carved file
        # (Carver._unseen_instances); only a later one of k's own module can leak
        a, b = g.nodes[k], g.nodes[i]
        return b.cmd < a.cmd if a.module == b.module else True

    def check(item, keep, visible):
        out = []
        cand = [i for i in visible & inst]
        for k in sorted(keep):
            if k not in g.nodes:
                continue
            asked = g.inst_problems(k)
            for i in sorted(cand):
                if i == k or saw(k, i):
                    continue
                ci = g.instance_class(i)
                if asked is not None and ci and ci[0] not in {cls for cls, _ in asked}:
                    continue
                if _could_match(g, k, i):
                    out.append((item, k, i))
        return out
    leaks = []
    for b in plan['bundles']:
        vis = bundles_have(b['imports']) | set(b['nodes'])
        for st in b.get('statements', ()):
            vis |= bundles_have(plan['stubs'][st]['bundles'])
        leaks += check('bundle:' + b['name'], b['nodes'], vis)
    for n, s in plan['stubs'].items():
        if n not in plan.get('external', ()):
            leaks += check('statement:' + n, [n], bundles_have(s['bundles']))
    for n, p in plan['pieces'].items():
        vis = bundles_have(p['bundles']) | set(p['keep'])
        for i in p['imports']:
            vis |= bundles_have(plan['stubs'][i]['bundles'])
        leaks += check('piece:' + n, p['keep'], vis)
    return leaks


def leak_summary(leaks):
    """instance_leaks as one line per instance: `instance: n declarations in k files (files…)`."""
    by = collections.defaultdict(lambda: (set(), set()))
    for item, k, i in leaks:
        by[i][0].add(item)
        by[i][1].add(k)
    out = []
    for i, (items, ks) in sorted(by.items(), key=lambda x: (-len(x[1][1]), x[0])):
        its = sorted(items)
        out.append('%s: %d declaration%s in %d file%s (%s%s)' % (
            i, len(ks), '' if len(ks) == 1 else 's', len(its), '' if len(its) == 1 else 's',
            ', '.join(its[:3]), ', …' if len(its) > 3 else ''))
    return out


def publish_order(plan, external=()):
    """The import DAG as waves: every item of a wave can publish concurrently once the earlier
    waves are published. Items: `bundle:NAME` (after the bundles it imports and the pieces of the
    statements it imports: a bundle may import only a Proved theorem), `statement:NODE` (after
    its bundles; none for `external` nodes, published by someone else), `piece:NODE` (after its
    own statement, the statements it imports and its bundles)."""
    deps = {}

    def proved_after(names):
        # a statement is Proved once its piece and, transitively, the pieces of the statements
        # that piece imports are accepted (an accepted reduction leaves it Open: Eilenberg–Ganea
        # OAIEGC001, 2026-10-25)
        out, todo = [], list(names)
        while todo:
            x = todo.pop()
            if x in out or x not in plan['pieces']:
                continue
            out.append(x)
            todo.extend(plan['pieces'][x].get('imports', ()))
        return sorted(out)
    for b in plan['bundles']:
        # a bundle may import a statement only once it is Proved
        deps['bundle:' + b['name']] = ['bundle:' + x for x in b['imports']] + \
            ['piece:' + x for x in proved_after(b.get('statements', ()))]
    for n, s in plan['stubs'].items():
        if n not in external:
            deps['statement:' + n] = ['bundle:' + x for x in s['bundles']]
    for n, p in plan['pieces'].items():
        d = ['bundle:' + x for x in p['bundles']] + \
            ['statement:' + x for x in p['imports'] if x not in external]
        if n not in external:
            d.append('statement:' + n)
        deps['piece:' + n] = d
    level, busy = {}, set()

    def lv(x):
        if x not in level:
            if x in busy:
                raise CarveError('publish order: %s depends on itself (an import cycle through %s)'
                                 % (x, ', '.join(sorted(busy))))
            busy.add(x)
            level[x] = 1 + max([lv(y) for y in deps[x]], default=-1)
            busy.discard(x)
        return level[x]
    for x in deps:
        lv(x)
    waves = [sorted(x for x in deps if level[x] == i) for i in range(max(level.values(), default=-1) + 1)]
    return {'deps': deps, 'waves': waves}


# ================================================================ carving

def _apply(text_bytes, base, edits):
    """text_bytes[base:...] with byte edits [(start, end, new)] (absolute offsets) applied."""
    out, cur = [], base
    for a, b, new in sorted(edits):
        if a < cur:
            continue                           # inside an earlier (larger) edit
        out += [text_bytes[cur:a], new.encode('utf-8')]
        cur = b
    return out, cur


def _attribute_list_end(t, a, b):
    """Byte offset just past the `]` closing the attribute list of the command in t[a:b] (b if none)."""
    i = t.find(b'[', a, b)
    if i < 0:
        return b
    depth = 0
    for j in range(i, b):
        ch = t[j:j + 1]
        if ch in b'([{':
            depth += 1
        elif ch in b')]}':
            depth -= 1
            if depth == 0:
                return j + 1
    return b


def _cmd_text(info, c, edits):
    t = info.text_bytes
    parts, cur = _apply(t, c.start.byte, edits)
    return (b''.join(parts) + t[cur:c.end.byte]).decode('utf-8')


def _skip_ws(t, b):
    while b < len(t) and t[b:b + 1] in (b' ', b'\t', b'\n'):
        b += 1
    return b


class Carver:
    """Cut declarations out of a development's modules, keeping the context they need.

    `carve(keep, have)`: the text of every module holding a kept node, each module its own
    `section`, in import order, with every declaration command not in `keep` removed by its Lean
    range. `have` is every public name the carved file declares or imports (bundle and
    statement imports): a project name outside it is gone, and the context commands are rewritten
    so that nothing names a gone declaration:
    * a `variable` binder group whose type names a gone declaration, or a binder of a dropped
      group, goes; the others stay (one multi-line command is one command);
    * `include`/`omit` lose dropped binders, and an `omit … in` head of a kept declaration that is
      left empty goes with all its lines;
    * an `attribute` command loses gone targets; a notation naming a gone declaration goes;
    * a namespace or section block left without a kept declaration goes whole, with its
      notations, attributes and `open`s;
    * `open X` where X now names no namespace goes (B007), and so does `export X (…)` (or the
      names it lists that are gone); where it would now also open a
      namespace the original module never saw (one from a module it did not import, emitted
      earlier in the file), it is pinned to what it meant: `open _root_.X`;
    * `example` and `#check`-style commands go; a kept `macro`/`syntax` command is refused.
    Options: `deprivatize` (bundles: drop `private`), `sorry` (stubs: these nodes' values become
    `by sorry`, doc comments dropped), `rename` ({env name: new short name}: the `_oai` rename
    and private collisions; declarations and the references Lean resolves to them)."""

    def __init__(self, g):
        self.g = g
        self.alive_pos = {}

    def carve(self, keep, have, deprivatize=False, sorry=(), rename=None, external=()):
        g = self.g
        self.external = set(external)
        self.pre = set()
        keep = set(keep)
        self.keep = keep
        have = set(have) | g.have_names(keep)
        self.keep_names = g.have_names(keep)
        # names for local instances emitted again in this file: unique to the file, since an
        # anonymous copy gets the same generated name in every file of one root (two stubs each
        # declaring `…instMeasurableSingletonClassFreeRow_theorems`, both imported by a piece)
        # and different in a statement (its `sorry` nodes) from the solution that keeps the same
        # declarations: the verifier compiles the solution and the statement in one file
        # (UniversalFInfinity Milnor.contractible: both declared `…_r461751_1`, "has already been
        # declared")
        import hashlib
        salt = '\nsorry:' + '\n'.join(sorted(sorry)) if sorry else ''
        self.tag = hashlib.sha1(('\n'.join(sorted(keep)) + salt).encode()).hexdigest()[:6]
        self.re_count = collections.Counter()
        rename = dict(rename or {})
        self.rename = rename
        self.sorry, self.deprivatize = set(sorry), deprivatize
        self._simp_in_file = None
        mods = g.topo({g.nodes[k].module for k in keep})
        kept_cmds = {m: {g.nodes[k].cmd for k in keep if g.nodes[k].module == m} for m in mods}
        # pass 1: what goes, per module (independent of namespaces)
        drops = {m: self._drops(m, kept_cmds[m], have) for m in mods}
        # namespaces the carved file has at each module: those of its imported names, then those
        # of the kept names and namespace commands of the modules emitted so far (an `open` may
        # only rely on a namespace that exists by then: Hecke 7/8 B001, `open
        # HeckeInverseAmplification` emitted before the later module that re-creates it)
        alive = set()
        for p in have - self.keep_names:
            alive.update(ns_prefixes(p))
        by_mod = collections.defaultdict(set)
        by_pos = collections.defaultdict(dict)           # module -> namespace -> first command making it
        for k in keep:
            for n in g.have_names([k]):
                m0 = g.nodes[k].module
                by_mod[m0].update(ns_prefixes(n))
                for x in ns_prefixes(n):
                    by_pos[m0][x] = min(by_pos[m0].get(x, g.nodes[k].cmd), g.nodes[k].cmd)
        out = []
        earlier = set()
        for m in mods:
            info = g.infos[m]
            before = set(alive)
            alive |= by_mod[m]
            pos = dict(by_pos[m])
            for c in info.commands:
                if c.short_kind == 'namespace' and c.index not in drops[m]:
                    full = join(c.namespace, leanedit.text(info, c.index).split()[1])
                    alive.update(ns_prefixes(full + '.x'))
                    for x in ns_prefixes(full + '.x'):
                        pos[x] = min(pos.get(x, c.index), c.index)
            # a namespace first made by a later command of this module is not there yet at an
            # `open` before it (PeriodicGroups BooleanCircuits, 2026-10-26: `open … Device.Formula`
            # kept in a bundle whose `namespace …Formula` command comes after it)
            self.alive_pos = {x: i for x, i in pos.items() if x not in before}
            sec = self._module(m, kept_cmds[m], drops[m], have, set(alive), deprivatize,
                               {g.nodes[k].cmd for k in sorry if g.nodes[k].module == m}, rename)
            # an instance with no name this file can write is skipped: `attribute [-instance] `
            # with nothing after it does not parse (Heisenberg 2026-10-25)
            hide = [h for h in self._unseen_instances(m, have, earlier, rename) if h and h.strip()]
            simps = [h for h in self._unseen_simps(m, have, earlier, rename) if h and h.strip()]
            if hide or simps:
                head = 'section\n-- module %s\n' % m
                sec = head + ('attribute [-instance] %s\n' % ' '.join(hide) if hide else '') + \
                    ('attribute [-simp] %s\n' % ' '.join(simps) if simps else '') + sec[len(head):]
            out.append(sec)
            earlier |= {k for k in keep if g.nodes[k].module == m}
        # reducibility of an external declaration, once at the top: the port's attribute is global
        return ''.join(sorted(self.pre)) + ''.join(out)

    def _unseen_instances(self, m, have, earlier, rename):
        """The global instances this file shows module m's section that m never saw (declared in a
        module m does not import), by the names this file knows them by: `attribute [-instance]`
        at the top of the section hides them again until its `end`, so type class search there
        takes the paths it took in the port (RationalHitting 2026-10-24: witnessCharZero of
        Generator.lean, visible in the carved list_hits through a bundle, changed how
        `algebraMap ℚ WitnessField` elaborated in Certificates.lean, and a `rwa` no longer matched).
        An instance from a later module of the file is not declared yet; one kept from an earlier
        module, or imported, is. Only instances whose type could match a problem of the section's
        declarations: it mentions a project declaration one of them uses, or only library types
        (`_could_match`; hiding every unseen instance cost PosteriorReplicas 19,889 names)."""
        g = self.g
        if not hasattr(g, '_global_insts'):
            g._global_insts = sorted(k for k in g.nodes if _global_instance(g, k))
        names = getattr(g, 'instance_names', None) or {}
        mine = [k for k in self.keep if g.nodes[k].module == m]
        out = []
        for i in g._global_insts:
            nd = g.nodes[i]
            if nd.module == m or g.sees(m, nd.module):
                continue
            if not any(_could_match(g, k, i) for k in mine):
                continue
            if i in self.keep:
                if i not in earlier:
                    continue
            elif not instance_imported(i, have, rename):
                continue
            if i in names:
                full = names[i]
            else:
                full = pubname(i)
                if i in rename:
                    full = full.rsplit('.', 1)[0] + '.' + rename[i] if '.' in full else rename[i]
            out.append('_root_.' + full)
        return out

    def _unseen_simps(self, m, have, earlier, rename):
        """The global `@[simp]` lemmas this file shows module m's section that m never saw (declared in
        a module m does not import), by the names this file knows them by: `attribute [-simp]` at the
        top of the section takes them out of the simp set until its `end`, as `_unseen_instances`
        does for instances (oaiq-081 SubexponentialSAT: `status_read` of a later module fired in
        modules that never imported it, `simp` closed goals early or left an opaque `status`, ~40
        post-carve patches). Only when a kept declaration of the section calls the default simp set
        (a stub: in its statement), and only lemmas whose statement mentions a project declaration
        one of them uses, or only library ones. Never a library lemma: only this carve's
        declarations, kept earlier in the file or imported from its bundles."""
        g = self.g
        if not hasattr(g, '_simp_lemmas'):
            g._simp_lemmas = sorted(k for k in g.nodes if _global_simp(g, k))
        info = g.infos[m]
        mine = []
        for k in self.keep:
            nd = g.nodes[k]
            if nd.module != m:
                continue
            c = info.commands[nd.cmd]
            end = c.value_start.byte if k in self.sorry and c.value_start else c.end.byte
            if _default_simp_call(strip(info.text_bytes[c.start.byte:end].decode('utf-8', 'replace'))):
                mine.append(k)
        if not mine:
            return []
        if self._simp_in_file is None:
            # the simp lemmas this file has at all: kept, or imported
            self._simp_in_file = [i for i in g._simp_lemmas
                                  if (i in self.keep and not (g.nodes[i].private and not self.deprivatize))
                                  or (i not in self.keep and instance_imported(i, have, rename))]
        uses = set().union(*(g.nodes[k].deps | g.nodes[k].sig for k in mine))
        out = []
        for i in self._simp_in_file:
            nd = g.nodes[i]
            if nd.module == m or g.sees(m, nd.module) or (i in self.keep and i not in earlier):
                continue
            td = nd.tdeps - {i}
            if td and not td & uses:
                continue
            full = pubname(i)
            if i in rename:
                full = full.rsplit('.', 1)[0] + '.' + rename[i] if '.' in full else rename[i]
            out.append('_root_.' + full)
        return out

    # ---------------------------------------------------------- what goes
    def _gone(self, tok, c, m, have, opens, bound=(), idn=None):
        """Does identifier tok, read in command c's scope, need a project declaration the carved
        file does not have? With `idn` (its LeanInfo identifier) and the elaborated port's record
        of it, exactly: some project constant Lean resolved inside the token (a field included:
        `S.big` with `S` a variable needs Space.big) is gone. Without a record, the text-based
        reading: every project declaration it may name is gone; no guessing for fields of locals
        then (guessing dropped needed binders: Erdős 3 v2 B107, B167, B248)."""
        g = self.g
        if idn is not None:
            r = g.reading(g.infos[m], c, idn)
            if r is not None:
                return any(g.is_project(n) and pubname(n) not in have for n in r.consts)
        if tok.split('.')[0] in bound:
            return False
        hits = g.resolve_lean(tok, c.namespace, opens, m)
        if hits and idn is not None:
            g.note_fallback(g.infos[m], c, idn)
        return bool(hits) and all(pubname(h) not in have for h in hits)

    def _external_ref(self, idn, c, m):
        """The name of the external (published bundle) declaration the identifier resolves to, or None."""
        r = self.g.reading(self.g.infos[m], c, idn)
        for n in (r.consts if r is not None else ()):
            if pubname(n) in self.external:
                return pubname(n)
        return None

    def _drops(self, m, kept, have):
        g, info = self.g, self.g.infos[m]
        drop = set()
        for c in info.commands:
            if _is_decl_command(c) and c.index not in kept:
                drop.add(c.index)
            elif c.short_kind in DIAGNOSTIC or c.decl_kind == 'example':
                drop.add(c.index)
            elif (m, c.index) in g._scoped_cmds and c.index not in kept:
                drop.add(c.index)                        # it lives in its own node's file only
        # notations and attributes that name gone declarations
        keep_global = set()
        for c in info.commands:
            if c.index in drop:
                continue
            if c.short_kind in NOTATION or c.short_kind == 'attribute':
                opens = g.scope_opens(info, c, m)
                refs = [i for i in c.idents or [] if i['role'] == 'ref']
                bound = g.scope_vars(info, c) if c.short_kind in NOTATION else ()
                gone = [i for i in refs if self._gone(i['name'], c, m, have, opens, bound, idn=i)]
                if c.short_kind in NOTATION and gone:
                    drop.add(c.index)
                elif c.short_kind == 'attribute' and refs and len(gone) == len(refs):
                    drop.add(c.index)
                elif not _is_local(leanedit.text(info, c.index)):
                    keep_global.add(c.index)
            elif c.short_kind == 'export' and self._export_alive(info, c, m, have):
                # an export makes aliases that outlive its block (`namespace PA / export
                # PolynomialAlgorithm (denote) / end PA`): with a name it exports still here, the
                # block stays, though it holds no declaration (oaiq-081: the piece's `PA.denote`)
                keep_global.add(c.index)
        # a local notation nothing kept in its scope uses goes: kept, it would keep the variables
        # it names (Erdős 3 v2 stub: `local notation "hamin" => … B` kept `variable (B :
        # LayerSamplerAxis I n → Type*)`), or name variables already gone (B169 "Unknown
        # identifier `active` at quotation precheck"). Comments do not count as uses; last first, so
        # chains resolve.
        for c in reversed(info.commands):
            if c.index in drop or c.short_kind not in NOTATION:
                continue
            txt = leanedit.text(info, c.index)
            if not re.match(r'\s*(?:/--.*?-/\s*)?(?:@\[[^\]]*\]\s*)?local\b', txt, re.S):
                continue
            toks = _notation_tokens(txt)
            if not toks:
                continue
            # a local instance counts even when dropped: the file may re-emit it for a kept
            # declaration in its scope (Erdős 3 v2: `local instance … : NeZero Ncrt` came back,
            # `local notation "Ncrt"` had gone)
            # by Lean's record (the command's syntax contains the notation's kind) or by its text
            kinds = set(c.declares_kinds or ())
            used = any((c2.index not in drop or _local_instance(info, c2)[0]) and
                       _in_scope(info, c.index, c2) and
                       (bool(kinds & set(c2.kinds_used or ())) or
                        any(_uses_token(strip(info.slice(*info.command_span(c2.index))), tk) for tk in toks))
                       for c2 in info.commands[c.index + 1:])
            if not used:
                drop.add(c.index)
                keep_global.discard(c.index)
        # a `variable` (or `include`/`omit`) with no kept declaration after it in its scope serves
        # nothing, and a `variable` may not
        # even elaborate: its binders can need instances only the left-out declarations brought in
        # (Erdős 3 v2 B038: a trailing `variable [∀ j, IsZLattice …]`, DiscreteTopology missing)
        # So does a local notation: kept for a local instance using it that is never emitted again
        # (nothing kept follows), it would name the variables just dropped (UniversalFInfinity
        # B005: `local notation "hf" => (Fact.out : Function.Injective f)`, "Unknown identifier
        # `f` at quotation precheck")
        decls = [c2 for c2 in info.commands if c2.index in kept]
        for c in info.commands:
            if c.index in drop:
                continue
            ctx = c.short_kind in ('variable', 'include', 'omit') or (
                c.short_kind in NOTATION and
                re.match(r'\s*(?:/--.*?-/\s*)?(?:@\[[^\]]*\]\s*)?local\b', leanedit.text(info, c.index), re.S))
            if ctx and not any(_in_scope(info, c.index, c2) for c2 in decls):
                drop.add(c.index)
                keep_global.discard(c.index)
        # blocks left without a kept declaration (or a global notation/attribute) go whole
        blocks = collections.defaultdict(set)
        for c in info.commands:
            for o, _ in c.context:
                if o is not None:
                    blocks[o].add(c.index)
        for o, members in blocks.items():
            members = members | {o}
            if not (members & (kept | keep_global)):
                drop |= members
        return drop

    # ---------------------------------------------------------- one module
    def _module(self, m, kept, drop, have, alive, deprivatize, sorry, rename):
        g, info = self.g, self.g.infos[m]
        keep_names = self.keep_names
        t = info.text_bytes
        reps = {}
        drop = set(drop)
        dropped_vars = set()
        # binder names kept notations use: their groups stay
        protect = collections.defaultdict(set)
        for c in info.commands:
            if c.index in drop or c.short_kind not in NOTATION:
                continue
            heads = {i['name'].split('.')[0] for i in c.idents or [] if i['role'] == 'ref'}
            for _, cs in c.context:
                for vi in cs:
                    vc = info.commands[vi]
                    if vc.short_kind == 'variable':
                        for grp in vc.binders or []:
                            if set(grp['names']) & heads:
                                protect[vi].update(grp['names'])
        # tokens of the notations this file drops: a `variable` group written with one has lost
        # its meaning (Hecke 7/8 stub ProbeEuler.pow_mul_sqrt: `variable (p : O)` kept after
        # `local notation "O" => ActualEisensteinCubic.O` went with its target)
        dead_tok = {c.index: _notation_tokens(leanedit.text(info, c.index)) for c in info.commands
                    if c.index in drop and c.short_kind in NOTATION}
        inst_names = getattr(g, 'instance_names', None) or {}
        reactivated, local_attrs = set(), set()
        for c in info.commands:
            if c.index in drop:
                continue
            edits = []
            opens = g.scope_opens(info, c, m)
            k = c.short_kind
            if k == 'variable':
                toks = set().union(*[v for vi, v in dead_tok.items() if _in_scope(info, vi, c)]) \
                    if dead_tok else set()
                r = self._variable(info, c, m, have, opens, dropped_vars, protect.get(c.index, set()),
                                   toks, self._pin_edits(info, c, m, have, opens, c.end.byte, set()))
                if r is None:
                    drop.add(c.index)
                    continue
                # local instances its binders may need come back before it, not only before the
                # next declaration (Erdős 3 v2: `variable (hread : … W.cover …)` after
                # `local instance … : NeZero W.cover`; cut by the repair, the statement lost it)
                pre = self._reactivate(info, c, m, drop, reactivated, inst_names, have)
                if r is not False or pre:
                    reps[c.index] = pre + (r if r is not False else leanedit.text(info, c.index))
                continue
            if k in ('include', 'omit'):
                ids = [i for i in c.idents or [] if i['role'] in ('ref', 'binder')]
                bad = [i for i in ids if i['name'] in dropped_vars or
                       self._gone(i['name'], c, m, have, opens, idn=i)]
                if bad and len(bad) == len(ids):
                    drop.add(c.index)
                elif bad:
                    reps[c.index] = _cmd_text(info, c, [(i['start'], _skip_ws(t, i['end']), '') for i in bad])
                continue
            if k == 'attribute':
                txt = leanedit.text(info, c.index)
                refs = [i for i in c.idents or [] if i['role'] == 'ref']
                gone = [i for i in refs if self._gone(i['name'], c, m, have, opens, idn=i)]
                ents = attribute_entries(txt) if restricted_attribute(txt) or generating_attribute(txt) else None
                if gone and len(gone) == len(refs):
                    drop.add(c.index)
                elif ents is not None:
                    # the targets: the identifiers after the attribute list (`reassoc (attr := simp)`
                    # names `simp` inside it)
                    lend = _attribute_list_end(t, c.start.byte, c.end.byte)
                    refs = [i for i in refs if i['start'] >= lend]
                    # attributes Lean lets only the declaring file set: the command is in its
                    # target's module (the port compiled), so the bundle that declares the target
                    # carries it, persistently; this file keeps it only for its own declarations
                    # (Kirchberg–Rørdam: a piece re-emitted `attribute [instance_reducible]
                    # PauliData.finite`, a bundle's declaration). The other attributes of the
                    # command stay on every target the file has.
                    mine = [i for i in refs if i not in gone and not self._gone(i['name'], c, m, keep_names, opens, idn=i)]
                    ren_edits = self._rename_edits(info, c, m, opens, rename)

                    def tok(i):
                        mine_e = [e for e in ren_edits if i['start'] <= e[0] < i['end']]
                        parts, cur = _apply(t, i['start'], mine_e)
                        return (b''.join(parts) + t[cur:i['end']]).decode('utf-8')
                    names = lambda L: ' '.join(tok(i) for i in L)
                    rest = [e for e in ents if not restricted_attribute('attribute [%s] x' % e)
                            and not generating_attribute('attribute [%s] x' % e)]
                    res = [e for e in ents if e not in rest and restricted_attribute('attribute [%s] x' % e)]
                    # a declaring attribute on a target of this module: the file declaring the target
                    # applies it (its constants travel with the target's node); on a target of
                    # another module (or the library) the command itself is the only application
                    gen = [e for e in ents if e not in rest and e not in res]
                    mine_gen = mine + [i for i in refs if i not in gone and i not in mine and
                                       m not in self._ref_modules(i, c, m)]
                    # a declaration of someone else's published bundle (external_defs) is carried by
                    # no bundle of this carve, and Lean lets only its own file set the attribute
                    # globally: keep it here, `local` (reducibility needs allowUnsafeReducibility)
                    # (Coboundary: `attribute [reducible] Face`, Face in Def_CoboundaryExpanders)
                    theirs = [self._external_ref(i, c, m) for i in refs
                              if i not in gone and i not in mine]
                    out = []
                    for full in [x for x in theirs if x]:
                        for e in res:
                            kw = e.split()[0]
                            if kw in ('reducible', 'irreducible', 'semireducible'):
                                self.pre.add('set_option allowUnsafeReducibility true in\n'
                                             'attribute [local %s] _root_.%s\n' % (e, full))
                            elif kw == 'instance_reducible':
                                self.pre.add('attribute [local %s] _root_.%s\n' % (e, full))
                    if rest and refs and len(gone) < len(refs):
                        out.append('attribute [%s] %s' % (', '.join(rest), names([i for i in refs if i not in gone])))
                    if mine and res:
                        out.append('attribute [%s] %s' % (', '.join(res), names(mine)))
                    if mine_gen and gen:
                        out.append('attribute [%s] %s' % (', '.join(gen), names(mine_gen)))
                    if out:
                        reps[c.index] = '\n'.join(out)
                    else:
                        drop.add(c.index)
                elif gone:
                    new_txt = _cmd_text(info, c, [(i['start'], _skip_ws(t, i['end']), '') for i in gone] +
                                        self._rename_edits(info, c, m, opens, rename))
                    # `attribute [-simp] a b` whose targets are all gone, though `simp` itself is a
                    # reference that stays: nothing left to apply it to (PeriodicGroups, 2026-10-26)
                    if re.fullmatch(r'\s*(?:local\s+|scoped\s+)?attribute\s*\[[^\]]*\]\s*', new_txt):
                        drop.add(c.index)
                    else:
                        reps[c.index] = new_txt
                else:
                    # a renamed target (a collided private declaration, a duplicate's renamed copy,
                    # the `_oai` target) is named by its new name
                    ren_edits = self._rename_edits(info, c, m, opens, rename)
                    if ren_edits:
                        reps[c.index] = _cmd_text(info, c, ren_edits)
                continue
            if k == 'open':
                r = self._open(info, c, m, alive, (c.start.byte, c.end.byte))
                if r is None:
                    drop.add(c.index)
                    continue
                r = list(r) + self._hiding_edits(info, c, m, have)
                if r:
                    txt = _cmd_text(info, c, r)
                    # `open X hiding` left with no names, `open X ()` left empty (Hecke 7/8 B000:
                    # `open SecondPassArithmetic hiding O` once its `O` was carved away)
                    txt = re.sub(r'\s+hiding\s*$', '', txt.rstrip())
                    if re.search(r'\(\s*\)\s*$', txt):
                        drop.add(c.index)
                    else:
                        reps[c.index] = txt
                continue
            if k == 'export':
                r = self._export(info, c, m, have, alive, opens)
                if r is None:
                    drop.add(c.index)
                elif r:
                    reps[c.index] = _cmd_text(info, c, r)
                continue
            if k in REFUSED or (c.heads and any(_head_kind(h) in REFUSED for h in c.heads)):
                raise CarveError('%s keeps a `%s` command (line %d), which prove2.me refuses: no '
                                 'macro or syntax commands' % (m, k, c.start.line))
            pre = ''
            if c.index in kept:
                edits += self._decl_edits(info, c, m, have, alive, opens, dropped_vars,
                                          deprivatize, c.index in sorry, rename)
                at = _anonymous_instance(info, c)
                key = g.cmd_node.get((m, c.index))
                if at is not None and key:
                    # name an anonymous instance as the port named it: Lean's generated name
                    # depends on the file and on what it imports, so a carved file's could
                    # collide with a name kept from the port (Hecke 7/8: `instance : Countable O`
                    # auto-named instCountableO in a bundle, a piece keeping the port's
                    # `local instance instCountableO`), and a consumer re-activates a local one
                    # by name
                    # (a private one under its collision rename: deprivatized in a bundle, two
                    # modules' `private instance : Countable O` share one public name)
                    edits.append((at, at, ' ' + rename.get(key, pubname(key).rsplit('.', 1)[-1])))
                pre = self._reactivate(info, c, m, drop, reactivated, inst_names, have, c.index in sorry)
                pre += self._local_attrs(info, c, m, drop, local_attrs, have, c.index in sorry)
            elif c.short_kind in NOTATION:
                edits += self._rename_edits(info, c, m, opens, rename)
            if edits or pre:
                reps[c.index] = pre + _cmd_text(info, c, edits)
        first = info.commands[0].start.byte if info.commands else 0
        body = leanedit.remove_commands(info, drop, a=first, reps=reps)
        closers = []
        last = info.commands[-1] if info.commands else None
        if last is not None:
            open_at_end = [o for o, _ in last.context if o is not None]
            if last.short_kind in OPENERS:
                open_at_end.append(last.index)
            closers = [leanedit.closer(info, o) for o in reversed(open_at_end) if o not in drop]
        body = body.strip('\n')
        return ('section\n-- module %s\n' % m + (body + '\n' if body else '') +
                ''.join(x + '\n' for x in closers) + 'end\n\n')

    def _ref_modules(self, idn, c, m):
        """The modules of the project declarations identifier idn of command c resolves to."""
        g = self.g
        r = g.reading(g.infos[m], c, idn)
        return {g.nodes[g.owner[n]].module for n in (r.consts if r is not None else ())
                if g.is_project(n) and g.owner.get(n) in g.nodes}

    def _used_instances(self, info, c, m, sorried):
        """The instances kept command c's elaboration used (LeanInfo `insts`, which sees instance
        search in every term the elaborator recorded, plus the instances its compiled constants
        name); for a statement stub (`sorried`) only its statement's. None when the port has no
        record of c (then every local instance in scope counts, as before the record existed)."""
        if c.insts is None:
            return None
        used = set(c.sig_insts if sorried else c.insts)
        # the class keys of what it uses ('Fact LT.lt'): Lean may have shared an equal proof that
        # another module declared instead of naming the local instance instance search found
        # (Problem340, MapSignal's input_eq_baseInput_of_mem_Ico)
        used |= {'key:' + x for x in ((c.sig_used_keys if sorried else c.used_keys) or ())}
        k = self.g.cmd_node.get((m, c.index))
        if k:
            for n in self.g.nodes[k].names:
                x = self.g.consts.get(n) or {}
                used.update(x.get('t', ()))
                if not sorried:
                    used.update(x.get('v', ()))
        return used

    def _reactivate(self, info, c, m, drop, done, inst_names, have, sorried=False, chain=None):
        """The local instances in force at kept command c in its module that this file does not
        declare and c's elaboration used, put back in force. Their use can be invisible in the
        declaration graph (Hecke 7/8 AmplificationAllocationCost: `local instance : DecidableEq
        (ι ⊕ Fin 2) := Classical.decEq _` won instance synthesis, but the elaborated term kept the
        defeq instance it was checked against, so the theorem's constants never name it): the
        elaborated port's record says which (`_used_instances`); without one, every one in scope
        counts:
        - imported (a bundle carries it as a plain constant): `attribute [local instance] N`
          (FiniteRayExpansion's `Fintype (MulChar R ℂ)` in B002); inst_names maps a port name to
          the name Lean gave it in a published bundle that kept it anonymous;
        - not imported, or nobody's node (its generated name taken by another module's): its
          command again, under a name unique to this file, after the earlier local instances its
          own elaboration used (the same rules, recursively: Lech oaiq-032, a re-emitted
          `baseAlgebra_r…` came before the `concreteRing` its statement needs).
        A local instance on the same type (argument heads) as one c used, or of the same class,
        comes back with it (`_sibling_used`), and so does one whose type mentions a declaration c
        uses (`_carrier_used`), unless a kept instance of its class between it and c would then
        lose to it (`_overtakes`). `chain`: the scope the emitted text lands in (c's, or the kept
        command's when re-emitting what a re-emitted instance needs)."""
        g = self.g
        if chain is None:
            chain = tuple(o for o, _ in c.context)
        out = []
        used = self._used_instances(info, c, m, sorried)
        for vi in sorted(drop):
            if vi >= c.index or (vi, chain) in done or not _in_scope(info, vi, c):
                continue
            vc = info.commands[vi]
            is_inst, anon_at = _local_instance(info, vc)
            sibling = False
            if is_inst and used is not None:
                ik0 = g.cmd_node.get((m, vi))
                names = {x[0] for x in vc.declares or ()} or set(g.nodes[ik0].names if ik0 else ())
                keys = {'key:' + ' '.join([x[1]] + list(x[2])) for x in vc.declares or () if x[1]}
                if not (names | keys) & used and not (not sorried and _could_answer(vc, c)):
                    if not (self._sibling_used(info, vc, c, used) or
                            self._carrier_used(info, vc, c, m, sorried) or
                            self._library_coercion(vc, ik0)) or \
                            self._overtakes(info, vc, c, drop):
                        continue
                    sibling = True
            # ik None: a local instance that is nobody's node. An instance of a Prop class is a
            # theorem, and Lean lets sibling modules declare the same one under one generated name
            # (Problem340 2026-10-24: `local instance : Fact ((0 : ℝ) < 100)` in 28 modules, 13
            # constants); the declaration graph keeps one per name, so this command is carved like
            # one that is not imported: emitted again
            ik = g.cmd_node.get((m, vi))
            # declared by this file: by its own node, not by another module's collided copy under
            # the same public name (Lech oaiq-032: the kept concreteRing of one module stood in for
            # the imported one of another, so it never came back)
            if not is_inst or (ik and instance_imported(ik, self.keep_names, self.rename)):
                continue
            done.add((vi, chain))
            if ik and instance_imported(ik, have, self.rename):
                # at the source's priority: `attribute [local instance 2000] other` of the module
                # must not win over a `(priority := 3000)` one (Auslander–Reiten oaiq-031)
                prio = _instance_priority(info.text_bytes[vc.start.byte:vc.end.byte])
                out.append('attribute [local instance%s] %s\n' % (' ' + prio if prio else '',
                                                                 instance_ref(ik, inst_names, self.rename)))
                continue
            # not imported: its command again under a name unique to this file, anonymous or
            # named (Erdős 3 v2: `local instance forecastModulusNeZero (Pr) (A) : NeZero …`, which
            # makes `ZMod (∏ …)` finite in a statement's binders, was named and so left out)
            decl = next((i for i in vc.idents or [] if i['role'] == 'decl'), None)
            if anon_at is None and decl is None:
                continue
            opens = g.scope_opens(info, vc, m)
            refs = [i for i in vc.idents or [] if i['role'] == 'ref']
            if any(self._gone(i['name'], vc, m, have, opens, idn=i) for i in refs):
                if used is not None and not sibling:
                    # used, but it names what this file lacks: the plan should have kept it
                    g.lost_instances.append((m, vc.start.line, c.start.line))
                continue
            # the earlier local instances its own elaboration used, first
            out.append(self._reactivate(info, vc, m, drop, done, inst_names, have, chain=chain))
            short = pubname(ik).rsplit('.', 1)[-1] if ik else \
                (decl['name'].rsplit('.', 1)[-1] if decl else 'localInst')
            self.re_count[short] += 1
            name = '%s_r%s_%d' % (short, self.tag, self.re_count[short])
            edit = (anon_at, anon_at, ' ' + name) if anon_at is not None else (decl['start'], decl['end'], name)
            out.append(_cmd_text(info, vc, [edit]).strip() + '\n')
        return ''.join(out)

    def _library_coercion(self, vc, ik):
        """Is local instance vc a coercion between types that mention no project declaration
        (`Coe (E → ℝ) (E → ℂ)`)? Its use unfolds to a lambda and leaves no constant, no instance
        problem and no carrier to match (oaiq-096, the PNT module `Wiener`: "Application type
        mismatch ℕ → ℝ vs ℕ → ℂ" in the piece), so it comes back for every kept declaration in its
        scope, as it was in force there in the port. One over project types comes back by
        `_carrier_used`."""
        decl = [x for x in vc.declares or () if x[1]]
        if not decl or not any(x[1] in COERCION_CLASSES for x in decl):
            return False
        g = self.g
        if any(h in g.owner for x in decl for h in x[2] or ()):
            return False
        if ik and ik in g.nodes:
            classes = {x[1] for x in decl}
            if any(d in g.nodes and not g.nodes[d].instance and d not in classes
                   for d in g.nodes[ik].tdeps - {ik}):
                return False
        return True

    def _local_attrs(self, info, c, m, drop, done, have, sorried=False):
        """`attribute [local X] N` before kept command c, for each declaration N of its module with a
        `@[local X]` attribute in force at c that this file imports rather than declares: a local
        attribute does not travel with the declaration into the bundle that holds it (oaiq-096:
        `@[local gcongr] theorem norm_lt_norm_of_nonneg` in a bundle, `gcongr` in the piece "did not
        make progress"). Only when c's text uses the attribute (`simp` by a default simp call, any
        other by its name; `instance` always)."""
        g = self.g
        chain = tuple(o for o, _ in c.context)
        end = c.value_start.byte if sorried and c.value_start else c.end.byte
        text = strip(info.text_bytes[c.start.byte:end].decode('utf-8', 'replace'))
        out = []
        for vi in sorted(drop):
            if vi >= c.index or (vi, chain) in done or not _in_scope(info, vi, c):
                continue
            vc = info.commands[vi]
            locs = [a.split(None, 1)[1].strip() for a in vc.attrs or ()
                    if a.split() and a.split()[0] == 'local' and len(a.split()) > 1]
            if not locs or not _is_decl_command(vc) or vc.short_kind == 'attribute':
                continue
            k = g.cmd_node.get((m, vi))
            if not k or k in self.keep or not instance_imported(k, have, self.rename):
                continue
            want = [x for x in locs if x.split()[0] == 'instance' or
                    (x.split()[0] == 'simp' and _default_simp_call(text)) or
                    _uses_token(text, x.split()[0]) or _uses_token(text, pubname(k).rsplit('.', 1)[-1])]
            if want:
                done.add((vi, chain))
                out.append('attribute [local %s] _root_.%s\n' % (', local '.join(want),
                                                                instance_ref(k, {}, self.rename)))
        return ''.join(out)

    def _sibling_used(self, info, vc, c, used):
        """Did command c use another local instance of its module, in scope at c, of another class
        on the same carrier as local instance vc (a type among the argument heads of both, LeanInfo
        `declares`), or of vc's own class? Then vc comes back too: both were in force in the port,
        and a use of vc can leave no record (Thomason oaiq-043: `local instance : Fintype
        (OrdinalVertices n)` beside the kept `LinearOrder` one on that synonym; partialLastVertex
        needed it, though neither its constants, `insts` nor `inst_keys` show a Fintype problem;
        Auslander–Reiten oaiq-031: the Prop partner `IsScalarTower k A M` of a used `Module k M`,
        whose heads list A and the instances too, never named by a term, "failed to synthesize
        SMulCommClass k R …"; SharpRamsey oaiq-060: `BDE : DecidableEq (Fin w × Bool)` beside the
        used `IDE : DecidableEq (Slots w n)` and `TDE`, all `Classical.decEq _`, BDE's use replaced
        by a defeq instance in the statement's term, which then failed "synthesized type class
        instance is not definitionally equal"). Same-class siblings come back in their source
        order, so the one that won in the port still wins (`_overtakes` guards a kept one)."""
        classes = {x[1] for x in vc.declares or () if x[1]}
        if not classes:
            return False
        heads = {h for x in vc.declares or () if x[1] for h in x[2]}
        mine = self._carriers(info, heads)
        for c2 in info.commands[:c.index]:
            if c2.index == vc.index or not _in_scope(info, c2.index, c) or \
                    not _local_instance(info, c2)[0]:
                continue
            for x in c2.declares or ():
                if not x[1]:
                    continue
                # vc is stated over c2 (its class takes c2 as an argument: `StarOrderedRing (A i)` over
                # the `PartialOrder (A i)` instance normEntryOrder) and c2 comes back, by name or by its
                # class key: c2 then wins instance search, and only vc agrees with it (NuclearUltrapower
                # oaiq-123: the carrier `A i` is a bound variable, so no carrier matched; "failed to
                # synthesize" at a CStarMatrix instance)
                if x[0] in heads and ('key:' + ' '.join([x[1]] + list(x[2])) in used or x[0] in used):
                    return True
                if x[0] not in used:
                    continue
                if x[1] in classes or (mine and mine & self._carriers(info, x[2])):
                    return True
        return False

    def _carrier_used(self, info, vc, c, m, sorried):
        """Does local instance vc's type mention a project declaration (not its class) that kept
        command c uses (a stub: its statement)? Then vc comes back: it was in force there in the
        port, and its use can leave no instance constant (SimpleOvergroups oaiq-066: a `CoeFun` on
        `FunctionalTree.diagonalRep`, unfolded by coercion elaboration, "Function expected at
        ↑(diagonalRep A)"; `Primcodable (Symbols k i)` on an abbrev, whose problem the record shows
        as `Encodable (Source.Symbols …)`; Thomason oaiq-043 the same)."""
        g = self.g
        k = g.cmd_node.get((m, c.index))
        ik = g.cmd_node.get((m, vc.index))
        if not k or not ik:
            return False
        classes = {x[1] for x in vc.declares or () if x[1]}
        mention = {x for x in g.nodes[ik].tdeps - {ik} - classes
                   if x in g.nodes and not g.nodes[x].instance and not g.is_local_instance(x)}
        nd = g.nodes[k]
        return bool(mention & (nd.sig if sorried else nd.deps | nd.sig))

    @staticmethod
    def _overtakes(info, vc, c, drop):
        """Would local instance vc, put back in force just before c, take priority over a kept
        instance of its class that the port declared after it (and so preferred)?"""
        classes = {x[1] for x in vc.declares or () if x[1]}
        for c2 in info.commands[vc.index + 1:c.index]:
            if c2.index not in drop and any(x[1] in classes for x in c2.declares or ()):
                return True
        return False

    def _carriers(self, info, heads):
        """The heads of an instance's conclusion that are types, not instances (`TensorProduct.instSMul`,
        `SMulZeroClass.toSMul`, an instance of the project)."""
        cache = self.__dict__.setdefault('_inst_names_cache', {})
        insts = cache.get(id(info))
        if insts is None:
            insts = cache[id(info)] = {x[0] for c in info.commands for x in c.declares or () if x[1]}
        return {h for h in heads if h not in insts and not (self.g.consts.get(h) or {}).get('i') and
                not re.match(r"(?:inst|to[A-Z])", h.rsplit('.', 1)[-1])}

    def _variable(self, info, c, m, have, opens, dropped_vars, protected, dead_tokens=(), pins=None):
        """The `variable` command without its gone binder groups: False (unchanged), None (none
        left) or the new text."""
        groups = c.binders or []
        bound = {n for grp in groups for n in grp['names']}
        refs = [i for i in c.idents or [] if i['role'] == 'ref']
        bad, changed = set(), True
        while changed:
            changed = False
            lost_all = {n for j in bad for n in groups[j]['names']} | dropped_vars
            for j, grp in enumerate(groups):
                if j in bad or set(grp['names']) & protected:
                    continue
                # a name an earlier kept group of this command binds again is that new variable,
                # not the dropped one (KL invariance 2026-10-26: `{B : Type ub} [CommRing B]
                # (e : A ≃ₐ[k] B)` after an earlier `{A B : Type ua}` whose B was dropped)
                lost = lost_all - {n for i in range(j) if i not in bad for n in groups[i]['names']}
                # a token right after `.` is a field (`(e a).Bounds`): read only as Lean resolved
                # it, never by its text
                inside = [i for i in refs if grp['start'] <= i['start'] < grp['end'] and
                          (not is_field(info, i) or self.g.reading(info, c, i) is not None)]
                gtxt = info.text_bytes[grp['start']:grp['end']].decode('utf-8')
                if any(_uses_token(gtxt, tk) for tk in dead_tokens) or any(i['name'].split('.')[0] in lost - set(grp['names']) or
                       self._gone(i['name'], c, m, have, opens, bound - lost, idn=i) for i in inside):
                    bad.add(j)
                    changed = True
        # a name bound again here is a new variable, not the dropped one
        dropped_vars.difference_update(n for j, grp in enumerate(groups) if j not in bad
                                       for n in grp['names'])
        pins = pins or []
        if not bad and not pins:
            return False
        dropped_vars.update(n for j in bad for n in groups[j]['names'])
        if len(bad) == len(groups):
            return None
        t = info.text_bytes

        def grp_text(grp):
            mine = sorted(e for e in pins if grp['start'] <= e[0] < grp['end'])
            parts, cur = _apply(t, grp['start'], mine)
            return (b''.join(parts) + t[cur:grp['end']]).decode('utf-8')
        return 'variable ' + ('\n  ').join(grp_text(grp) for j, grp in enumerate(groups) if j not in bad)

    def _open(self, info, c, m, alive, span):
        """Edits for the namespace tokens of an `open` in [span): [] unchanged, None when nothing
        is left to open."""
        g = self.g
        toks = [i for i in c.idents or [] if i['role'] == 'open' and span[0] <= i['start'] < span[1]]
        special = any(i['role'] == 'hiding' and span[0] <= i['start'] < span[1] for i in c.idents or [])
        edits, dead = [], 0
        # Lean reads an `open` token relative to the current namespaces and to every namespace
        # already open, including those the same command opened before it (Kaplansky 2026-10-18:
        # `open _root_.SimpleGraph _root_.OAI.SimpleGraph Walk` also opened SimpleGraph.Walk)
        prior = list(g.scope_opens(info, c, m))
        for i in toks:
            tok = i['name']
            cands = [tok[len('_root_.'):]] if tok.startswith('_root_.') else \
                list(dict.fromkeys([join(p, tok) for p in prefixes(c.namespace)] +
                                   [join(o, tok) for o in prior]))
            prior += cands      # unknown readings only add candidates no namespace matches
            known = [x for x in cands if x in g.proj_ns or x in g.ext_ns]
            if not known:
                continue                      # Mathlib's, say: carving cannot change it
            now = [x for x in cands if x in g.ext_ns or (x in alive and self.alive_pos.get(x, -1) < c.index)]
            orig = [x for x in cands if x in g.ext_ns or g.ns_existed(x, m, before=c.index)]
            if not now:
                dead += 1
                edits.append((i['start'], _skip_ws(info.text_bytes, i['end']), ''))
                continue
            # a reading the original did not take is a project namespace somewhere: say which one
            # is meant, since a statement is appended to its solution by the verifier and may land
            # after that namespace (Erdős 3 v2: `open MvPolynomial` read as
            # OAI.Erdos3.MvPolynomial, "Unknown identifier `eval`")
            shadow = not tok.startswith('_root_.') and any(x in g.proj_ns and x not in orig for x in cands)
            if any(x not in orig for x in now) or shadow:
                meant = [x for x in now if x in orig]
                if not meant:
                    dead += 1
                    edits.append((i['start'], _skip_ws(info.text_bytes, i['end']), ''))
                else:
                    edits.append((i['start'], i['end'], ' '.join('_root_.' + x for x in meant)))
        if toks and (dead == len(toks) or (special and dead)):
            return None
        return edits

    def _export(self, info, c, m, have, alive, opens):
        """Edits for `export X (a b)`: None (drop it) when X is a project namespace the file does
        not have, or none of the names it exports is left; else the names gone removed
        (RationalHitting 2026-10-24: `export Coding (code)` in a bundle without the class
        Coding, "unknown namespace `Coding`")."""
        g, t = self.g, info.text_bytes
        refs = [i for i in c.idents or [] if i['role'] == 'ref']
        if not refs:
            return []
        tok = refs[0]['name']
        cands = [tok[len('_root_.'):]] if tok.startswith('_root_.') else \
            list(dict.fromkeys([join(p, tok) for p in prefixes(c.namespace)] + [join(o, tok) for o in opens]))
        if not any(x in g.proj_ns or x in g.ext_ns for x in cands):
            return []                         # Mathlib's: carving cannot change it
        now = [x for x in cands if x in g.ext_ns or (x in alive and self.alive_pos.get(x, -1) < c.index)]
        if not now:
            return None
        gone = []
        for i in refs[1:]:
            proj = [n for x in now for n in g.pub.get(join(x, i['name']), ())]
            if proj and all(pubname(n) not in have for n in proj):
                gone.append(i)
        if gone and len(gone) == len(refs) - 1:
            return None
        return [(i['start'], _skip_ws(t, i['end']), '') for i in gone]

    def _export_alive(self, info, c, m, have):
        """Does `export X (a b)` still export something the carved file has (or a library name)?"""
        g = self.g
        refs = [i for i in c.idents or [] if i['role'] == 'ref']
        if len(refs) < 2:
            return bool(refs)
        tok = refs[0]['name']
        opens = g.scope_opens(info, c, m)
        cands = [tok[len('_root_.'):]] if tok.startswith('_root_.') else \
            list(dict.fromkeys([join(p, tok) for p in prefixes(c.namespace)] + [join(o, tok) for o in opens]))
        for i in refs[1:]:
            proj = [n for x in cands for n in g.pub.get(join(x, i['name']), ())]
            if not proj or any(pubname(n) in have for n in proj):
                return True
        return False

    def _hiding_edits(self, info, c, m, have):
        """Remove from an `open X hiding a b` / `open X (a b)` list the names that were project
        declarations of X and are not in the carved file ("Unknown constant `X.a`")."""
        g, t = self.g, info.text_bytes
        targets = []
        for i in c.idents or []:
            if i['role'] == 'open':
                targets += g.open_targets(i['name'], c.namespace, m)
        edits = []
        for i in c.idents or []:
            if i['role'] != 'hiding':
                continue
            full = [join(x, i['name']) for x in targets]
            proj = [n for f in full for n in g.pub.get(f, ())]
            if proj and all(pubname(n) not in have for n in proj):
                edits.append((i['start'], _skip_ws(t, i['end']), ''))
        return edits

    def _command_uses(self, m, c):
        """The project declarations the compiled declarations of command c use (with their own
        names), or None when c declares nothing (a context line)."""
        cache = self.__dict__.setdefault('_uses_cache', {})
        if m not in cache:
            by_cmd = collections.defaultdict(set)
            for k, nd in self.g.nodes.items():
                if nd.module == m:
                    # the compiled terms only: source dependencies over-approximate by these
                    # same short-name readings
                    by_cmd[nd.cmd] |= set(nd.term) | set(nd.names) | {k}
            cache[m] = by_cmd
        return cache[m].get(c.index)

    def _rename_edits(self, info, c, m, opens, rename):
        """Rename references Lean resolved to a renamed declaration, and its declId: in every
        identifier token, each part the elaborated port recorded as a renamed constant gets the new
        last component (`D.localize` -> `D.localize_s2`, `(e).f` -> `(e).f_oai`, `ZG.wcl` left alone
        while `AZ.wcl` is renamed). A token with no record falls back to `_rename_text`."""
        g, edits = self.g, []
        if not rename:
            return edits
        done, rest = set(), []
        for i in c.idents or []:
            if i['role'] not in ('decl', 'ref', 'dot'):
                continue
            r = g.reading(info, c, i)
            if r is None:
                rest.append(i)
                continue
            for a, b, n in r.entries + self._binder_entries(info, c, i, r):
                if n in rename:
                    span = last_component(info.text_bytes, a, b)
                    if span not in done:
                        done.add(span)
                        edits.append((span[0], span[1], rename[n]))
        return edits + self._rename_text(info, c, m, opens, rename, rest)

    def _binder_entries(self, info, c, i, r):
        """The declaring entries of token i that its Reading left out for a use (`theorem foo`
        with `foo` also used inside the token: both renamed)."""
        if r.binder:
            return []
        ents = [tuple(x[:3]) for x in c.resolved if len(x) > 3 and x[3] == 'b']
        return [x for x in ents if i['start'] - 1 <= x[0] and x[1] <= i['end'] and x[1] > i['start']]

    def _rename_text(self, info, c, m, opens, rename, idents):
        """The text-based rename of identifiers the elaborated port has no record of (the fallback;
        each fix below is a case where the text reading had disagreed with Lean)."""
        g, edits = self.g, []
        if not idents:
            return edits
        # a field-style use (`D.localize`, `(…).f`) of a renamed declaration: its short name, when
        # exactly one renamed declaration has it (Erdős 3 v2: pieces kept `D.localize` for the
        # imported statement `localize_s2`, "Invalid field")
        by_short = collections.defaultdict(list)
        for n in rename:
            by_short[pubname(n).rsplit('.', 1)[-1]].append(n)
        # what the command's own declarations use: a reading by short name (dot notation on a
        # local, or a field) counts only when it is one of them (Kaplansky 2026-10-18: Mathlib's
        # `HNNExtension.of_injective` became `HNNExtension.of_injective_oai`, read as a field of
        # the local `HNNExtension` because the renamed `MultipleHNN.of_injective` shares its name)
        uses = self._command_uses(m, c)
        # the command's own declarations: its signature cannot name them (PermanentBorder
        # 2026-10-23: in `theorem HasBorderDeterminant.coefficientPolynomial … :
        # HasBorderDeterminant n (coefficientPolynomial k q θ)` the token is the definition
        # `coefficientPolynomial`, and was renamed with the theorem)
        k = g.cmd_node.get((m, c.index))
        own = set(g.nodes[k].names) | {k} if k else set()
        vs = c.value_start.byte if c.value_start else None
        # a section variable or a binder of the command shadows any declaration of its name
        bound = g.scope_vars(info, c) | {i['name'] for i in c.idents or [] if i['role'] == 'binder'}
        for i in idents:
            if i['role'] == 'ref' and not is_field(info, i) and i['name'].split('.')[0] in bound:
                continue
            if i['role'] == 'decl':
                full = i['name'][len('_root_.'):] if i['name'].startswith('_root_.') else \
                    join(c.namespace, i['name'])
                full = g.dup_alias.get(m, {}).get(full, full)
                hits = [n for n in g.pub.get(full, ()) if g.consts[n]['m'] == m and n in rename]
            elif i['role'] == 'ref':
                field = is_field(info, i)
                nm = i['name'][len('_root_.'):] if i['name'].startswith('_root_.') else i['name']
                full = [nm] if i['name'].startswith('_root_.') else \
                    [join(p, nm) for p in prefixes(decl_ns(c))] + [join(o, nm) for o in opens]
                # the project constants the token names as written (no fields stripped)
                skip = own if vs is None or i['start'] < vs else set()
                named = [n for f in full for n in g.pub.get(f, ())
                         if g.visible(n, m) and n not in skip]
                hits = [] if field else \
                    [n for n in g.resolve(i['name'], decl_ns(c), opens, m)
                     if n in rename and n not in skip]
                if hits and '.' in i['name'] and uses is not None:
                    exact = [n for n in named if n in rename]
                    hits = exact or [n for n in hits if n in uses]
                # a field, or dot notation on a local: by short name, only when the token names
                # no project constant as written (Problem355 2026-10-23: inside
                # AuxiliaryZeroCount.weighted_count_le_log, `ZeroGlobalCount.weighted_count_le_log`
                # is that other theorem, and was renamed with the target)
                if not hits and not (named and not field):
                    head = i['name'].split('.')[0]
                    dotted = '.' in i['name'] and not g.resolve_lean(head, decl_ns(c), opens, m)
                    cand = by_short.get(i['name'].rsplit('.', 1)[-1], [])
                    if (field or dotted) and len(cand) == 1 and (uses is None or cand[0] in uses):
                        hits = cand
            else:
                continue
            if hits:
                g.note_fallback(info, c, i)
                parts = i['name'].split('.')
                parts[-1] = rename[hits[0]]
                edits.append((i['start'], i['end'], '.'.join(parts)))
        return edits

    def _decl_edits(self, info, c, m, have, alive, opens, dropped_vars, deprivatize, sorry, rename):
        t = info.text_bytes
        edits = []
        cut = []                 # heads removed whole
        for h in c.heads or []:
            hk = _head_kind(h)
            span = (h['start'], h['end'])
            ids = [i for i in c.idents or [] if span[0] <= i['start'] < span[1]]
            if hk in ('omit', 'include'):
                refs = [i for i in ids if i['role'] in ('ref', 'binder')]
                bad = [i for i in refs if i['name'] in dropped_vars or
                       self._gone(i['name'], c, m, have, opens, idn=i)]
                if refs and len(bad) == len(refs):
                    cut.append(span)
                else:
                    edits += [(i['start'], _skip_ws(t, i['end']), '') for i in bad]
            elif hk == 'open':
                r = self._open(info, c, m, alive, span)
                if r is None:
                    cut.append(span)
                else:
                    edits += r
        edits = [e for e in edits if not any(a <= e[0] < b for a, b in cut)]
        edits += [(a, b, '') for a, b in cut]
        if deprivatize and c.private:
            edits.append((c.private['start'], _skip_ws(t, c.private['end']), ''))
        if sorry:
            if c.doc:
                edits.append((c.doc['start'], _skip_ws(t, c.doc['end']), ''))
            if c.private:
                edits.append((c.private['start'], _skip_ws(t, c.private['end']), ''))
            if c.value_start is None:
                raise CarveError('%s: no value to replace by sorry (line %d)' % (m, c.start.line))
            edits.append((c.value_start.byte, c.end.byte, ':= by\n  sorry'))
        body_end = c.value_start.byte if sorry and c.value_start else c.end.byte
        edits += [e for e in self._rename_edits(info, c, m, opens, rename) if e[0] < body_end]
        edits += self._pin_edits(info, c, m, have, opens, body_end, {e[0] for e in edits})
        return edits

    def _seen_at(self, n, m, c):
        """Could command c of module m name constant n? A constant of the same module counts only
        when declared before c: KernelEllipsoid's `BlockCount` comes after the commands that meant
        MemoryPrecision.BlockCount, and treating the module as seen whole left them unpinned, so a
        file that also has the later one read it (MemoryPrecision, 2026-10-25)."""
        g = self.g
        if not g.visible(n, m):
            return False
        x = g.consts[n]
        r = x.get('r')
        if x['m'] == m and r and not n.startswith('_private.') and (r[0], r[1]) >= (c.start.line, c.start.col):
            return False
        return True

    def _pin_edits(self, info, c, m, have, opens, body_end, taken):
        """A reference that meant one declaration in its module but would read ambiguously or
        differently in the carved file, where modules the original never imported sit side by
        side, is written in full (Hecke 7/8 B027: `PrimeIdeal` under `open ProbePhysical
        HeckeInverseAmplification`; a piece: `sourceRowSeries` in namespace ProbePhysical meant the
        opened ProbeEuler's, before a later module declared ProbePhysical.sourceRowSeries)."""
        g = self.g
        binders = {i['name'] for i in c.idents or [] if i['role'] == 'binder'}
        out = []
        for i in c.idents or []:
            tok = i['name']
            if i['role'] != 'ref' or i['start'] >= body_end or tok.startswith('_root_.') or \
                    any(i['start'] <= a < i['end'] for a in taken):
                continue
            r = g.reading(info, c, i)
            if r is not None:
                # Lean's own reading: the constant the name part denotes. Write it in full when the
                # carved file, where modules the original never imported sit side by side, would
                # read that text as some other project declaration (a library constant included:
                # a project `CD.Finset.foo` in the file would capture `Finset.foo`)
                if len(r.head) != 1 or r.field or r.binder or is_field(info, i) or \
                        r.head[0].startswith('_private.') or \
                        r.head[0] in self.rename or _alternative_name(info, i):
                    continue      # a field, a declared name, a case name (`| zero =>`): not a reference
                orig = r.head[0]
                a, b = r.span
                if a < i['start'] or info.text_bytes[a:b].startswith(b'.'):
                    continue                       # a dot-identifier: resolved by its expected type
                htxt = info.text_bytes[a:b].decode('utf-8')
                if not g.is_project(orig):
                    # a library constant: pinned only when a project declaration the module did not
                    # see would capture the text in the carved file (oaiq-096: project `norm_nonneg`
                    # over Mathlib's); a local or an unresolvable name is left alone
                    if not orig or orig != htxt:
                        continue
                    now, k2 = g.lean_hits(htxt, c.namespace, opens, lambda n: pubname(n) in have)
                    if k2 or not now:
                        continue
                    src, k = g.lean_hits(htxt, c.namespace, opens, lambda n: self._seen_at(n, m, c))
                    if k == 0 and {pubname(n) for n in src} == {pubname(n) for n in now}:
                        continue
                    out.append((a, b, '_root_.' + orig))
                    continue
                now, k2 = g.lean_hits(htxt, c.namespace, opens, lambda n: pubname(n) in have)
                if k2 or not now or {pubname(n) for n in now} == {pubname(orig)}:
                    continue
                # the same candidates the original module saw: Lean chose among them there and
                # will choose the same way here (PermanentBorder: `Plane` read both
                # FrobeniusPlane.Plane and another, in the port too)
                src, k = g.lean_hits(htxt, c.namespace, opens, lambda n: self._seen_at(n, m, c))
                if k == 0 and {pubname(n) for n in src} == {pubname(n) for n in now}:
                    continue
                out.append((a, b, '_root_.' + pubname(orig)))
                continue
            if tok.split('.')[0] in binders:
                continue
            src, k = g.lean_hits(tok, c.namespace, opens, lambda n: self._seen_at(n, m, c))
            if len(src) != 1 or k:
                continue
            now, k2 = g.lean_hits(tok, c.namespace, opens, lambda n: pubname(n) in have)
            if k2 == 0 and now and {pubname(n) for n in now} != {pubname(src[0])}:
                out.append((i['start'], i['end'], '_root_.' + pubname(src[0])))
        return out


# ================================================================ generated files

def header(g, mods, bundles=(), thms=(), collapse_mathlib=True, extra=()):
    """The import block: the modules' non-project imports (all of Mathlib as `import Mathlib`
    with collapse_mathlib), then the Definitions bundles, then the Theorems statements."""
    ext = g.ext_imports(mods) + [x for x in extra if x]
    if collapse_mathlib and any(x == 'Mathlib' or x.startswith('Mathlib.') for x in ext):
        ext = ['Mathlib'] + [x for x in ext if not (x == 'Mathlib' or x.startswith('Mathlib.'))]
    ext = list(dict.fromkeys(x for x in ext if not x.startswith(('Definitions.', 'Theorems.')))) + \
        sorted({x for x in ext if x.startswith('Definitions.')}) + \
        ['Definitions.Def_' + b for b in bundles] + \
        sorted({x for x in ext if x.startswith('Theorems.')}) + \
        ['Theorems.Thm_' + slug(n) for n in sorted(thms)]
    return ''.join('import %s\n' % x for x in dict.fromkeys(ext))


def mark_repaired(g, names):
    """Treat these declarations as sorry-free: a post-carve patch supplies the proof the port
    stubbed (generate then refuses any bundle or piece that still contains `sorry`). `names` is a
    list, or {name: [declarations the patched proof uses]}: the graph read the stub, so it has none
    of the patched proof's dependencies (Erdős 3 v2: a piece kept
    `polynomialVectorMap_second_fderiv_bound` without `polynomialOperator_fderiv_norm_le`)."""
    extra = names if isinstance(names, dict) else {n: [] for n in names}
    for n, deps in extra.items():
        k = g.owner.get(n, n)
        if k not in g.nodes:
            raise CarveError('unknown repaired declaration %s' % n)
        g.nodes[k].sorry = False
        for d in deps or ():
            o = g.owner.get(d)
            if o is None:
                raise CarveError('repaired declaration %s: unknown dependency %s' % (n, d))
            g.nodes[k].term.add(o)
            g.nodes[k].sdeps.add(o)
            g.nodes[k].deps.add(o)


def statement_name(plan, node):
    """The published name of a node: `<name><suffix>`, or the name itself for an external statement."""
    if node in plan.get('external', ()) or not plan.get('statement_suffix'):
        return pubname(node)
    return pubname(node) + plan['statement_suffix']


def _stmt_renames(g, plan, nodes):
    """{node: new short name} for the suffix rename of these nodes."""
    return {n: statement_name(plan, n).rsplit('.', 1)[-1] for n in nodes
            if statement_name(plan, n) != pubname(n)}


def _ext_imports(g, plan, keys, statement_only=False):
    """Modules of the external definitions these declarations (or their statements) use; with
    `statement_only` (a stub, whose proof is `sorry`) only what their statements use."""
    ext = plan.get('external_defs') or {}
    if not ext:
        return []
    return sorted({ext[d] for k in keys
                   for d in g.nodes[k].sig | (set() if statement_only else g.nodes[k].deps)
                   if d in ext})


def _bundle_have(g, plan, names):
    """The nodes the bundles `names` and what they import declare: their plan nodes, less the local
    instances their text lost (`absent_instances`, set by `generate`)."""
    pos, bimp, _ = _plan_index(plan)
    cl = _bundle_closure(bimp, [pos[n] for n in names])
    absent = plan.get('absent_instances') or {}
    return {k for i in cl for k in plan['bundles'][i]['nodes']
            if k not in absent.get(plan['bundles'][i]['name'], ())}


def absent_instances(g, plan, name, text):
    """The local instance nodes of bundle `name` that its text does not declare: a repair cut the
    command (p2mlib.repair takes a `local instance` for a context command), so a file importing the
    bundle must emit the command again, not `attribute [local instance]` a constant no file declares
    (Lech oaiq-032, Def_OAIQ032L039:289: `scalarComm_p6`, cut from L026)."""
    b = next(x for x in plan['bundles'] if x['name'] == name)
    ren = collision_renames(g)
    inst_names = getattr(g, 'instance_names', None) or {}
    body = strip(text)
    out = set()
    for k in b['nodes']:
        nd = g.nodes.get(k)
        # the command, not nd.instance: DeclGraph reads the environment, where a local instance is
        # no instance once its section ends
        if nd is None or not _local_instance(g.infos[nd.module], g.infos[nd.module].commands[nd.cmd])[0]:
            continue
        short = instance_ref(k, inst_names, ren).rsplit('.', 1)[-1]
        if not re.search(r'\binstance\s+' + re.escape(short) + r"(?![\w'.!?])", body):
            out.add(k)
    return out


def _ext_have(g, plan, own, bundles=(), statements=()):
    """The external definitions a file can name: those of the external bundles it imports itself
    (`own`, its `_ext_imports`) or through a bundle or statement it imports. Not every
    external definition: a file that does not import Def_OAIStdSimplexCompat cannot name its
    instances, and hiding them there was "Unknown constant" (Eilenberg–Ganea 2026-10-24)."""
    ext = plan.get('external_defs') or {}
    if not ext:
        return set()
    pos, bimp, _ = _plan_index(plan)
    mods = set(own)
    seen_b, seen_s = set(), set()
    todo_b, todo_s = list(bundles), list(statements)
    while todo_b or todo_s:
        if todo_s:
            st = todo_s.pop()
            if st in seen_s:
                continue
            seen_s.add(st)
            mods.update(_ext_imports(g, plan, [st], statement_only=True))
            todo_b.extend(plan['stubs'].get(st, {}).get('bundles', ()))
            continue
        name = todo_b.pop()
        if name in seen_b or name not in pos:
            continue
        seen_b.add(name)
        b = plan['bundles'][pos[name]]
        mods.update(_ext_imports(g, plan, b['nodes']))
        todo_b.extend(b['imports'])
        todo_s.extend(b.get('statements', ()))
    return {d for d, mod in ext.items() if mod in mods}


def gen_bundle(g, plan, name, collapse_mathlib=True):
    b = next(x for x in plan['bundles'] if x['name'] == name)
    keep = set(b['nodes'])
    bad = sorted(k for k in keep if g.nodes[k].sorry)
    if bad:
        raise CarveError('bundle %s would contain sorry: %s (repair the port first)' % (name, bad))
    sts = list(b.get('statements', ()))
    avail = _bundle_have(g, plan, b['imports']) | set(sts)
    avail |= _ext_have(g, plan, _ext_imports(g, plan, keep), b['imports'], sts)
    for st in sts:
        avail |= _bundle_have(g, plan, plan['stubs'][st]['bundles'])
    ren = collision_renames(g)
    ren.update(_stmt_renames(g, plan, sts))
    body = Carver(g).carve(keep, g.have_names(keep | avail), deprivatize=True, rename=ren,
                         external=plan.get('external_defs') or ())
    hdr = header(g, {g.nodes[k].module for k in keep}, b['imports'],
                 [statement_name(plan, st) for st in sts], collapse_mathlib,
                 extra=_ext_imports(g, plan, keep))
    return hdr + '\n' + body.rstrip('\n') + '\n'


def gen_stub(g, plan, node, collapse_mathlib=True):
    bs = plan['stubs'][node]['bundles']
    avail = _bundle_have(g, plan, bs)
    avail |= _ext_have(g, plan, _ext_imports(g, plan, [node], statement_only=True), bs)
    ren = collision_renames(g)
    ren.update(_stmt_renames(g, plan, [node]))
    body = Carver(g).carve({node}, g.have_names({node} | avail), sorry={node}, rename=ren,
                         external=plan.get('external_defs') or ())
    # no comments: a statement's formal_statement freezes at publish and api.call refuses one
    # carrying a comment (the `-- module` markers, OpenAI's comments in kept context lines)
    body = re.sub(r'\n\s*\n(\s*\n)+', '\n\n', '\n'.join(l.rstrip() for l in strip(body).split('\n')))
    hdr = header(g, {g.nodes[node].module}, bs, (), collapse_mathlib,
                 extra=_ext_imports(g, plan, [node], statement_only=True))
    return hdr + '\n' + body.strip('\n') + '\n'


def solution_tail(g, node, plan=None):
    nd = g.nodes[node]
    lv = '.{%s}' % ', '.join(nd.univ) if nd.univ else ''
    full = (statement_name(plan, node) if plan else pubname(node)) + '_oai'
    return 'theorem solution%s : type_of%% @%s%s := @%s%s\n' % (lv, full, lv, full, lv)


def gen_piece(g, plan, node, collapse_mathlib=True):
    """The node's piece: its keep set carved, OpenAI's own declaration of the node renamed
    `<name>_oai` (the verifier's environment already declares `<name>`; a same-named declaration
    that elaborates even slightly differently gives a locationless WA, Chowla 2026-10-08), and
    `theorem solution : type_of% @<name>_oai := @<name>_oai`."""
    p = plan['pieces'][node]
    keep = set(p['keep'])
    bad = sorted(k for k in keep if g.nodes[k].sorry)
    if bad:
        raise CarveError('piece %s would contain sorry: %s (repair the port first)' % (node, bad))
    avail = _bundle_have(g, plan, p['bundles']) | set(p['imports'])
    avail |= _ext_have(g, plan, _ext_imports(g, plan, keep), p['bundles'], p['imports'])
    for i in p['imports']:
        avail |= _bundle_have(g, plan, plan['stubs'][i]['bundles'])
    ren = collision_renames(g)
    ren.update(_stmt_renames(g, plan, p['imports']))
    ren[node] = statement_name(plan, node).rsplit('.', 1)[-1] + '_oai'
    body = Carver(g).carve(keep, g.have_names(keep | avail), rename=ren,
                         external=plan.get('external_defs') or ())
    hdr = header(g, {g.nodes[k].module for k in keep}, p['bundles'],
                 [statement_name(plan, i) for i in p['imports']], collapse_mathlib,
                 extra=_ext_imports(g, plan, keep))
    return hdr + '\n' + body.rstrip('\n') + '\n\n' + solution_tail(g, node, plan)


def generate(g, plan, out, what=('bundles', 'stubs', 'pieces'), names=None, external=(),
             collapse_mathlib=True, patches=(), repairs=None, frozen_text=None, frozen_stubs=None):
    """Write out/lib/Def_<bundle>.lean, out/lib/Thm_<slug>.lean (not for `external` nodes,
    published by someone else) and out/solutions/Sol_<slug>.lean. Returns {'files', 'sizes',
    'over_cap'} (files over prove2.me's 1 MiB cap), 'patches_unused'}.

    `patches`: [{'literal_old', 'literal_new'}] text replacements applied to every generated file.
    Proof fixes (a port's leftover `sorry`, a slow proof) go here, never into the port's source: the
    carver cuts modules by the command ranges recorded when the port was compiled, so a source edit
    corrupts every later carve of that module (Erdős 3, 2026-10-16).

    `repairs`: {file name: [cut]}, the cuts carve_measure recorded in work/repairs.json, applied
    after the patches, so a regenerated file is the one that was measured (and published);
    a cut that no longer matches is returned in 'stale_repairs' as (file name, cut).

    `frozen_stubs`: {file name: text} of live statements, written the same way (a live statement
    cannot change).
    `frozen_text`: {bundle name: text} of published bundles. A published bundle is frozen, so its
    file is written exactly as published; when the generator (with patches and repairs) would
    write something else, the bundle is listed in 'frozen_drift' (Boone-Higman, 2026-10-24: a
    carve extending a published one regenerated its frozen bundles without their repair)."""
    repairs, frozen_text = repairs or {}, frozen_text or {}
    frozen_stubs = frozen_stubs or {}
    stale, drift = [], []
    os.makedirs(os.path.join(out, 'lib'), exist_ok=True)
    os.makedirs(os.path.join(out, 'solutions'), exist_ok=True)
    files = []

    used = set()

    def put(path, txt, published=None):
        for pt in patches:
            if pt['literal_old'] in txt:
                txt = txt.replace(pt['literal_old'], pt['literal_new'])
                used.add(pt['literal_old'])
        base = os.path.basename(path)
        if repairs.get(base):
            txt, _, bad = RP.apply_cuts(txt, repairs[base])
            stale.extend((base, c) for c in bad)
        if published is not None:
            if txt != published:
                drift.append(base)
            txt = published
        if os.path.basename(path).startswith(('Def_', 'Sol_')) and re.search(r'\bsorry\b', strip(txt)):
            raise CarveError('%s still contains sorry (a repaired declaration whose patch did not apply?)' % path)
        # what prove2.me's soundness guard refuses, found before publishing (WLTime 2026-10-23: a
        # bundle kept OpenAI's `def prelude`; the port renames it now, oaiport.guard_renames)
        bad = guard_problems(txt)
        if bad:
            raise CarveError('%s: the soundness guard would refuse %s; rename it in the port '
                             '(oaiport.guard_renames) or by a carve patch' % (path, guard_message(bad)))
        with open(path, 'w', encoding='utf-8') as f:
            f.write(txt)
        files.append(path)
        return txt
    # what each bundle's text really declares: a later file activates only those local instances
    # and emits the others again (`absent_instances`); a bundle not written now is read as it stands
    # (published, or the earlier run's file)
    plan = dict(plan, absent_instances={})
    real_imports = {}
    for b in plan['bundles']:
        name = b['name']
        path = os.path.join(out, 'lib', 'Def_%s.lean' % name)
        if 'bundles' in what and (names is None or name in names):
            txt = put(path, gen_bundle(g, plan, name, collapse_mathlib), frozen_text.get(name))
        elif name in frozen_text:
            txt = frozen_text[name]
        elif os.path.exists(path):
            txt = open(path, encoding='utf-8').read()
        else:
            continue
        lost = absent_instances(g, plan, name, txt)
        if lost:
            plan['absent_instances'][name] = sorted(lost)
        real_imports[name] = [m for m in re.findall(r'^import Definitions\.Def_(\S+)\s*$', txt, re.M)]
    bof = {k: b['name'] for b in plan['bundles'] for k in b['nodes']}

    def need(kind, n):
        if kind == 'stubs':
            ds = set(g.nodes[n].sig) if n in g.nodes else set()
        else:
            keep = plan['pieces'][n].get('keep', ())
            ds = {d for x in keep if x in g.nodes for d in g.nodes[x].deps | {x}}
        return {bof[d] for d in ds if d in bof}
    plan = restore_cut_bundle_imports(plan, real_imports, need)
    for n in plan['nodes']:
        if names is not None and n not in names:
            continue
        external = set(external) | set(plan.get('external', ()))
        if 'stubs' in what and n not in external:
            fn = 'Thm_%s.lean' % slug(statement_name(plan, n))
            put(os.path.join(out, 'lib', fn), gen_stub(g, plan, n, collapse_mathlib), frozen_stubs.get(fn))
        if 'pieces' in what:
            put(os.path.join(out, 'solutions', 'Sol_%s.lean' % slug(statement_name(plan, n))),
                gen_piece(g, plan, n, collapse_mathlib))
    sizes = {f: os.path.getsize(f) for f in files}
    return {'files': files, 'sizes': sizes, 'over_cap': [f for f, s in sizes.items() if s > SIZE_CAP],
            'patches_unused': [pt['literal_old'] for pt in patches if pt['literal_old'] not in used],
            'stale_repairs': stale, 'frozen_drift': drift}
