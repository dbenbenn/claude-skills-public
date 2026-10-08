"""The carver: split a large ported Lean development into prove2.me Definitions bundles, published
intermediate statements and one carved proof piece per statement (scripts/carve.py is its command
line; read its docstring for the workflow and the lessons behind each rule).

Inputs, both from Lean:
* lean/DeclGraph.lean on the compiled development: every constant, its declaration range, and the
  project constants its type and value use (`load_decl_graph`);
* lean/LeanInfo.lean --parse-only --idents on each module: its commands, scopes, and every
  identifier with its role (`module_info`).

`Graph` joins them. A node is a declaration COMMAND (its constants: a structure with its fields,
constructor and recursor, a def with its equation lemmas). Its dependencies are the owners of the
constants its constants use (`term`), plus every identifier its source names that resolves to a
project declaration in its namespace and opens (`simp only [h]` with an `rfl` lemma `h` leaves no
trace in the term), plus what the `local notation`s in force before it name. `make_plan` chooses
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
from dataclasses import dataclass, field

from . import leanedit, leaninfo

HERE = os.path.dirname(os.path.abspath(__file__))
DECLGRAPH = os.path.join(os.path.dirname(HERE), 'lean', 'DeclGraph.lean')
SIZE_CAP = 1 << 20                     # prove2.me refuses a solution or statement over 1 MiB

NOTATION = {'notation', 'mixfix', 'notation3'}
# the platform refuses these in any submitted file (prove2me SKILL: "notation ok, macros refused")
REFUSED = {'macro', 'syntax', 'macro_rules', 'elab', 'elab_rules', 'syntaxAbbrev', 'syntaxCat',
           'declare_syntax_cat'}
REDUCIBILITY = re.compile(r'\[\s*(?:local\s+|scoped\s+)?(?:reducible|irreducible|semireducible)\b')
DIAGNOSTIC = {'check', 'eval', 'print', 'printAxioms', 'reduce', 'check_failure', 'synth',
              'evalBang', 'exit'}
OPENERS = {'namespace', 'section', 'noncomputableSection'}


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

def run_decl_graph(out, prefix, roots, ws=None, timeout=7200):
    """lean/DeclGraph.lean on the compiled ROOT modules (their .olean must be built)."""
    ws = ws or leaninfo.workspace()
    r = subprocess.run(['lake', 'env', 'lean', '--run', DECLGRAPH, out, prefix] + list(roots),
                       cwd=ws, capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise CarveError('DeclGraph failed:\n' + (r.stdout + r.stderr)[-3000:])
    return out


def module_path(src_root, m):
    return os.path.join(src_root, *m.split('.')) + '.lean'


def module_info(src_root, m, ws=None, use_cache=True):
    """LeanInfo (parse-only, with identifiers) of module m under src_root; cached."""
    return leaninfo.run(module_path(src_root, m), parse_only=True, idents=True, ws=ws,
                        use_cache=use_cache)


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
        for imp in re.findall(r'^import\s+(\S+)', open(module_path(src_root, m)).read(), re.M):
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
            data = leaninfo.raw(module_path(src_root, m), parse_only=True, ws=ws, idents=True)
            data['file'] = os.path.relpath(module_path(src_root, m), src_root)
            rel = os.path.relpath(module_path(src_root, m), src_root)[:-5] + '.parse.json'
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
    sig: set = field(default_factory=set)     # what its statement needs: tdeps + names before `:=`
    deps: set = field(default_factory=set)    # term | sdeps | ndeps


def load_decl_graph(path):
    consts, imports, ext = {}, {}, set()
    for line in open(path, encoding='utf-8'):
        if not line.strip():
            continue
        x = json.loads(line)
        if 'n' in x:
            consts[x['n']] = x
        elif 'module' in x:
            imports[x['module']] = list(dict.fromkeys(x['imports']))
        elif 'ext_namespaces' in x:
            ext = set(x['ext_namespaces'])
    return consts, imports, ext


def _is_decl_command(c):
    return bool(c.decl_kind) and c.decl_kind != 'example' or c.short_kind in ('mutual', 'alias') or \
        (bool(c.names) and c.short_kind not in NOTATION | REFUSED)


def _is_local(text):
    """A `local`/`scoped` notation, or an `attribute [local …]`: it lasts to the end of its scope."""
    return bool(re.match(r'\s*(?:/--.*?-/\s*)?(?:@\[[^\]]*\]\s*)?(?:local|scoped)\b', text, re.S)) or \
        '[local ' in text or '[scoped ' in text


def _head_kind(h):
    return h['kind'].rsplit('.', 1)[-1]


class Graph:
    """The declaration graph of a development: nodes (declaration commands), module DAG, name
    resolution. `Graph.load(decl_graph.jsonl, src_root)` reads the module infos (recorded
    `<module>.parse.json` beside the source if present, else LeanInfo, cached)."""

    def __init__(self, consts, imports, ext_ns, infos):
        self.consts, self.imports, self.ext_ns, self.infos = consts, imports, ext_ns, infos
        self.modules = sorted(infos)
        self._closure_cache = {}
        self._build_modules()
        self._build_nodes()
        self._build_names()
        self._build_deps()

    @classmethod
    def load(cls, decl_graph, src_root, ws=None):
        consts, imports, ext = load_decl_graph(decl_graph)
        infos = {}
        for m in imports:
            rec = module_path(src_root, m)[:-5] + '.parse.json'
            if os.path.exists(rec):
                infos[m] = leaninfo.parse(json.load(open(rec, encoding='utf-8')),
                                          open(module_path(src_root, m), 'rb').read())
            else:
                infos[m] = module_info(src_root, m, ws)
        return cls(consts, imports, ext, infos)

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
        """Non-project imports of mods and of the project modules they import."""
        seen, out, todo = set(), [], list(mods)
        while todo:
            m = todo.pop()
            if m in seen:
                continue
            seen.add(m)
            for x in self.imports.get(m, []):
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
        for n in self.owner:
            bit = 1 << self.mod_index[self.consts[n]['m']]
            for p in ns_prefixes(pubname(n)):
                nsmods[p] |= bit
        for m, info in self.infos.items():
            bit = 1 << self.mod_index[m]
            for c in info.commands:
                if c.short_kind == 'namespace':
                    tok = leanedit.text(info, c.index).split()[1]
                    full = join(c.namespace, tok)
                    for p in ns_prefixes(full + '.x'):
                        nsmods[p] |= bit
        self.ns_mask = dict(nsmods)
        self.proj_ns = set(nsmods)

    def ns_existed(self, ns, m):
        """Did project namespace ns exist when module m was elaborated (from m's imports or m)?"""
        return bool(self.ns_mask.get(ns, 0) & self.closure_mask[m])

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

    def resolve(self, tok, ns, opens, m):
        """The project constants (env names) identifier `tok` may denote in module m, namespace ns,
        with project namespaces `opens` open. Over-approximates: every reading Lean could take,
        and when none, the reading with trailing fields (`h.mp`, `foo.1`) stripped."""
        if tok.startswith('_root_.'):
            cands = [tok[len('_root_.'):]]
        else:
            cands = [join(p, tok) for p in prefixes(ns)] + [join(o, tok) for o in opens]
        for strip in range(3):
            hits = []
            for c in cands:
                if strip:
                    parts = c.split('.')
                    if len(parts) <= strip:
                        continue
                    c = '.'.join(parts[:-strip])
                hits += [n for n in self.pub.get(c, ()) if self.visible(n, m)]
            if hits:
                return list(dict.fromkeys(hits))
        # dot notation on a local (`A.coord_eq` with `A : Space`, Erdős 3 B024): the head names no
        # declaration, so read the field by its short name when that is (nearly) unambiguous
        if '.' in tok and not tok.startswith('_root_.'):
            hits = [n for n in self.short.get(tok.rsplit('.', 1)[-1], ()) if self.visible(n, m)]
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
        for strip in range(3):
            parts = tok.split('.')
            if strip and len(parts) <= strip:
                break
            t = '.'.join(parts[:len(parts) - strip])
            for p in prefixes(ns)[:-1]:
                hits = [n for n in self.pub.get(join(p, t), ()) if self.visible(n, m)]
                if hits:
                    return hits
            hits = [n for c in [t] + [join(o, t) for o in opens]
                    for n in self.pub.get(c, ()) if self.visible(n, m)]
            if hits:
                return list(dict.fromkeys(hits))
        return self.resolve(tok, ns, opens, m)

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
        for idn in c.idents or []:
            if idn['role'] != 'ref' or (before is not None and idn['start'] >= before):
                continue
            for n in self.resolve(idn['name'], c.namespace, opens, m):
                o = self.owner.get(n)
                if not o or o == me:
                    continue
                on = self.nodes[o]
                if on.module == m and on.cmd >= c.index:
                    continue
                out.add(o)
        return out

    def _build_deps(self):
        for k, nd in self.nodes.items():
            info = self.infos[nd.module]
            c = info.commands[nd.cmd]
            declared = set(c.names)
            for n in nd.names:
                x = self.consts[n]
                nd.term |= self._owners(x['t'] + x['v'], k)
                if n == k or pubname(n) in declared:
                    nd.tdeps |= self._owners(x['t'], k)
            nd.sdeps = self._source_refs(info, c, nd.module, k)
            vs = c.value_start.byte if c.value_start else None
            nd.sig = set(nd.tdeps) | self._source_refs(info, c, nd.module, k, before=vs)
        # `attribute [simp] foo` marks foo; notations in force are dependencies of what follows
        for m, info in self.infos.items():
            notations = []
            for c in info.commands:
                if c.short_kind == 'attribute':
                    for o in self._source_refs(info, c, m, None):
                        self.nodes[o].attributed = True
                elif c.short_kind in NOTATION:
                    inner = c.context[-1][0] if c.context else None
                    notations.append((inner, self._source_refs(info, c, m, None)))
                key = self.cmd_node.get((m, c.index))
                if key:
                    openers = {o for o, _ in c.context}
                    for inner, refs in notations:
                        if inner is None or inner in openers:
                            self.nodes[key].ndeps |= refs - {key}
        for k, nd in self.nodes.items():
            nd.deps = nd.term | nd.sdeps | nd.ndeps

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

    def have_names(self, keys):
        """The public names a set of nodes declares (what a file keeping or importing them has)."""
        return {pubname(n) for k in keys for n in self.nodes[k].names}


def collision_renames(g):
    """Private declarations whose public names collide (two modules' `private theorem helper`, in
    one carved file or deprivatized): {env name: new short name}, the same in every file."""
    out = {}
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


def make_plan(g, targets, forced=(), budget=60.0, piece_size=700_000, bundle_budget=90.0,
              bundle_size=650_000, band_width=4.0, cost=None, frozen=None, bundle_prefix='Bundle'):
    """The split: bundles, nodes (published statements) and each node's piece.

    - Bundle material B: every reachable non-theorem, what reachable statements need, their
      closure (a definition cannot import a theorem statement, so a theorem a definition uses is
      proved inside the bundle), and the instances and attributed declarations whose dependencies
      are then present.
    - Nodes: targets and `forced`, plus theorems promoted greedily, bottom-up, until each piece
      (its closure over non-node theorems) costs at most `budget` seconds and `piece_size` bytes.
      A node needs an ASCII public name and a statement that only uses bundle material.
    - `frozen`: (old plan, [bundle names]) of bundles already published, kept as they are."""
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
    B = g.closure(seeds) | {k for ch in fz_chunks for k in ch}
    B |= g.extra_roots(B, set())
    T = reach - B
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

    def ok_node(k):
        nd = g.nodes[k]
        return nd.theorem and not nd.private and ascii_ok(k) and nd.sig <= B and k not in renames

    for t in sorted(nodes):
        if not g.nodes[t].theorem or g.nodes[t].sig - B:
            raise CarveError('%s cannot be a published statement: %s' % (
                t, 'not a theorem' if not g.nodes[t].theorem else
                'its statement needs %s' % sorted(g.nodes[t].sig - B)))

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
    chunks = chunk_bundles(g, B, cost, bundle_budget, bundle_size, band_width, fz_chunks)
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
    for j, ch in enumerate(chunks):
        for k in ch:
            for d in g.nodes[k].deps:
                if d in bidx and bidx[d] != j:
                    bimp[j].add(bidx[d])
    red = [_reduce(bimp, bimp[j]) for j in range(len(chunks))]
    bundles = [{'name': names[j], 'nodes': chunks[j], 'imports': [names[i] for i in sorted(red[j])],
                'cost': round(pcost(chunks[j]), 2), 'size': psize(chunks[j])}
               for j in range(len(chunks))]

    def need(keys):
        return {bidx[d] for x in keys for d in g.nodes[x].deps | {x} if d in bidx}
    pieces, stubs = {}, {}
    for n in sorted(nodes):
        keep = fresh(n)
        imps = {d for x in keep for d in g.nodes[x].deps if d in nodes and d not in keep}
        bks = need(keep) - {bidx[x] for x in keep if x in bidx}
        avail = {k for k in B if bidx[k] in _bundle_closure(bimp, bks)} | imps
        keep |= {k for k in g.extra_roots(keep, avail) if k not in nodes and k not in B}
        bks = need(keep - B)
        pieces[n] = {'keep': sorted(keep), 'imports': sorted(imps),
                     'bundles': [names[i] for i in sorted(_reduce(bimp, bks))],
                     'cost': round(pcost(keep), 2), 'size': psize(keep)}
        sb = {bidx[d] for d in g.nodes[n].sig if d in bidx}
        stubs[n] = {'bundles': [names[i] for i in sorted(_reduce(bimp, sb))]}
    return {'version': 1, 'targets': targets, 'forced': forced, 'bundle_prefix': bundle_prefix,
            'budget': budget, 'bundles': bundles, 'nodes': sorted(nodes), 'pieces': pieces,
            'stubs': stubs, 'over': sorted(set(over)),
            'sorry': sorted(k for k in reach | B if g.nodes[k].sorry)}


def _bundle_closure(bimp, ks):
    out, todo = set(), list(ks)
    while todo:
        k = todo.pop()
        if k in out:
            continue
        out.add(k)
        todo += bimp[k]
    return out


def _plan_index(plan):
    pos = {b['name']: i for i, b in enumerate(plan['bundles'])}
    bimp = [[pos[x] for x in b['imports'] if x in pos] for b in plan['bundles']]
    bidx = {k: i for i, b in enumerate(plan['bundles']) for k in b['nodes']}
    return pos, bimp, bidx


def check_plan(g, plan):
    """What would not compile: every dependency of a bundle member in its bundle or one it
    imports; of a piece, in the piece, an imported statement or its bundles; of a statement, in
    its bundles. A missing definition is Erdős 3 B006 ("Unknown identifier `A.space`"). Returns
    a list of problems (empty: the plan is consistent)."""
    pos, bimp, bidx = _plan_index(plan)
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
    for i, b in enumerate(plan['bundles']):
        if any(pos.get(x, len(pos)) >= i for x in b['imports']):
            probs.append('bundle %s imports a later or unknown bundle' % b['name'])
        cl = _bundle_closure(bimp, [i])
        for k in b['nodes']:
            for d in sorted(g.nodes[k].deps):
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
        have = set(p['keep']) | set(p['imports'])
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
        for d in sorted(g.nodes[n].sig):
            if not (d in bidx and bidx[d] in cl):
                probs.append('statement %s needs %s, not in its bundles' % (n, d))
    return probs


def publish_order(plan, external=()):
    """The import DAG as waves: every item of a wave can publish concurrently once the earlier
    waves are published. Items: `bundle:NAME`, `statement:NODE` (after its bundles; none for
    `external` nodes, published by someone else), `piece:NODE` (after its own statement, the
    statements it imports and its bundles)."""
    deps = {}
    for b in plan['bundles']:
        deps['bundle:' + b['name']] = ['bundle:' + x for x in b['imports']]
    for n, s in plan['stubs'].items():
        if n not in external:
            deps['statement:' + n] = ['bundle:' + x for x in s['bundles']]
    for n, p in plan['pieces'].items():
        d = ['bundle:' + x for x in p['bundles']] + \
            ['statement:' + x for x in p['imports'] if x not in external]
        if n not in external:
            d.append('statement:' + n)
        deps['piece:' + n] = d
    level = {}

    def lv(x):
        if x not in level:
            level[x] = 0
            level[x] = 1 + max([lv(y) for y in deps[x]], default=-1)
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
    * `open X` where X now names no namespace goes (B007); where it would now also open a
      namespace the original module never saw (one from a module it did not import, emitted
      earlier in the file), it is pinned to what it meant: `open _root_.X`;
    * `example` and `#check`-style commands go; a kept `macro`/`syntax` command is refused.
    Options: `deprivatize` (bundles: drop `private`), `sorry` (stubs: these nodes' values become
    `by sorry`, doc comments dropped), `rename` ({env name: new short name}: the `_oai` rename
    and private collisions; declarations and the references Lean resolves to them)."""

    def __init__(self, g):
        self.g = g

    def carve(self, keep, have, deprivatize=False, sorry=(), rename=None):
        g = self.g
        keep = set(keep)
        have = set(have) | g.have_names(keep)
        self.keep_names = g.have_names(keep)
        rename = dict(rename or {})
        mods = g.topo({g.nodes[k].module for k in keep})
        kept_cmds = {m: {g.nodes[k].cmd for k in keep if g.nodes[k].module == m} for m in mods}
        # pass 1: what goes, per module (independent of namespaces)
        drops = {m: self._drops(m, kept_cmds[m], have) for m in mods}
        # namespaces the carved file has: those of its names, and of its kept namespace commands
        alive = set()
        for p in have:
            alive.update(ns_prefixes(p))
        for m in mods:
            info = g.infos[m]
            for c in info.commands:
                if c.short_kind == 'namespace' and c.index not in drops[m]:
                    full = join(c.namespace, leanedit.text(info, c.index).split()[1])
                    alive.update(ns_prefixes(full + '.x'))
        out = []
        for m in mods:
            out.append(self._module(m, kept_cmds[m], drops[m], have, alive, deprivatize,
                                    {g.nodes[k].cmd for k in sorry if g.nodes[k].module == m},
                                    rename))
        return ''.join(out)

    # ---------------------------------------------------------- what goes
    def _gone(self, tok, c, m, have, opens, bound=()):
        """Does identifier tok, read in command c's scope, name only gone project declarations?"""
        if tok.split('.')[0] in bound:
            return False
        hits = self.g.resolve_lean(tok, c.namespace, opens, m)
        return bool(hits) and all(pubname(h) not in have for h in hits)

    def _drops(self, m, kept, have):
        g, info = self.g, self.g.infos[m]
        drop = set()
        for c in info.commands:
            if _is_decl_command(c) and c.index not in kept:
                drop.add(c.index)
            elif c.short_kind in DIAGNOSTIC or c.decl_kind == 'example':
                drop.add(c.index)
        # notations and attributes that name gone declarations
        keep_global = set()
        for c in info.commands:
            if c.index in drop:
                continue
            if c.short_kind in NOTATION or c.short_kind == 'attribute':
                opens = g.scope_opens(info, c, m)
                refs = [i for i in c.idents or [] if i['role'] == 'ref']
                gone = [i for i in refs if self._gone(i['name'], c, m, have, opens)]
                if c.short_kind in NOTATION and gone:
                    drop.add(c.index)
                elif c.short_kind == 'attribute' and refs and len(gone) == len(refs):
                    drop.add(c.index)
                elif not _is_local(leanedit.text(info, c.index)):
                    keep_global.add(c.index)
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
        for c in info.commands:
            if c.index in drop:
                continue
            edits = []
            opens = g.scope_opens(info, c, m)
            k = c.short_kind
            if k == 'variable':
                r = self._variable(info, c, m, have, opens, dropped_vars, protect.get(c.index, set()))
                if r is None:
                    drop.add(c.index)
                elif r is not False:
                    reps[c.index] = r
                continue
            if k in ('include', 'omit'):
                ids = [i for i in c.idents or [] if i['role'] in ('ref', 'binder')]
                bad = [i for i in ids if i['name'] in dropped_vars or
                       self._gone(i['name'], c, m, have, opens)]
                if bad and len(bad) == len(ids):
                    drop.add(c.index)
                elif bad:
                    reps[c.index] = _cmd_text(info, c, [(i['start'], _skip_ws(t, i['end']), '') for i in bad])
                continue
            if k == 'attribute':
                txt = leanedit.text(info, c.index)
                # a global reducibility change may only touch this file's declarations ("failed to
                # set reducibility status, `auxOnly` has not been defined in this file"): it stays
                # with the bundle that declares its target
                here = keep_names if (REDUCIBILITY.search(txt) and not _is_local(txt)) else None
                refs = [i for i in c.idents or [] if i['role'] == 'ref']
                gone = [i for i in refs if self._gone(i['name'], c, m, have, opens) or
                        (here is not None and self._gone(i['name'], c, m, here, opens))]
                if gone and len(gone) == len(refs):
                    drop.add(c.index)
                elif gone:
                    reps[c.index] = _cmd_text(info, c, [(i['start'], _skip_ws(t, i['end']), '') for i in gone])
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
            if k in REFUSED or (c.heads and any(_head_kind(h) in REFUSED for h in c.heads)):
                raise CarveError('%s keeps a `%s` command (line %d), which prove2.me refuses: no '
                                 'macro or syntax commands' % (m, k, c.start.line))
            if c.index in kept:
                edits += self._decl_edits(info, c, m, have, alive, opens, dropped_vars,
                                          deprivatize, c.index in sorry, rename)
            elif c.short_kind in NOTATION:
                edits += self._rename_edits(info, c, m, opens, rename)
            if edits:
                reps[c.index] = _cmd_text(info, c, edits)
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

    def _variable(self, info, c, m, have, opens, dropped_vars, protected):
        """The `variable` command without its gone binder groups: False (unchanged), None (none
        left) or the new text."""
        groups = c.binders or []
        bound = {n for grp in groups for n in grp['names']}
        refs = [i for i in c.idents or [] if i['role'] == 'ref']
        bad, changed = set(), True
        while changed:
            changed = False
            lost = {n for j in bad for n in groups[j]['names']} | dropped_vars
            for j, grp in enumerate(groups):
                if j in bad or set(grp['names']) & protected:
                    continue
                inside = [i for i in refs if grp['start'] <= i['start'] < grp['end']]
                if any(i['name'].split('.')[0] in lost - set(grp['names']) or
                       self._gone(i['name'], c, m, have, opens, bound - lost) for i in inside):
                    bad.add(j)
                    changed = True
        # a name bound again here is a new variable, not the dropped one
        dropped_vars.difference_update(n for j, grp in enumerate(groups) if j not in bad
                                       for n in grp['names'])
        if not bad:
            return False
        dropped_vars.update(n for j in bad for n in groups[j]['names'])
        if len(bad) == len(groups):
            return None
        t = info.text_bytes
        return 'variable ' + ('\n  ').join(t[grp['start']:grp['end']].decode('utf-8')
                                          for j, grp in enumerate(groups) if j not in bad)

    def _open(self, info, c, m, alive, span):
        """Edits for the namespace tokens of an `open` in [span): [] unchanged, None when nothing
        is left to open."""
        g = self.g
        toks = [i for i in c.idents or [] if i['role'] == 'open' and span[0] <= i['start'] < span[1]]
        special = any(i['role'] == 'hiding' and span[0] <= i['start'] < span[1] for i in c.idents or [])
        edits, dead = [], 0
        for i in toks:
            tok = i['name']
            cands = [tok[len('_root_.'):]] if tok.startswith('_root_.') else \
                [join(p, tok) for p in prefixes(c.namespace)]
            known = [x for x in cands if x in g.proj_ns or x in g.ext_ns]
            if not known:
                continue                      # Mathlib's, say: carving cannot change it
            now = [x for x in cands if x in g.ext_ns or x in alive]
            orig = [x for x in cands if x in g.ext_ns or g.ns_existed(x, m)]
            if not now:
                dead += 1
                edits.append((i['start'], _skip_ws(info.text_bytes, i['end']), ''))
                continue
            if any(x not in orig for x in now):
                meant = [x for x in now if x in orig]
                if not meant:
                    dead += 1
                    edits.append((i['start'], _skip_ws(info.text_bytes, i['end']), ''))
                else:
                    edits.append((i['start'], i['end'], ' '.join('_root_.' + x for x in meant)))
        if toks and (dead == len(toks) or (special and dead)):
            return None
        return edits

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

    def _rename_edits(self, info, c, m, opens, rename):
        """Rename references Lean resolves to a renamed declaration, and its declId."""
        g, edits = self.g, []
        if not rename:
            return edits
        for i in c.idents or []:
            if i['role'] == 'decl':
                full = i['name'][len('_root_.'):] if i['name'].startswith('_root_.') else \
                    join(c.namespace, i['name'])
                hits = [n for n in g.pub.get(full, ()) if g.consts[n]['m'] == m and n in rename]
            elif i['role'] == 'ref':
                hits = [n for n in g.resolve(i['name'], c.namespace, opens, m) if n in rename]
            else:
                continue
            if hits:
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
                       self._gone(i['name'], c, m, have, opens)]
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
        return edits


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


def _bundle_have(g, plan, names):
    pos, bimp, _ = _plan_index(plan)
    cl = _bundle_closure(bimp, [pos[n] for n in names])
    return {k for i in cl for k in plan['bundles'][i]['nodes']}


def gen_bundle(g, plan, name, collapse_mathlib=True):
    b = next(x for x in plan['bundles'] if x['name'] == name)
    keep = set(b['nodes'])
    bad = sorted(k for k in keep if g.nodes[k].sorry)
    if bad:
        raise CarveError('bundle %s would contain sorry: %s (repair the port first)' % (name, bad))
    avail = _bundle_have(g, plan, b['imports'])
    body = Carver(g).carve(keep, g.have_names(keep | avail), deprivatize=True,
                           rename=collision_renames(g))
    hdr = header(g, {g.nodes[k].module for k in keep}, b['imports'], (), collapse_mathlib)
    return hdr + '\n' + body.rstrip('\n') + '\n'


def gen_stub(g, plan, node, collapse_mathlib=True):
    bs = plan['stubs'][node]['bundles']
    avail = _bundle_have(g, plan, bs)
    body = Carver(g).carve({node}, g.have_names({node} | avail), sorry={node},
                           rename=collision_renames(g))
    hdr = header(g, {g.nodes[node].module}, bs, (), collapse_mathlib)
    return hdr + '\n' + body.rstrip('\n') + '\n'


def solution_tail(g, node):
    nd = g.nodes[node]
    lv = '.{%s}' % ', '.join(nd.univ) if nd.univ else ''
    full = pubname(node) + '_oai'
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
    for i in p['imports']:
        avail |= _bundle_have(g, plan, plan['stubs'][i]['bundles'])
    ren = collision_renames(g)
    ren[node] = pubname(node).rsplit('.', 1)[-1] + '_oai'
    body = Carver(g).carve(keep, g.have_names(keep | avail), rename=ren)
    hdr = header(g, {g.nodes[k].module for k in keep}, p['bundles'], p['imports'], collapse_mathlib)
    return hdr + '\n' + body.rstrip('\n') + '\n\n' + solution_tail(g, node)


def generate(g, plan, out, what=('bundles', 'stubs', 'pieces'), names=None, external=(),
             collapse_mathlib=True):
    """Write out/lib/Def_<bundle>.lean, out/lib/Thm_<slug>.lean (not for `external` nodes,
    published by someone else) and out/solutions/Sol_<slug>.lean. Returns {'files', 'sizes',
    'over_cap'} (files over prove2.me's 1 MiB cap)."""
    os.makedirs(os.path.join(out, 'lib'), exist_ok=True)
    os.makedirs(os.path.join(out, 'solutions'), exist_ok=True)
    files = []

    def put(path, txt):
        with open(path, 'w', encoding='utf-8') as f:
            f.write(txt)
        files.append(path)
    if 'bundles' in what:
        for b in plan['bundles']:
            if names is None or b['name'] in names:
                put(os.path.join(out, 'lib', 'Def_%s.lean' % b['name']),
                    gen_bundle(g, plan, b['name'], collapse_mathlib))
    for n in plan['nodes']:
        if names is not None and n not in names:
            continue
        if 'stubs' in what and n not in external:
            put(os.path.join(out, 'lib', 'Thm_%s.lean' % slug(n)), gen_stub(g, plan, n, collapse_mathlib))
        if 'pieces' in what:
            put(os.path.join(out, 'solutions', 'Sol_%s.lean' % slug(n)),
                gen_piece(g, plan, n, collapse_mathlib))
    sizes = {f: os.path.getsize(f) for f in files}
    return {'files': files, 'sizes': sizes, 'over_cap': [f for f, s in sizes.items() if s > SIZE_CAP]}
