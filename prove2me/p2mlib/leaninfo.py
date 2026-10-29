"""What a Lean file contains, as Lean itself sees it: the Python side of lean/LeanInfo.lean.

    info = leaninfo.run('Foo.lean')                   # elaborate (needs the file's imports built)
    info = leaninfo.run('Foo.lean', parse_only=True)  # syntax only

`info.commands` are every command in order (kind, byte/line positions, namespace and opens in
force, attributes, declared names); `info.decls` every declaration a user wrote, with its range,
type, dependencies on this file's declarations (`uses_local`, auxiliary constants folded through)
and on our own published modules (`uses_imported`), and the index of the command holding it;
`info.messages` everything Lean said.

Positions are UTF-8 byte offsets into the file, so cut source text with `info.text_bytes[a:b]`
(see `Info.slice`), never with character indices.

Results are cached in ~/.cache/p2m/leaninfo, keyed by the file's content, the mode, LeanInfo.lean
itself and the modification times of the workspace modules the file imports directly.

LeanInfo runs compiled (`native_tool`): built once per LeanInfo.lean and toolchain into
~/.cache/p2m/leaninfo-bin/<key>/, it prints the same JSON as `lean --run LeanInfo.lean` without
re-elaborating and interpreting the tool on every call (2026-10-27: 3.0 s instead of 5.4 s CPU on a
small module, 17 s instead of 21 s on a large one, 6.8 instead of 8.7 GB). A failed build is
recorded there (FAILED) and the interpreted tool used instead; P2M_LEANINFO_INTERPRETED=1 forces it.
"""
import fcntl
import hashlib
import json
import os
import re
import shutil
import subprocess
from dataclasses import dataclass, field

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(os.path.dirname(HERE), 'lean', 'LeanInfo.lean')
CACHE = os.path.expanduser('~/.cache/p2m/leaninfo')
BIN_CACHE = os.path.expanduser('~/.cache/p2m/leaninfo-bin')

_LAKEFILE = """name = "leaninfo"
defaultTargets = ["leaninfo"]

[[lean_exe]]
name = "leaninfo"
root = "LeanInfo"
supportInterpreter = true
"""


def workspace():
    """The prove2.me Lean workspace: $P2M_WORKSPACE, else the known locations."""
    for p in (os.environ.get('P2M_WORKSPACE'), '~/claude/prove2me_workspace', '~/prove2me_workspace'):
        if p and os.path.isdir(os.path.expanduser(p)):
            return os.path.expanduser(p)
    raise SystemExit('prove2.me workspace not found; set P2M_WORKSPACE')


@dataclass
class Pos:
    line: int
    col: int
    byte: int


@dataclass
class Command:
    index: int
    kind: str                     # e.g. 'Lean.Parser.Command.declaration'
    start: Pos
    end: Pos
    namespace: str                # in force before the command ('' at the root)
    opens: list
    attrs: list
    names: list                   # declared names, from syntax
    inner_kind: str = None        # for `open … in` / `set_option … in`: the wrapped command's kind
    decl_kind: str = None         # for a declaration: theorem, definition, instance, structure, …
    value_start: Pos = None       # for a declaration with a value: where its `:=` (or `|`, `where`) starts
    # the scopes it sits in, outermost first: (index of the namespace/section command that opened
    # it, None for the file's root; [indices of the open/variable/universe/include/omit/set_option
    # commands elaborated in it before this command])
    context: list = field(default_factory=list)
    ids: list = field(default_factory=list)   # (start Pos, end Pos) of each declId, parallel to names
    # with run(idents=True) (LeanInfo --idents; byte offsets): every identifier with its role
    # ({'name', 'role', 'start', 'end'}; roles in lean/LeanInfo.lean), the `… in` wrapper heads
    # ({'kind', 'start', 'end'}), a `variable` command's binder groups ({'start', 'end', 'names'}),
    # and a declaration's doc comment and `private` keyword ({'start', 'end'} or None)
    idents: list = None
    heads: list = None
    binders: list = None
    doc: dict = None
    private: dict = None
    # with run(idents=True) in elaborate mode (lean/LeanInfo.lean, "--idents when elaborating"):
    # [[start, end, name]] what Lean resolved inside each identifier token ('' a local); the
    # instances its terms use that are not global library instances (`insts`; `sig_insts` those of
    # the statement, before the value); what instance search solved (`inst_keys`, 'Class Head …');
    # and [[name, class, [heads]]] the constants its declaration names bind (class '' unless an
    # instance)
    resolved: list = None
    insts: list = None
    sig_insts: list = None
    inst_keys: list = None
    declares: list = None
    used_keys: list = None        # 'Class Head …' of each class-typed constant of ours it uses
    sig_used_keys: list = None    # the same, for its statement
    declares_kinds: list = None   # syntax kinds a notation command adds
    kinds_used: list = None       # this file's notation kinds the command's syntax contains

    @property
    def short_kind(self):
        return self.kind.rsplit('.', 1)[-1]


@dataclass
class Decl:
    name: str
    private: bool
    kind: str                     # theorem, def, structure, inductive, axiom, constructor, ...
    start: Pos                    # includes doc comment and modifiers
    end: Pos
    selection: tuple              # (Pos, Pos) of the name
    type: str
    type_hash: int
    uses_local: list
    uses_imported: list           # [{'name', 'module'}], our modules only
    same_statement_as: list = field(default_factory=list)   # with run(candidates=...): published copies
    rests_on: list = field(default_factory=list)   # Theorems.* statements reached (stopping there)
    uses_sorry: bool = False                        # sorryAx reachable without passing through one
    statement_compared: bool = True                 # False: the --candidates comparison itself failed
    command: int = None           # index into Info.commands
    generated: bool = False       # made by Lean for another declaration (P.rec, P.casesOn, ...)

    @property
    def short(self):
        return self.name.rsplit('.', 1)[-1]


@dataclass
class Message:
    severity: str
    start: Pos
    end: Pos
    text: str


@dataclass
class Info:
    path: str
    mode: str
    commands: list
    decls: list
    messages: list
    text_bytes: bytes = field(repr=False, default=b'')

    def slice(self, a, b):
        return self.text_bytes[a:b].decode('utf-8')

    def decl(self, name):
        hit = [d for d in self.decls if d.name == name]
        return hit[0] if hit else None

    def command_span(self, i):
        """Byte span of command i including the trivia (comments, blank lines) up to the next
        command: what to cut to remove the command whole."""
        a = self.commands[i].start.byte
        b = self.commands[i + 1].start.byte if i + 1 < len(self.commands) else len(self.text_bytes)
        return a, b

    @property
    def errors(self):
        return [m for m in self.messages if m.severity == 'error']

    def unknown_identifiers(self):
        out = []
        for m in self.errors:
            hit = re.match(r'(?:Unknown identifier|unknown identifier|Unknown constant|unknown constant) [`\'](.+?)[`\']', m.text)
            if hit and hit.group(1) not in out:
                out.append(hit.group(1))
        return out


def _pos(j):
    return Pos(j['line'], j['col'], j['byte'])


def parse(data, text_bytes=b''):
    """An Info from LeanInfo's JSON (a dict)."""
    cmds = [Command(i, c['kind'], _pos(c['start']), _pos(c['end']), c['namespace'], c['opens'],
                    c['attrs'], c['names'], c.get('inner_kind'), (c.get('decl_kind') or '').rsplit('.', 1)[-1] or None,
                    _pos(c['value_start']) if c.get('value_start') else None,
                    [(x['opener'], x['cmds']) for x in c.get('context') or []],
                    [(_pos(x['start']), _pos(x['end'])) for x in c.get('ids') or []],
                    c.get('idents'), c.get('heads'), c.get('binders'), c.get('doc'), c.get('private'),
                    c.get('resolved'), c.get('insts'), c.get('sig_insts'), c.get('inst_keys'),
                    c.get('declares'), c.get('used_keys'), c.get('sig_used_keys'),
                    c.get('declares_kinds'), c.get('kinds_used'))
            for i, c in enumerate(data['commands'])]
    decls = []
    for d in data.get('decls') or []:
        x = Decl(d['name'], d['private'], d['kind'], _pos(d['range']['start']), _pos(d['range']['end']),
                 (_pos(d['selection']['start']), _pos(d['selection']['end'])), d['type'], d['type_hash'],
                 d['uses_local'], d['uses_imported'], d.get('same_statement_as') or [],
                 d.get('rests_on') or [], bool(d.get('uses_sorry')), d.get('statement_compared', True))
        for c in cmds:
            if c.start.byte <= x.start.byte <= c.end.byte:
                x.command = c.index
                x.generated = x.name not in c.names
                break
        decls.append(x)
    msgs = [Message(m['severity'], _pos(m['start']), _pos(m['end']), m['text']) for m in data['messages']]
    return Info(data['file'], data['mode'], cmds, decls, msgs, text_bytes)


def _key(path, parse_only, ws, candidates=(), idents=False, module=None, no_decls=False, options=()):
    h = hashlib.sha256()
    for o in options:
        h.update(('option:' + o).encode())
    if idents:
        h.update(b'idents')
    if module:
        h.update(('module:' + module).encode())
    if no_decls:
        h.update(b'no_decls')
    if candidates:
        h.update(('candidates:' + ','.join(candidates)).encode())
    h.update(open(TOOL, 'rb').read())
    h.update(open(path, 'rb').read())
    h.update(b'parse' if parse_only else b'elaborate')
    h.update(os.path.abspath(path).encode())
    tc = os.path.join(ws, 'lean-toolchain')
    if os.path.exists(tc):
        h.update(open(tc, 'rb').read())
    # a changed imported workspace module changes the result; Mathlib is pinned by the toolchain
    # ... and of the candidates imported beside them (copies.find: a statement published minutes
    # ago may not be built yet, Artin 2026-10-09)
    for mod in re.findall(r'^import\s+(\S+)', open(path, encoding='utf-8').read(), re.M) + list(candidates):
        f = os.path.join(ws, mod.replace('.', os.sep) + '.lean')
        if os.path.exists(f):
            st = os.stat(f)
            h.update(('%s:%d:%d' % (mod, st.st_mtime_ns, st.st_size)).encode())
            # and whether it is built: an unbuilt import fails the run, and building it later
            # leaves the .lean untouched (markov-heat-kernels 2026-10-04 served a stale failure)
            o = os.path.join(ws, '.lake', 'build', 'lib', 'lean', mod.replace('.', os.sep) + '.olean')
            if os.path.exists(o):
                so = os.stat(o)
                h.update(('olean:%d:%d' % (so.st_mtime_ns, so.st_size)).encode())
            else:
                h.update(b'olean:none')
    return h.hexdigest()


def _toolchain(ws):
    tc = os.path.join(ws, 'lean-toolchain')
    return open(tc).read() if os.path.exists(tc) else ''


def native_dir(ws):
    """Where the compiled LeanInfo for this LeanInfo.lean and the workspace's toolchain lives."""
    h = hashlib.sha256(open(TOOL, 'rb').read() + b'\0' + _toolchain(ws).encode() + _LAKEFILE.encode())
    return os.path.join(BIN_CACHE, h.hexdigest()[:20])


def native_tool(ws):
    """The compiled LeanInfo executable, built on first use (one builder at a time; ~20 s), or None
    to fall back to `lean --run` (the build failed before, or P2M_LEANINFO_INTERPRETED is set)."""
    if os.environ.get('P2M_LEANINFO_INTERPRETED'):
        return None
    d = native_dir(ws)
    exe = os.path.join(d, '.lake', 'build', 'bin', 'leaninfo')
    if os.access(exe, os.X_OK):
        return exe
    if os.path.exists(os.path.join(d, 'FAILED')):
        return None
    os.makedirs(BIN_CACHE, exist_ok=True)
    with open(d + '.lock', 'w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if os.access(exe, os.X_OK):
            return exe
        if os.path.exists(os.path.join(d, 'FAILED')):
            return None
        os.makedirs(d, exist_ok=True)
        shutil.copyfile(TOOL, os.path.join(d, 'LeanInfo.lean'))
        with open(os.path.join(d, 'lean-toolchain'), 'w') as f:
            f.write(_toolchain(ws))
        with open(os.path.join(d, 'lakefile.toml'), 'w') as f:
            f.write(_LAKEFILE)
        env = {k: v for k, v in os.environ.items() if k != 'LEAN_PATH'}
        try:
            r = subprocess.run(['lake', 'build'], cwd=d, env=env, capture_output=True, text=True, timeout=1800)
            ok, log = r.returncode == 0, (r.stdout or '') + (r.stderr or '')
        except (OSError, subprocess.SubprocessError) as e:
            ok, log = False, repr(e)
        if ok and os.access(exe, os.X_OK):
            return exe
        with open(os.path.join(d, 'FAILED'), 'w') as f:
            f.write(log[-4000:] or 'no executable after lake build')
        return None


def raw(path, parse_only=False, ws=None, timeout=3000, candidates=(), idents=False, module=None,
        no_decls=False, options=()):
    """LeanInfo's JSON for `path` as a dict, uncached (tests/record_fixtures.py records it)."""
    path = os.path.abspath(path)
    ws = ws or workspace()
    exe = native_tool(ws)
    tool = [exe] if exe else ['lean', '--run', TOOL]
    args = ['lake', 'env'] + tool + [path] + (['--parse-only'] if parse_only else []) + \
        (['--candidates', ','.join(candidates)] if candidates else []) + (['--idents'] if idents else []) + \
        (['--module', module] if module else []) + (['--no-decls'] if no_decls else []) + \
        ['-D' + o for o in options]
    r = subprocess.run(args, cwd=ws, capture_output=True, text=True, timeout=timeout)
    out = r.stdout.strip().split('\n')[-1] if r.stdout.strip() else ''
    try:
        return json.loads(out)
    except ValueError:
        raise RuntimeError('LeanInfo failed on %s:\n%s' % (path, (r.stdout + r.stderr)[-3000:]))


def run(path, parse_only=False, ws=None, use_cache=True, timeout=3000, candidates=(), idents=False,
        module=None, no_decls=False, options=()):
    """LeanInfo on `path`. `candidates`: published modules to import beside the file's own, so each
    theorem reports `same_statement_as` (elaborate mode; see lean/LeanInfo.lean). `idents`: every
    command also reports its identifiers by role, and when elaborating what Lean resolved them to
    and the instances it used (the carver's input). `module`: the file's module name (private
    names then read as in its .olean). `no_decls`: skip the per-declaration report. `options`:
    Lean options as `name=value` (`-D`), e.g. the build's autoImplicit=false."""
    path = os.path.abspath(path)
    ws = ws or workspace()
    text = open(path, 'rb').read()
    candidates = list(candidates)
    key = _key(path, parse_only, ws, candidates, idents, module, no_decls, options)
    cf = os.path.join(CACHE, key + '.json')
    if use_cache and os.path.exists(cf):
        return parse(json.load(open(cf)), text)
    data = raw(path, parse_only, ws, timeout, candidates, idents, module, no_decls, options)
    if use_cache:
        os.makedirs(CACHE, exist_ok=True)
        json.dump(data, open(cf, 'w'))
    return parse(data, text)


def is_cached(path, parse_only=False, ws=None, candidates=(), idents=False, module=None, no_decls=False,
              options=()):
    """Would run(path, ...) with these arguments be served from the cache?"""
    path = os.path.abspath(path)
    ws = ws or workspace()
    key = _key(path, parse_only, ws, list(candidates), idents, module, no_decls, options)
    return os.path.exists(os.path.join(CACHE, key + '.json'))


BUILD_OPTIONS = ('autoImplicit=false',)   # what the verifier and `lean -DautoImplicit=false` use


def build_module(path, module, olean, ilean, options=BUILD_OPTIONS, ws=None, timeout=3000):
    """Compile `path` as `module` into olean/ilean with the compiled LeanInfo, and cache the reading
    `carve.module_info` asks for (idents, no decls, these options) from the same elaboration, so
    `carve.py graph` does not elaborate the module again (2026-10-27). Returns (ok, build seconds,
    errors as `lean` prints them: FILE:LINE:COL: error: TEXT), or None without the compiled tool
    (then compile with `lean -o`). Nothing is written or cached when Lean reported an error."""
    path = os.path.abspath(path)
    ws = ws or workspace()
    exe = native_tool(ws)
    if not exe:
        return None
    # the key hashes the imports' builds as they are now (built before this module)
    key = _key(path, False, ws, (), True, module, True, options)
    for f in (olean, ilean):
        os.makedirs(os.path.dirname(os.path.abspath(f)), exist_ok=True)
    args = ['lake', 'env', exe, path, '--idents', '--module', module, '--no-decls'] + \
        ['-D' + o for o in options] + ['--olean', olean, '--ilean', ilean]
    # build_ms is the cost model's input, planned against the verifier's single thread: pin one thread
    # (lean-cap gives untimed calls two since 2026-10-28)
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    r = subprocess.run(args, cwd=ws, capture_output=True, text=True, timeout=timeout, env=env)
    out = r.stdout.strip().split('\n')[-1] if r.stdout.strip() else ''
    try:
        data = json.loads(out)
    except ValueError:
        tail = (r.stdout + r.stderr)[-2000:]
        return False, 0.0, ['%s:1:0: error: LeanInfo failed (exit %s): %s' % (path, r.returncode, tail)]
    secs = data.get('build_ms', 0) / 1000.0
    errs = ['%s:%d:%d: error: %s' % (path, m['start']['line'], m['start']['col'], m['text'])
            for m in data['messages'] if m['severity'] == 'error']
    if errs or r.returncode:
        for f in (olean, ilean):
            if os.path.exists(f):
                os.remove(f)
        return False, secs, errs or ['%s:1:0: error: LeanInfo exit %s' % (path, r.returncode)]
    os.makedirs(CACHE, exist_ok=True)
    with open(os.path.join(CACHE, key + '.json'), 'w') as f:
        json.dump(data, f)
    return True, secs, []
