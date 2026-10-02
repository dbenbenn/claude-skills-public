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
"""
import hashlib
import json
import os
import re
import subprocess
from dataclasses import dataclass, field

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.join(os.path.dirname(HERE), 'lean', 'LeanInfo.lean')
CACHE = os.path.expanduser('~/.cache/p2m/leaninfo')


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
                    c['attrs'], c['names'], c.get('inner_kind'), (c.get('decl_kind') or '').rsplit('.', 1)[-1] or None)
            for i, c in enumerate(data['commands'])]
    decls = []
    for d in data.get('decls') or []:
        x = Decl(d['name'], d['private'], d['kind'], _pos(d['range']['start']), _pos(d['range']['end']),
                 (_pos(d['selection']['start']), _pos(d['selection']['end'])), d['type'], d['type_hash'],
                 d['uses_local'], d['uses_imported'])
        for c in cmds:
            if c.start.byte <= x.start.byte <= c.end.byte:
                x.command = c.index
                x.generated = x.name not in c.names
                break
        decls.append(x)
    msgs = [Message(m['severity'], _pos(m['start']), _pos(m['end']), m['text']) for m in data['messages']]
    return Info(data['file'], data['mode'], cmds, decls, msgs, text_bytes)


def _key(path, parse_only, ws):
    h = hashlib.sha256()
    h.update(open(TOOL, 'rb').read())
    h.update(open(path, 'rb').read())
    h.update(b'parse' if parse_only else b'elaborate')
    h.update(os.path.abspath(path).encode())
    tc = os.path.join(ws, 'lean-toolchain')
    if os.path.exists(tc):
        h.update(open(tc, 'rb').read())
    # a changed imported workspace module changes the result; Mathlib is pinned by the toolchain
    for mod in re.findall(r'^import\s+(\S+)', open(path, encoding='utf-8').read(), re.M):
        f = os.path.join(ws, mod.replace('.', os.sep) + '.lean')
        if os.path.exists(f):
            st = os.stat(f)
            h.update(('%s:%d:%d' % (mod, st.st_mtime_ns, st.st_size)).encode())
    return h.hexdigest()


def run(path, parse_only=False, ws=None, use_cache=True, timeout=3000):
    path = os.path.abspath(path)
    ws = ws or workspace()
    text = open(path, 'rb').read()
    key = _key(path, parse_only, ws)
    cf = os.path.join(CACHE, key + '.json')
    if use_cache and os.path.exists(cf):
        return parse(json.load(open(cf)), text)
    args = ['lake', 'env', 'lean', '--run', TOOL, path] + (['--parse-only'] if parse_only else [])
    r = subprocess.run(args, cwd=ws, capture_output=True, text=True, timeout=timeout)
    out = r.stdout.strip().split('\n')[-1] if r.stdout.strip() else ''
    try:
        data = json.loads(out)
    except ValueError:
        raise RuntimeError('LeanInfo failed on %s:\n%s' % (path, (r.stdout + r.stderr)[-3000:]))
    if use_cache:
        os.makedirs(CACHE, exist_ok=True)
        json.dump(data, open(cf, 'w'))
    return parse(data, text)
