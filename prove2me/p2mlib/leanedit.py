"""Edit Lean source by the ranges Lean itself reports (`leaninfo`), never by regular expressions.

A command's span runs from its first token to the next command's first token, so it carries the
comments and blank lines after it and the spans tile the file: removing a command removes exactly
it (an `open X in` prefix goes with its declaration, a `section`/`variable`/`end` is its own
command), and nothing else moves."""
import re


_LEAD = re.compile(rb'(?:^[ \t]*--[^\n]*\n)+\Z', re.M)


def _spans(info):
    """Removal spans: each command with the `--` comment block directly above it (no blank line
    between), up to the next command's. Lean attaches a comment to the previous token, so by
    Lean's ranges the comment introducing a declaration belongs to the one before it: removing
    that one took the next one's comment, and removing the commented one left its comment behind."""
    t = info.text_bytes
    cs = info.commands
    lead = []
    for i, c in enumerate(cs):
        gap_start = cs[i - 1].end.byte if i else c.start.byte
        m = _LEAD.search(t, gap_start, c.start.byte)
        # the block must start a line of its own and end exactly at the command
        lead.append(m.start() if m and m.end() == c.start.byte else c.start.byte)
    return [(lead[i], lead[i + 1] if i + 1 < len(cs) else len(t)) for i in range(len(cs))]


def _trailing_ws(b):
    return b[len(b.rstrip(b' \t\n')):]


def remove_commands(info, indices, a=None, b=None):
    """The source without the given commands (indices into info.commands); with byte bounds a, b,
    only that region of it (the commands' spans clipped to it).

    Each maximal run of removed commands goes with its trailing blank lines, and the kept text on
    either side is separated by the wider of the two separators the source had there (the one
    before the run and the one after it), so `def a`, two removed lines, blank, `/-! b -/` keeps
    its blank line instead of gluing `def a` to the doc comment."""
    drop = set(indices)
    t = info.text_bytes
    lo, hi = a or 0, len(t) if b is None else b
    spans = [(max(x, lo), min(y, hi)) for x, y in _spans(info)]
    spans = [(x, y) if x < y else (hi, hi) for x, y in spans]
    out, cur, i = [], lo, 0
    while i < len(spans):
        if i not in drop:
            i += 1
            continue
        j = i
        while j + 1 < len(spans) and j + 1 in drop:
            j += 1
        before = t[cur:spans[i][0]]
        w1, w2 = _trailing_ws(before), _trailing_ws(t[spans[j][0]:spans[j][1]])
        k = max(w1.count(b'\n'), w2.count(b'\n'))
        sep = (b'\n' * k + w2.rsplit(b'\n', 1)[-1]) if k else (w2 or w1)
        out.append(before[:len(before) - len(w1)] + sep)
        cur, i = max(cur, spans[j][1]), j + 1
    out.append(t[cur:hi])
    return b''.join(out).decode('utf-8')


def replace_command(info, i, text):
    """The source with command i replaced by `text` (its trailing trivia kept)."""
    c = info.commands[i]
    t = info.text_bytes
    return (t[:c.start.byte] + text.encode('utf-8') + t[c.end.byte:]).decode('utf-8')


def replace_commands(info, reps):
    """The source with each command i in `reps` ({i: text}) replaced, trailing trivia kept."""
    t = info.text_bytes
    out, cur = [], 0
    for i in sorted(reps):
        c = info.commands[i]
        out += [t[cur:c.start.byte], reps[i].encode('utf-8')]
        cur = c.end.byte
    out.append(t[cur:])
    return b''.join(out).decode('utf-8')


def insert_before(info, i, text):
    """The source with `text` inserted just before command i."""
    a = info.commands[i].start.byte
    t = info.text_bytes
    return (t[:a] + text.encode('utf-8') + t[a:]).decode('utf-8')


def text(info, i):
    """The source of command i (its own range: no trailing trivia)."""
    c = info.commands[i]
    return info.slice(c.start.byte, c.end.byte)


def closer(info, i):
    """The `end` that closes the namespace or section command i opened."""
    m = re.match(r'(?:namespace\s+(\S+)|(?:noncomputable\s+)?section(?:\s+(\S+))?)', text(info, i))
    name = m and (m.group(1) or m.group(2))
    return 'end' + (' ' + name if name else '')


def scope_wrap(info, i, top_level=False):
    """(prefix, suffix) that re-create, at the top level of any file, the scope command i sits in:
    an anonymous section holding the file's root-level context commands, then each enclosing
    namespace/section with the context commands elaborated in it (open, variable, universe,
    include, omit, set_option), and the matching `end`s. Nothing leaks out of the wrapper, and
    `open scoped`, `variable` and `section`-local options come along (Lean's own openDecls miss
    `open scoped`).

    `top_level`: declare at the top level instead (a `theorem solution` must not be namespaced:
    the verifier answers "Unknown identifier solution"). Each enclosing namespace is `open`ed where
    it was entered, so the context commands after it resolve their names as they did."""
    pre, post, ns = ['section'], ['end'], ''
    for opener, cmds in info.commands[i].context:
        # a plain `section` adds nothing but its context commands, which come anyway; a namespace
        # names what is declared in it, a `noncomputable section` changes elaboration
        o = text(info, opener) if opener is not None else ''
        if o.startswith('namespace'):
            ns = (ns + '.' if ns else '') + o.split()[1]
            if top_level:
                # opened where the namespace was entered, so the context commands after it (an
                # `attribute [local instance] polishSpace_P1`) resolve their names as they did
                pre.append('open %s' % ns)
            else:
                pre.append(o)
                post.insert(0, closer(info, opener))
        elif o.startswith('noncomputable'):
            pre.append(o)
            post.insert(0, closer(info, opener))
        pre += [text(info, k) for k in cmds]
    return '\n'.join(pre) + '\n', '\n'.join(post) + '\n'


def command_of(info, name):
    """The index of the command declaring `name`, or None."""
    d = info.decl(name)
    if d is not None:
        return d.command
    for c in info.commands:
        if name in c.names:
            return c.index
    return None
