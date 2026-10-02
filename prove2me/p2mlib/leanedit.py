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


def remove_commands(info, indices):
    """The source without the given commands (indices into info.commands).

    Each maximal run of removed commands goes with its trailing blank lines, and the kept text on
    either side is separated by the wider of the two separators the source had there (the one
    before the run and the one after it), so `def a`, two removed lines, blank, `/-! b -/` keeps
    its blank line instead of gluing `def a` to the doc comment."""
    drop = set(indices)
    t = info.text_bytes
    spans = _spans(info)
    out, cur, i = [], 0, 0
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
        cur, i = spans[j][1], j + 1
    out.append(t[cur:])
    return b''.join(out).decode('utf-8')


def replace_command(info, i, text):
    """The source with command i replaced by `text` (its trailing trivia kept)."""
    c = info.commands[i]
    t = info.text_bytes
    return (t[:c.start.byte] + text.encode('utf-8') + t[c.end.byte:]).decode('utf-8')


def insert_before(info, i, text):
    """The source with `text` inserted just before command i."""
    a = info.commands[i].start.byte
    t = info.text_bytes
    return (t[:a] + text.encode('utf-8') + t[a:]).decode('utf-8')


def command_of(info, name):
    """The index of the command declaring `name`, or None."""
    d = info.decl(name)
    if d is not None:
        return d.command
    for c in info.commands:
        if name in c.names:
            return c.index
    return None
