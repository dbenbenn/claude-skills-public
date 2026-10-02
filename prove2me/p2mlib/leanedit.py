"""Edit Lean source by the ranges Lean itself reports (`leaninfo`), never by regular expressions.

A command's span runs from its first token to the next command's first token, so it carries the
comments and blank lines after it and the spans tile the file: removing a command removes exactly
it (an `open X in` prefix goes with its declaration, a `section`/`variable`/`end` is its own
command), and nothing else moves."""


def _spans(info):
    return [info.command_span(i) for i in range(len(info.commands))]


def remove_commands(info, indices):
    """The source without the given commands (indices into info.commands)."""
    drop = set(indices)
    t = info.text_bytes
    out, cur = [], 0
    for i, (a, b) in enumerate(_spans(info)):
        if i in drop:
            out.append(t[cur:a]); cur = b
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
