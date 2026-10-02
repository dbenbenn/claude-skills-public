#!/usr/bin/env python3
"""Regenerate the scripts index in SKILL.md from the scripts' own docstrings.

usage: gen_index.py [--check]     (--check: exit 1 if SKILL.md's index is stale, write nothing)

Each row is a script's first docstring line; a library (no `__main__`) also names the scripts
that import it. The index sits between the `scripts-index` markers in SKILL.md and is never edited
by hand: tests/test_scripts_index.py fails when it is stale or when a runnable script has no
`usage:` line (either case), so a new script cannot go undocumented.
"""
import ast
import glob
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SKILL = os.path.join(os.path.dirname(HERE), 'SKILL.md')
BEGIN, END = '<!-- scripts-index:begin -->', '<!-- scripts-index:end -->'


def scripts():
    """[(name, first docstring line, runnable, docstring)] for every scripts/*.py."""
    out = []
    for f in sorted(glob.glob(os.path.join(HERE, '*.py'))):
        src = open(f, encoding='utf-8').read()
        doc = ast.get_docstring(ast.parse(src)) or ''
        para = ' '.join(doc.strip().split('\n\n')[0].split())
        m = re.match(r'(.+?[.?])(?=\s+[A-Z]|$)', para)    # not at "e.g." mid-sentence
        out.append((os.path.basename(f), m.group(1) if m else para,
                    bool(re.search(r'__name__\s*==\s*[\'"]__main__[\'"]', src)), doc))
    return out


def index():
    rows = ['| Script | What it does |', '|---|---|']
    srcs = {n: open(os.path.join(HERE, n), encoding='utf-8').read() for n, *_ in scripts()}
    for name, first, runnable, _ in scripts():
        what = first.replace('|', '\\|')
        if not runnable:
            mod = name[:-3]
            users = sorted(n for n, s in srcs.items() if n != name and re.search(
                r'^\s*(?:from %s import|import %s\b)' % (mod, mod), s, re.M))
            what += ' *(library; used by %s)*' % ', '.join('`%s`' % u for u in users) if users else ' *(library)*'
        rows.append('| `%s` | %s |' % (name, what))
    return '\n'.join(rows)


def main():
    text = open(SKILL, encoding='utf-8').read()
    if BEGIN not in text or END not in text:
        sys.exit('SKILL.md has no %s ... %s markers' % (BEGIN, END))
    a, b = text.index(BEGIN) + len(BEGIN), text.index(END)
    new = text[:a] + '\n' + index() + '\n' + text[b:]
    if '--check' in sys.argv[1:]:
        sys.exit(0 if new == text else 'SKILL.md scripts index is stale: run scripts/gen_index.py')
    open(SKILL, 'w', encoding='utf-8').write(new)
    print('index: %d scripts' % len(scripts()))


if __name__ == '__main__':
    main()
