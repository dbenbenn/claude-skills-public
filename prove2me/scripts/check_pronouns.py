#!/usr/bin/env python3
"""Find gendered pronouns used for an author, in local mission prose or in live platform prose.

Why this exists: across four missions I wrote "his" for Wolf, Milnor, Rosenblatt and Chou and
"she" for Garrido, inferring pronouns from surnames every time. dbenbenn caught one by eye. A
surname does not establish anyone's pronouns, and the checklist already said to use the surname
or "the paper" — so the rule needed to be checkable, not remembered.

Use the surname, "the paper", or "they".

usage:
  check_pronouns.py local <dir> [<dir> ...]    # prose files (.md, .py) under each dir
  check_pronouns.py live --mine                # every mission you created
  check_pronouns.py live <name-substring>      # missions whose name contains this

`live` never scans the whole catalog: other captains' prose is not yours to edit, and a checker
that fails on it is a checker you learn to ignore. Pass `--mine` or a substring.

`live` separates **patchable** fields from **frozen** ones: `formal_statement`, `preamble` and
definition code never change after publish, so a pronoun inside a published Lean docstring is
permanent. That is a second reason to keep prose out of uploaded Lean and in the
natural-language field. Only patchable hits fail the check.

In a frozen Lean field only comments and docstrings are scanned, because a pronoun in Lean code
is an identifier (`hE`, `he`, `his`) rather than prose.
"""
import os
import re
import sys

PRON = re.compile(r'(?<![\w-])(he|him|his|she|her|hers)(?![\w-])', re.I)
SKIP_DIRS = {'.git', '__pycache__', '.lake', 'worktrees', '.claude', 'readbacks_raw',
             'readbacks'}
FROZEN = {'formal_statement', 'preamble', 'definition'}
CODE_SPAN = re.compile(r'`[^`]*`')
LEAN_PROSE = re.compile(r'/--(.*?)-/|/-(.*?)-/|--([^\n]*)', re.S)


def blank_code(line):
    return CODE_SPAN.sub(lambda m: ' ' * len(m.group(0)), line)


def lean_prose_only(text):
    """Keep only comment and docstring text, blanking the code around it."""
    out = [' '] * len(text)
    for m in LEAN_PROSE.finditer(text):
        for i in range(m.start(), m.end()):
            out[i] = text[i]
    return ''.join(out)


def scan_local(dirs):
    hits = []
    for root in dirs:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
            for fn in filenames:
                if not fn.endswith(('.md', '.py')):
                    continue
                path = os.path.join(dirpath, fn)
                try:
                    lines = open(path, encoding='utf-8').read().split('\n')
                except Exception:
                    continue
                for i, line in enumerate(lines, 1):
                    if 'PRON' in line or 're.finditer' in line:
                        continue          # the checker's own regex is not prose
                    for m in PRON.finditer(blank_code(line)):
                        a = max(0, m.start() - 70)
                        hits.append((path, i, m.group(0),
                                     ' '.join(line[a:m.end() + 70].split())))
    return hits


def scan_live(substr, mine):
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from p2m import call

    me = None
    if mine:
        s = call('GET', '/submissions?limit=1')
        subs = s.get('submissions') or s.get('data') or []
        me = subs[0].get('user_id') if subs else None
        if not me:
            raise SystemExit('could not determine your user id; pass a name substring instead')

    m = call('GET', '/missions?limit=200')
    missions = []
    for x in (m.get('missions') or []):
        if mine:
            if (x.get('creator') or {}).get('id') == me:
                missions.append(x)
        elif substr.lower() in str(x.get('name')).lower():
            missions.append(x)
    print('missions scanned: %d' % len(missions))

    rows = []

    def add(where, field, text):
        if not text:
            return
        hay = lean_prose_only(text) if field in FROZEN else text
        for mt in PRON.finditer(hay):
            a = max(0, mt.start() - 70)
            rows.append(('FROZEN' if field in FROZEN else 'PATCHABLE', field, where,
                         mt.group(0), ' '.join(text[a:mt.end() + 70].split())))

    for mis in missions:
        nm = str(mis.get('name'))
        add(nm, 'description', mis.get('description'))
        ms = call('GET', '/missions/%s/milestones?limit=100' % mis['id'])
        seen = set()
        for row in (ms.get('milestones') or []):
            add(nm, 'milestone_title', row.get('title'))
            add(nm, 'milestone_description', row.get('milestone_description'))
            tid = (row.get('theorem') or {}).get('id')
            if not tid or tid in seen:
                continue
            seen.add(tid)
            t = call('GET', '/theorems/' + tid)
            t = t.get('theorem', t)
            for f in ('theorem_title', 'natural_language_statement', 'source',
                      'formal_statement', 'preamble'):
                add(t.get('theorem_name', '?'), f, t.get(f))
    return rows


def main():
    a = sys.argv[1:]
    if not a or a[0] not in ('local', 'live'):
        print(__doc__)
        sys.exit(2)
    if a[0] == 'local':
        hits = scan_local(a[1:] or ['.'])
        print('prose pronoun hits: %d' % len(hits))
        for path, i, word, ctx in hits:
            print('  %s:%d  %-5s %s' % (path, i, word, ctx[:130]))
        sys.exit(1 if hits else 0)

    if len(a) < 2:
        print('live needs --mine or a mission-name substring; it will not scan the catalog.')
        sys.exit(2)
    rows = scan_live('' if a[1] == '--mine' else a[1], a[1] == '--mine')
    patch = [r for r in rows if r[0] == 'PATCHABLE']
    print('live hits: %d   patchable: %d   frozen: %d'
          % (len(rows), len(patch), len(rows) - len(patch)))
    for kind, field, where, word, ctx in rows:
        print('  %-9s %-27s %-34s %-5s %s' % (kind, field, str(where)[:34], word, ctx[:100]))
    sys.exit(1 if patch else 0)


if __name__ == '__main__':
    main()
