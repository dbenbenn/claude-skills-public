#!/usr/bin/env python3
"""Find gendered pronouns used for an author, in local mission prose or in live platform prose.

Why this exists: across four missions I wrote "his" for Wolf, Milnor, Rosenblatt and Chou and
"she" for Garrido, inferring pronouns from surnames every time. dbenbenn caught one by eye. A
surname does not establish anyone's pronouns, and the checklist already said to use the surname
or "the paper" — so the rule needed to be checkable, not remembered.

Use the surname, "the paper", or "they".

usage:
  check_pronouns.py local <dir> [<dir> ...]   # prose files (.md, .py) under each dir
  check_pronouns.py live [<name-substring>]   # my missions' live prose, via the API

`live` separates **patchable** fields from **frozen** ones: `formal_statement`, `preamble` and
definition code never change after publish, so a pronoun inside a Lean docstring is permanent.
That is a second reason to keep prose out of uploaded Lean and in the natural-language field.
"""
import os
import re
import sys

PRON = re.compile(r'(?<![\w-])(he|him|his|she|her|hers)(?![\w-])', re.I)
SKIP_DIRS = {'.git', '__pycache__', '.lake', 'worktrees', '.claude', 'readbacks_raw',
             'readbacks'}
FROZEN = {'formal_statement', 'preamble', 'definition'}


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
                    # the checker's own regex is not prose
                    if 'PRON' in line or 're.finditer' in line:
                        continue
                    # blank out inline code spans: `hE`, `he`, `his` are Lean identifiers,
                    # not pronouns, and a checker that cries wolf stops being read
                    line = re.sub(r'`[^`]*`', lambda m: ' ' * len(m.group(0)), line)
                    for m in PRON.finditer(line):
                        a = max(0, m.start() - 70)
                        hits.append((path, i, m.group(0),
                                     ' '.join(line[a:m.end() + 70].split())))
    return hits


def scan_live(substr):
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from p2m import call
    m = call('GET', '/missions?limit=200')
    missions = [x for x in (m.get('missions') or [])
                if substr.lower() in str(x.get('name')).lower()]
    rows = []

    def add(where, field, text):
        for mt in PRON.finditer(text or ''):
            a = max(0, mt.start() - 70)
            rows.append(('FROZEN' if field in FROZEN else 'PATCHABLE', field, where,
                         mt.group(0), ' '.join(text[a:mt.end() + 70].split())))

    for mis in missions:
        nm = str(mis.get('name'))
        add(nm, 'description', mis.get('description'))
        ms = call('GET', '/missions/%s/milestones?limit=100' % mis['id'])
        for row in (ms.get('milestones') or []):
            add(nm, 'milestone_title', row.get('title'))
            add(nm, 'milestone_description', row.get('milestone_description'))
            tid = (row.get('theorem') or {}).get('id')
            if not tid:
                continue
            t = call('GET', '/theorems/' + tid)
            t = t.get('theorem', t)
            for f in ('theorem_title', 'natural_language_statement', 'source',
                      'formal_statement', 'preamble'):
                add(t.get('theorem_name', '?'), f, t.get(f))
    return rows


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in ('local', 'live'):
        print(__doc__)
        sys.exit(2)
    if sys.argv[1] == 'local':
        hits = scan_local(sys.argv[2:] or ['.'])
        print('prose pronoun hits: %d' % len(hits))
        for path, i, word, ctx in hits:
            print('  %s:%d  %-5s %s' % (path, i, word, ctx[:130]))
        sys.exit(1 if hits else 0)

    rows = scan_live(sys.argv[2] if len(sys.argv) > 2 else '')
    patch = [r for r in rows if r[0] == 'PATCHABLE']
    print('live hits: %d   patchable: %d   frozen: %d'
          % (len(rows), len(patch), len(rows) - len(patch)))
    for kind, field, where, word, ctx in rows:
        print('  %-9s %-27s %-34s %-5s %s' % (kind, field, str(where)[:34], word, ctx[:100]))
    # only the patchable ones are actionable, so only they fail the check
    sys.exit(1 if patch else 0)


if __name__ == '__main__':
    main()
