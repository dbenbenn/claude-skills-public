#!/usr/bin/env python3
"""PATCH the natural-language statements of published items from reviewed Markdown files.

usage: patch_notes.py DIR [--go]

DIR holds ids.json ({name: theorem id}) and one folder per name with old.md (the live text when it
was fetched) and new.md (the reviewed replacement). A dry run prints what would change; --go PATCHes
each changed note and reads it back. It refuses when the live text is no longer old.md (edited since
it was fetched) or new.md carries an escaped quote. Notes of finished missions are patched from such a
folder (p2m-standalone/maintenance/...), never by editing the archived mission repo (2026-10-03,
bundle-note quote completion).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def norm(s):
    return (s or '').strip()


def run(d, go, call=None):
    if call is None:
        from p2m import call
    ids = json.load(open(os.path.join(d, 'ids.json'), encoding='utf-8'))
    todo = []
    for name, tid in ids.items():
        nf = os.path.join(d, name, 'new.md')
        if not os.path.exists(nf):
            continue
        new = open(nf, encoding='utf-8').read()
        old = open(os.path.join(d, name, 'old.md'), encoding='utf-8').read()
        if '\\"' in new:
            sys.exit('%s: new.md has an escaped quote' % name)
        live = call('GET', '/theorems/' + tid)
        live = (live.get('theorem', live) or {}).get('natural_language_statement')
        if norm(live) == norm(new):
            continue
        if norm(live) != norm(old):
            sys.exit('%s: the live text is no longer old.md; refetch and re-review before patching' % name)
        todo.append((name, tid, new))
    for name, tid, new in todo:
        if not go:
            print('would PATCH %s (%s)' % (name, tid))
            continue
        call('PATCH', '/theorems/' + tid, {'natural_language_statement': norm(new)})
        back = call('GET', '/theorems/' + tid)
        back = (back.get('theorem', back) or {}).get('natural_language_statement')
        if norm(back) != norm(new):
            sys.exit('%s: read-back differs after PATCH' % name)
        print('verified %s (%s)' % (name, tid))
    if not todo:
        print('nothing to patch')


if __name__ == '__main__':
    a = [x for x in sys.argv[1:] if not x.startswith('--')]
    if len(a) != 1:
        sys.exit(__doc__)
    run(a[0], '--go' in sys.argv)
