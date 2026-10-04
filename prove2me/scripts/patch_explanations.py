#!/usr/bin/env python3
"""PATCH proof explanations from files named by submission id, checking each one first.

usage: patch_explanations.py DIR [--go]

Every `DIR/**/<submission-id>.md` is one explanation (the file is the whole text). Each is checked
with p2mlib.explanation (statement display, length, pronouns, banned adjectives); a file that fails
is reported and skipped. A submission whose platform explanation already equals the file is
skipped. Without --go this only lists what it would do. With --go it PATCHes
/submissions/<id> and reads the submission back to confirm the stored text.

Written 2026-10-04 for the backfill of 190 accepted submissions that had no explanation
(p2m-standalone/maintenance/explanations). New submissions get theirs at submit time
(submit_solution.py --explanation, submit_all.py's MISSION_DIR/explanations/<name>.md).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
from p2mlib import explanation  # noqa: E402

SID = re.compile(r'^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$')


def targets(root):
    """[(submission id, path)] for every `<uuid>.md` under root, sorted by path."""
    out = []
    for d, _, files in os.walk(root):
        for f in files:
            if f.endswith('.md') and SID.match(f[:-3]):
                out.append((f[:-3], os.path.join(d, f)))
    return sorted(out, key=lambda t: t[1])


def main():
    args = sys.argv[1:]
    go = '--go' in args
    args = [a for a in args if a != '--go']
    if len(args) != 1:
        sys.exit(__doc__)
    from p2mlib import api
    todo = targets(args[0])
    bad = same = done = 0
    for sid, path in todo:
        text = open(path, encoding='utf-8').read().strip()
        probs = explanation.problems(text)
        if probs:
            bad += 1
            print('BAD   %s  %s' % (os.path.relpath(path, args[0]), '; '.join(probs)))
            continue
        cur = (api.call('GET', '/submissions/%s' % sid).get('explanation') or '').strip()
        if cur == text:
            same += 1
            continue
        if not go:
            print('WOULD %s  (%s)' % (os.path.relpath(path, args[0]), 'replace' if cur else 'new'))
            continue
        api.call('PATCH', '/submissions/%s' % sid, {'explanation': text})
        back = (api.call('GET', '/submissions/%s' % sid).get('explanation') or '').strip()
        if back != text:
            bad += 1
            print('FAIL  %s  stored text differs after PATCH' % os.path.relpath(path, args[0]))
            continue
        done += 1
        print('OK    %s' % os.path.relpath(path, args[0]))
    print('\n%d files: %d patched, %d already current, %d failed checks%s'
          % (len(todo), done, same, bad, '' if go else ' (dry run; --go to PATCH)'))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
