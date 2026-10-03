#!/usr/bin/env python3
"""Add milestones to a live mission, or edit one, from .md files; a dry run unless --go.

usage: live_milestones.py add MISSION_ID --after MILESTONE FILE.md [FILE.md ...] [--go]
       live_milestones.py edit MISSION_ID MILESTONE FILE.md --reason TEXT [--go]

MISSION_ID is the full id; MILESTONE a milestone id or a unique prefix of one.

FILE.md: a front matter with `title:` (the milestone title, starting with the source index) and,
for `add`, `theorem:` (the full name of the published theorem to link); the body is the milestone
description (the source's sentence in quotation marks first). For `edit`, an empty body leaves the
description as it is.

`add` inserts the files' milestones, in the order given, right after MILESTONE, and moves later
milestones down only as far as the reading order needs (`sort_order` is not logged in the milestone
history; title, description and link are). A file whose theorem a milestone of the mission already
links is skipped, so a rerun only verifies. `edit` PATCHes what differs, with the reason, which
solvers read in the milestone history.

Written 2026-10-03, when Garrido I and Chou gained their full-strength theorems as milestones; the
per-mission scripts it replaces (chou-mission/apply_milestone_prose.py and the like) kept their prose
in Python strings, which the skill no longer allows.
"""
import argparse, os, re, sys

SK = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SK)

FRONT = re.compile(r'\A---\n(.*?)\n---[ \t]*\n?(.*)\Z', re.S)


def read_spec(path):
    """{'title', 'description'[, 'theorem', ...]} from a front-matter .md file."""
    text = open(path, encoding='utf-8').read()
    m = FRONT.match(text)
    if not m:
        raise ValueError('%s: no front matter (---, title: ..., ---)' % path)
    spec = {}
    for line in m.group(1).split('\n'):
        if line.strip():
            k, _, v = line.partition(':')
            spec[k.strip()] = v.strip()
    if not spec.get('title'):
        raise ValueError('%s: no title' % path)
    spec['description'] = m.group(2).strip()
    return spec


def _order(ms):
    return sorted(ms, key=lambda m: (m['sort_order'], m['id']))      # the platform's order


def plan_insert(ms, after, k):
    """Sort orders for k milestones placed right after milestone `after`, and the moves
    [(id, old, new)] that keep every later milestone after them, in its reading order."""
    order = _order(ms)
    i = next((j for j, m in enumerate(order) if m['id'] == after), None)
    if i is None:
        raise KeyError(after)
    base = order[i]['sort_order']
    new = [base + 1 + j for j in range(k)]
    moves, prev = [], new[-1] if new else base
    for m in order[i + 1:]:
        want = max(prev + 1, m['sort_order'])
        if want != m['sort_order']:
            moves.append((m['id'], m['sort_order'], want))
        prev = want
    return new, moves


def linked_theorem_ids(ms):
    out = set()
    for m in ms:
        t = m.get('theorem')
        tid = (t.get('id') if isinstance(t, dict) else t) or m.get('theorem_id')
        if tid:
            out.add(tid)
    return out


def all_pages(fetch, limit=100):
    """Every item of a paged listing; `fetch(offset, limit)` returns one page. The milestone list
    pages at 20 by default, which once hid four of Garrido I's 24 milestones from the plan."""
    out, off = [], 0
    while True:
        page = fetch(off, limit) or []
        out += page
        off += len(page)
        if len(page) < limit:
            return out


def _milestones(mission):
    from p2m import call

    def fetch(off, limit):
        r = call('GET', '/missions/%s/milestones?limit=%d&offset=%d' % (mission, limit, off))
        return r.get('milestones') if isinstance(r, dict) else r
    return all_pages(fetch)


def _resolve(ms, prefix):
    hits = [m for m in ms if m['id'].startswith(prefix)]
    if len(hits) != 1:
        sys.exit('milestone %s: %d matches' % (prefix, len(hits)))
    return hits[0]


def add(a):
    from p2m import call
    from submit_solution import theorem_id
    ms = _milestones(a.mission)
    anchor = _resolve(ms, a.after)
    linked = linked_theorem_ids(ms)
    todo = []
    for f in a.files:
        s = read_spec(f)
        if not s.get('theorem'):
            sys.exit('%s: no theorem:' % f)
        if not s['description']:
            sys.exit('%s: no description' % f)
        if len(s['title']) > 200:
            sys.exit('%s: title over 200 characters' % f)
        tid = theorem_id(s['theorem'])
        if tid in linked:
            print('already linked, skipped: %s' % s['theorem'])
            continue
        todo.append((f, s, tid))
    if not todo:
        print('nothing to add')
        return
    new, moves = plan_insert(ms, anchor['id'], len(todo))
    print('after  %s  %s' % (anchor['id'][:8], anchor['title']))
    for (f, s, tid), so in zip(todo, new):
        print('  new  %3d  %s  -> %s' % (so, s['title'], s['theorem']))
    for mid, old, want in moves:
        print('  move %s  %d -> %d' % (mid[:8], old, want))
    if not a.go:
        print('dry run; --go to apply')
        return
    for mid, old, want in reversed(moves):
        call('PATCH', '/milestones/%s' % mid, {'sort_order': want})
    for (f, s, tid), so in zip(todo, new):
        call('POST', '/missions/%s/milestones' % a.mission,
             {'title': s['title'], 'milestone_description': s['description'], 'sort_order': so,
              'theorem_id': tid})
    after = _order(_milestones(a.mission))
    i = next(j for j, m in enumerate(after) if m['id'] == anchor['id'])
    bad = 0
    for k, (f, s, tid) in enumerate(todo):
        m = after[i + 1 + k] if i + 1 + k < len(after) else {}
        ok = (m.get('title') == s['title'] and (m.get('milestone_description') or '').strip() == s['description']
              and tid in linked_theorem_ids([m]))
        bad += not ok
        print('%s  %s' % ('OK ' if ok else 'BAD', s['title']))
    sys.exit(1 if bad else 0)


def edit(a):
    from p2m import call
    s = read_spec(a.file)
    m = _resolve(_milestones(a.mission), a.milestone)
    body = {}
    if s['title'] != m.get('title'):
        body['title'] = s['title']
        print('title: %s\n    -> %s' % (m.get('title'), s['title']))
    if s['description'] and s['description'] != (m.get('milestone_description') or '').strip():
        body['milestone_description'] = s['description']
        print('description changes (%d -> %d chars)' % (len(m.get('milestone_description') or ''),
                                                       len(s['description'])))
    if not body:
        print('no change: %s' % m['id'])
        return
    if not a.go:
        print('dry run; --go to apply')
        return
    body['reason'] = a.reason
    call('PATCH', '/milestones/%s' % m['id'], body)
    m2 = _resolve(_milestones(a.mission), m['id'])
    ok = m2.get('title') == s['title'] and (not s['description'] or
                                           (m2.get('milestone_description') or '').strip() == s['description'])
    print('%s  %s' % ('OK ' if ok else 'BAD', m['id']))
    sys.exit(0 if ok else 1)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('add')
    p.add_argument('mission')
    p.add_argument('--after', required=True)
    p.add_argument('files', nargs='+')
    p.add_argument('--go', action='store_true')
    p = sub.add_parser('edit')
    p.add_argument('mission')
    p.add_argument('milestone')
    p.add_argument('file')
    p.add_argument('--reason', required=True)
    p.add_argument('--go', action='store_true')
    a = ap.parse_args()
    (add if a.cmd == 'add' else edit)(a)


if __name__ == '__main__':
    main()
