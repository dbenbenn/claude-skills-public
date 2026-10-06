#!/usr/bin/env python3
"""Link the published theorems that a live mission's texts name by their full Lean names.

usage: link_mentions.py MISSION_ID [--repo MISSION_DIR] [--go]

Reads the mission's live description, every milestone description, and the notes (natural-language
statements) of the main theorem and of every milestone's theorem. Each full name in backticks
(`NS.name`) that the platform has published as a theorem becomes [`NS.name`](https://prove2.me/theorems/ID).
Left alone: a name that is not a published theorem (a definition, a Lean term), a mention already
linked, and a note's or milestone's mention of its own theorem.

A dry run lists what would change. --go PATCHes each changed text (notes through `/theorems/:id`,
milestone descriptions through `/milestones/:id`, the description through `/missions/:id`), reads it
back, and exits 1 on a mismatch. A rerun changes nothing. With --go, --repo also applies the rewrite to
MISSION_DIR/description.md and the bodies of MISSION_DIR/prose/*.md (not their front matter), so the
repository keeps matching what is live.

Run it after approval (the skill's "link the platform mentions"). Written 2026-10-06 for
Erschler–Zheng after the same edit had been made by hand for Moore, Lodha–Moore and the H(ℤ) notes.
"""
import argparse, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

URL = 'https://prove2.me/theorems/'
MENTION = re.compile(r"(?<!\[)`([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+)`")
FRONT = re.compile(r'\A(---\n.*?\n---[ \t]*\n)(.*)\Z', re.S)


def link_text(text, resolve, own=None):
    """(text with every resolvable mention linked, the names linked in order)."""
    linked = []

    def sub(m):
        name = m.group(1)
        if name == own:
            return m.group(0)
        tid = resolve(name)
        if not tid:
            return m.group(0)
        if name not in linked:
            linked.append(name)
        return '[`%s`](%s%s)' % (name, URL, tid)
    return MENTION.sub(sub, text or ''), linked


class Resolver:
    """Full theorem name -> published theorem id, or None; one lookup per name."""

    def __init__(self, call):
        self.call, self.cache = call, {}

    def __call__(self, name):
        if name not in self.cache:
            r = self.call('GET', '/theorems?theorem_name=' + name)
            hit = [t for t in ((r.get('theorems') or []) if isinstance(r, dict) else [])
                   if t.get('theorem_name') == name]
            self.cache[name] = (hit[0].get('theorem_id') or hit[0].get('id')) if hit else None
        return self.cache[name]


def _milestones(call, mission):
    out, off = [], 0
    while True:
        r = call('GET', '/missions/%s/milestones?limit=100&offset=%d' % (mission, off))
        page = (r.get('milestones') if isinstance(r, dict) else r) or []
        out += page
        if len(page) < 100:
            return out
        off += 100


def _tid(x):
    return (x.get('id') if isinstance(x, dict) else x) if x else None


def _theorem(call, tid):
    t = call('GET', '/theorems/' + tid)
    return t.get('theorem', t) if isinstance(t, dict) else {}


def _own_names(repo):
    """prose file stem -> full theorem name, from mission.py (an entry's own namespace wins)."""
    names, ns = {}, None
    try:
        sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        from p2mlib.mission import load
        m = load(repo)
        ns = m.NAMESPACE
        for T in getattr(m, 'THEOREMS', []):
            names[T['name']] = '%s.%s' % (T.get('namespace', ns), T['name'])
    except Exception:
        src = open(os.path.join(repo, 'mission.py'), encoding='utf-8').read()
        mm = re.search(r"NAMESPACE\s*=\s*['\"]([^'\"]+)", src)
        ns = mm.group(1) if mm else None
    return names, ns


def sync_repo(repo, resolve):
    names, ns = _own_names(repo)
    changed = []
    p = os.path.join(repo, 'description.md')
    if os.path.exists(p):
        s = open(p, encoding='utf-8').read()
        new, got = link_text(s, resolve)
        if new != s:
            open(p, 'w', encoding='utf-8').write(new)
            changed.append('description.md')
    pd = os.path.join(repo, 'prose')
    for f in sorted(os.listdir(pd)) if os.path.isdir(pd) else []:
        if not f.endswith('.md'):
            continue
        path = os.path.join(pd, f)
        s = open(path, encoding='utf-8').read()
        m = FRONT.match(s)
        head, body = (m.group(1), m.group(2)) if m else ('', s)
        stem = f[:-3]
        own = names.get(stem) or ('%s.%s' % (ns, stem) if ns else None)
        new, got = link_text(body, resolve, own)
        if new != body:
            open(path, 'w', encoding='utf-8').write(head + new)
            changed.append('prose/' + f)
    print('repo: %d file(s) rewritten' % len(changed))
    return changed


def run(mission, go=False, call=None, repo=None):
    if call is None:
        from p2m import call
    resolve = Resolver(call)
    ms_list = call('GET', '/missions?limit=100&mine=true')
    ms_list = ms_list.get('missions', ms_list) if isinstance(ms_list, dict) else ms_list
    mrec = next((m for m in ms_list or [] if m.get('id') == mission or m.get('id', '').startswith(mission)), None)
    if not mrec:
        sys.exit('mission %s not found among your missions' % mission)
    mid = mrec['id']
    todo = []      # (kind, id, label, new text, names linked)
    new, got = link_text(mrec.get('description'), resolve)
    if got:
        todo.append(('desc', mid, 'description', new, got))
    milestones = _milestones(call, mid)
    tids = [_tid(mrec.get('main_theorem'))] + [_tid(m.get('theorem')) or m.get('theorem_id') for m in milestones]
    names = {}
    for tid in [t for t in tids if t]:
        t = _theorem(call, tid)
        names[tid] = t.get('theorem_name')
        new, got = link_text(t.get('natural_language_statement'), resolve, names[tid])
        if got:
            todo.append(('thm', tid, 'note %s' % names[tid], new, got))
    for m in milestones:
        own = names.get(_tid(m.get('theorem')) or m.get('theorem_id'))
        new, got = link_text(m.get('milestone_description'), resolve, own)
        if got:
            todo.append(('ms', m['id'], 'milestone %s' % m.get('title', m['id'])[:60], new, got))
    for kind, i, label, new, got in todo:
        print('%s: links %s' % (label, ', '.join(got)))
    if not go:
        print('%d text(s) to change%s; dry run, --go to apply' % (len(todo), ' (and the repo files)' if repo else ''))
        return todo
    if repo:
        sync_repo(repo, resolve)
    bad = 0
    for kind, i, label, new, got in todo:
        if kind == 'thm':
            call('PATCH', '/theorems/' + i, {'natural_language_statement': new,
                                             'reason': 'link the theorems named in the note'})
            back = _theorem(call, i).get('natural_language_statement')
        elif kind == 'ms':
            call('PATCH', '/milestones/' + i, {'milestone_description': new,
                                               'reason': 'link the theorems named in the description'})
            back = next((m.get('milestone_description') for m in _milestones(call, mid) if m['id'] == i), None)
        else:
            call('PATCH', '/missions/' + i, {'description': new})
            r = call('GET', '/missions?limit=100&mine=true')
            r = r.get('missions', r) if isinstance(r, dict) else r
            back = next((m.get('description') for m in r if m.get('id') == i), None)
        ok = (back or '').strip() == new.strip()
        bad += not ok
        print('%s  %s' % ('OK ' if ok else 'BAD', label))
    if bad:
        sys.exit(1)
    return todo


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('mission')
    ap.add_argument('--repo')
    ap.add_argument('--go', action='store_true')
    a = ap.parse_args(argv)
    run(a.mission, a.go, repo=a.repo)


if __name__ == '__main__':
    main()
