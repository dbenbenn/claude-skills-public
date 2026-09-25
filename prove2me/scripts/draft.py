#!/usr/bin/env python3
"""Upload a mission proposal Draft from a repo, and verify the live Draft against it.

usage: draft.py MISSION_DIR verify
       draft.py MISSION_DIR upload [--go]        (dry run without --go)

Every mission used to carry its own upload_X.py and verify_X.py, each copied from the last and
edited; eleven verifiers across six repos, most of which only checked that a read-back was
non-empty, so a read-back filed on the wrong item passed. This is the one copy. A mission supplies
data, not code: MISSION_DIR/mission.py defines

  NAME, FIELDS (field ids), MISSION_TYPE ('ResearchPaper' | 'Textbook'), NAMESPACE ('Garrido')
  DEFINITIONS  [{name, title, nls, tags, page, result[, extra, ref]}]   code: lib/Def_<name>.lean
  THEOREMS     [{name, title, nls, tags, page, result, milestone_title, milestone_description, ...}]
  REFERENCES   [{theorem_id, theorem_name[, milestone_title, milestone_description]}]  (no title:
               an item only, e.g. an imported definition bundle)
  GOAL         the goal theorem's short name (never a milestone)
  src(page, result, extra=None, ref=None) -> the `source` string
  payloads()   -> {short_name: (preamble, formal_statement)}; extract_payloads() below does it
               for the usual layout (one statements file, bundles imported by use)

and the repo holds description.md, readbacks/<name>.readback.md (Def_<name> for a bundle), and
proposal.json (the proposal id and item ids, written by upload --go; never by a dry run).

`upload` is diff-based. It reads the live Draft first and re-posts only what differs, so an item
that has not changed is never touched and cannot lose a confirmation to a no-op edit. It creates
the proposal on the first run. `verify` compares every field the upload sets, flags live items
and milestones the repo does not have, and ends with `BAD <n>`; its exit status is n != 0.
"""
import importlib.util, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

READBACK_MODEL = 'claude-opus-5-5'
norm = lambda t: ' '.join((t or '').split())


def extract_payloads(path, namespace, bundles, opens=None):
    """{name: (preamble, formal_statement)} from a statements file of top-level `theorem`s inside
    `namespace <namespace>`. Each preamble imports Mathlib plus exactly the bundles whose
    identifiers its statement uses (bundles: {module: [identifier, ...]}) -- never a template,
    since a preamble freezes at publish and an unused import is a permanent false dependency."""
    text = open(path, encoding='utf-8').read()
    text = '\n'.join(l for l in text.split('\n') if not l.lstrip().startswith('--'))
    out = {}
    for part in re.split(r'^(?=theorem )', text, flags=re.M):
        m = re.match(r'theorem (\w+)', part)
        if not m:
            continue
        body = re.split(r'^end %s\s*$' % re.escape(namespace), part, flags=re.M)[0].strip()
        imports = ['import Mathlib'] + ['import ' + mod for mod, ids in bundles.items()
                                         if any(re.search(r'(?<![\w.])' + re.escape(i) + r'\b', body)
                                                for i in ids)]
        pre = '\n'.join(imports)
        used = sorted(o for o, toks in (opens or {}).items() if any(t in body for t in toks))
        if used:
            pre += '\nopen scoped ' + ' '.join(used)
        for u in sorted(set(re.findall(r'Type (u(?:_\d+)?\b|v\b|w\b)', body))):
            pre += '\nuniverse ' + u
        out[m.group(1)] = (pre, 'namespace %s\n\n%s\n\nend %s' % (namespace, body, namespace))
    return out


def load(mdir):
    spec = importlib.util.spec_from_file_location('mission', os.path.join(mdir, 'mission.py'))
    M = importlib.util.module_from_spec(spec)
    sys.path.insert(0, mdir)
    spec.loader.exec_module(M)
    return M


def desired(M, mdir):
    """What the Draft should contain, keyed the way proposal.json keys item ids."""
    rb = lambda n: open(os.path.join(mdir, 'readbacks', n + '.readback.md'), encoding='utf-8').read()
    pay = M.payloads()
    items = {}
    for D in M.DEFINITIONS:
        items[D['name']] = {
            'kind': 'definition', 'definition_name': D['name'], 'definition_title': D['title'],
            'definition': open(os.path.join(mdir, 'lib', 'Def_' + D['name'] + '.lean'), encoding='utf-8').read(),
            'natural_language_statement': D['nls'], 'tags': D['tags'],
            'source': M.src(D['page'], D['result'], D.get('extra'), D.get('ref')),
            'readback': rb('Def_' + D['name']), 'readback_model': READBACK_MODEL}
    for R in M.REFERENCES:
        items['ref:' + R['theorem_name']] = {'kind': 'reference', 'theorem_id': R['theorem_id']}
    for T in M.THEOREMS:
        pre, fs = pay[T['name']]
        items[T['name']] = {
            'kind': 'theorem', 'theorem_name': M.NAMESPACE + '.' + T['name'], 'theorem_title': T['title'],
            'preamble': pre, 'formal_statement': fs, 'natural_language_statement': T['nls'],
            'tags': T['tags'], 'source': M.src(T['page'], T['result'], T.get('extra'), T.get('ref')),
            'readback': rb(T['name']), 'readback_model': READBACK_MODEL}
    miles = {}
    for R in M.REFERENCES:
        # a referenced definition bundle is an item, not an attack target: no milestone_title
        if R.get('milestone_title'):
            miles['ref:' + R['theorem_name']] = (R['milestone_title'], R['milestone_description'])
    for T in M.THEOREMS:
        if T['name'] != M.GOAL:
            miles[T['name']] = (T['milestone_title'], T['milestone_description'])
    order = ([D['name'] for D in M.DEFINITIONS] + ['ref:' + R['theorem_name'] for R in M.REFERENCES]
             + [T['name'] for T in M.THEOREMS])
    desc = open(os.path.join(mdir, 'description.md'), encoding='utf-8').read()
    return items, miles, order, desc


# fields compared per kind; `kind`, `theorem_id` and `readback_model` are identity, not content
FIELDS = {'definition': ['definition_name', 'definition_title', 'definition', 'natural_language_statement',
                         'tags', 'source', 'readback'],
          'theorem': ['theorem_name', 'theorem_title', 'preamble', 'formal_statement',
                      'natural_language_statement', 'tags', 'source', 'readback'],
          'reference': []}


def live_value(it, f):
    v = it.get(f)
    if f == 'definition_title' and v is None:
        v = it.get('theorem_title')
    if f == 'definition_name' and v is None:
        v = it.get('theorem_name')
    return v


def same(a, b):
    if isinstance(a, list) or isinstance(b, list):
        return sorted(a or []) == sorted(b or [])
    return norm(a) == norm(b)


def diff(M, mdir, call, st):
    """[(key, what)] for everything that differs; also returns the live proposal."""
    items, miles, order, desc = desired(M, mdir)
    d = call('GET', '/mission-proposals/' + st['id'])
    d = d.get('proposal', d)
    live = {it['id']: it for it in d.get('items') or []}
    lm = {m['item_id']: m for m in (call('GET', '/mission-proposals/%s/milestones' % st['id']).get('milestones') or [])}
    bad = []
    ids = st.get('items', {})
    for k, want in items.items():
        it = live.get(ids.get(k))
        if it is None:
            bad.append((k, 'missing item')); continue
        for f in FIELDS[want['kind']]:
            if not same(live_value(it, f), want[f]):
                bad.append((k, f))
    for k, (t, dsc) in miles.items():
        m = lm.get(ids.get(k))
        if m is None:
            bad.append((k, 'missing milestone')); continue
        if not same(m.get('title') or m.get('milestone_title'), t):
            bad.append((k, 'milestone title'))
        if not same(m.get('description') or m.get('milestone_description'), dsc):
            bad.append((k, 'milestone description'))
    known = {ids.get(k) for k in items}
    for iid in live:
        if iid not in known:
            bad.append((iid, 'stray live item not in the repo'))
    for iid in lm:
        if iid not in {ids.get(k) for k in miles}:
            bad.append((iid, 'stray milestone (the goal, or an item the repo does not list)'))
    if not same(d.get('description'), desc):
        bad.append(('description', 'text'))
    if d.get('item_order') != [ids.get(k) for k in order]:
        bad.append(('item_order', 'order'))
    if d.get('main_item_id') != ids.get(M.GOAL):
        bad.append(('goal', 'main_item_id'))
    return bad, d, lm


def main():
    if len(sys.argv) < 3 or sys.argv[2] not in ('verify', 'upload'):
        sys.exit(__doc__)
    mdir, cmd, go = os.path.abspath(sys.argv[1]), sys.argv[2], '--go' in sys.argv[3:]
    M = load(mdir)
    from p2m import call
    stp = os.path.join(mdir, 'proposal.json')
    st = json.load(open(stp)) if os.path.exists(stp) else {}
    st.setdefault('items', {})

    if cmd == 'verify':
        if 'id' not in st:
            sys.exit('no proposal.json -- nothing uploaded yet')
        bad, d, lm = diff(M, mdir, call, st)
        for k, what in bad:
            print('BAD', k, what)
        print('items %d  milestones %d  status %s | BAD %d'
              % (len(d.get('items') or []), len(lm), d.get('status'), len(bad)))
        sys.exit(1 if bad else 0)

    items, miles, order, desc = desired(M, mdir)

    def do(m, p, b, what):
        if not go:
            print('   would %s %s  (%s)' % (m, p, what)); return {'id': 'dry'}
        r = call(m, p, b)
        if isinstance(r, dict) and '__error' in r:
            sys.exit('FAILED %s: %s' % (what, str(r['__error'])[:400]))
        return r

    def save():
        if go:
            json.dump(st, open(stp, 'w'), indent=1)

    if 'id' not in st:
        r = do('POST', '/mission-proposals', {'name': M.NAME, 'description': desc,
                                               'mission_type': M.MISSION_TYPE, 'field_ids': M.FIELDS}, 'create')
        if not go:
            print('dry run: would create the proposal and every item'); return
        st['id'] = r.get('id') or (r.get('proposal') or {}).get('id'); save()
        bad = [(k, 'missing item') for k in items] + [(k, 'missing milestone') for k in miles] \
            + [('item_order', ''), ('goal', '')]
    else:
        bad, _, _ = diff(M, mdir, call, st)
    MS = ('missing milestone', 'milestone title', 'milestone description')
    todo = {k for k, w in bad if w not in MS}              # items (and the proposal-level keys)
    ms_todo = {k for k, w in bad if w in MS}                # milestones, tracked separately so an
    pid = st['id']                                          # item edit never re-posts its milestone
    for k, want in items.items():
        if k in todo:
            r = do('POST', '/mission-proposals/%s/items' % pid, want, k)
            if go:
                st['items'][k] = r.get('id') or st['items'].get(k); save()
    for k, (t, dsc) in miles.items():
        if k in ms_todo:
            do('POST', '/mission-proposals/%s/milestones' % pid,
               {'item_id': st['items'].get(k), 'milestone_title': t, 'milestone_description': dsc}, 'milestone ' + k)
    if 'description' in todo:
        do('PATCH', '/mission-proposals/' + pid, {'description': desc}, 'description')
    if todo & {'item_order', 'goal'} or any(w == 'missing item' for _, w in bad):
        do('PATCH', '/mission-proposals/' + pid, {'item_order': [st['items'].get(k) for k in order]}, 'order')
        do('PATCH', '/mission-proposals/' + pid, {'main_item_id': st['items'].get(M.GOAL)}, 'goal')
    strays = [(k, w) for k, w in bad if w.startswith('stray')]
    for k, w in strays:
        print('   NOTE %s: %s -- not deleted; remove it deliberately if it should go' % (k, w))
    print('%s: %d difference(s)%s' % ('uploaded' if go else 'dry run', len(bad) - len(strays),
                                       '' if go else ' -- pass --go to apply'))


if __name__ == '__main__':
    main()
