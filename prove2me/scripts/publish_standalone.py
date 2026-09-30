#!/usr/bin/env python3
"""Publish a folder's standalone statements (POST /submit-problem), wait for the jobs, record ids in
published_ids.json, and verify every published field against the folder.

usage: publish_standalone.py DIR [--dry]

DIR/mission.py supplies NAMESPACE, TAGS, THEOREMS [{name, page, result, ...}], PROSE {name: {title,
nls}} and src(page, result, extra, ref); DIR/lib/Thm_<name>.lean holds the statement (imports, then
the namespaced `theorem … := by sorry`). Already-published names (published_ids.json) are skipped,
so a rerun only verifies. Generalised 2026-09-30 from the per-folder publish.py of
p2m-standalone/t-finitely-presented and grigorchuk-growth.
"""
import json, os, sys, time

SK = os.path.dirname(os.path.abspath(__file__))


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    if len(args) != 1:
        sys.exit(__doc__)
    here = os.path.abspath(args[0])
    sys.path[:0] = [here, SK]
    from p2m import call
    import mission as M
    payloads = []
    for T in M.THEOREMS:
        src = open(os.path.join(here, 'lib', 'Thm_%s.lean' % T['name']), encoding='utf-8').read().split('\n')
        pre = '\n'.join(l for l in src if l.startswith('import '))
        body = '\n'.join(l for l in src if not l.startswith('import ')).strip() + '\n'
        P = M.PROSE[T['name']]
        payloads.append({'theorem_name': '%s.%s' % (T.get('namespace', M.NAMESPACE), T['name']),
                         'theorem_title': P['title'], 'formal_statement': body, 'preamble': pre,
                         'natural_language_statement': P['nls'],
                         'source': M.src(T['page'], T['result'], T.get('extra'), T.get('ref')),
                         'tags': T.get('tags', M.TAGS)})
    for p in payloads:
        print(p['theorem_name']); print('   ', p['source'])
    if '--dry' in sys.argv:
        return
    ids_path = os.path.join(here, 'published_ids.json')
    ids = json.load(open(ids_path)) if os.path.exists(ids_path) else {}
    todo = [p for p in payloads if p['theorem_name'] not in ids]
    if todo:
        r = call('POST', '/submit-problem', {'problems': todo})
        assert isinstance(r, dict) and '__error' not in r and r.get('jobs'), r
        for p, job in zip(todo, r['jobs']):
            while True:
                j = call('GET', '/publish-jobs/' + job['job_id'])
                if j.get('status') in ('PUBLISHED', 'FAILED', 'ERROR'):
                    break
                time.sleep(8)
            assert j.get('status') == 'PUBLISHED', (p['theorem_name'], j.get('status'), j.get('error_message'))
            ids[p['theorem_name']] = j['theorem_id']
            json.dump(ids, open(ids_path, 'w'), indent=1)
    norm = lambda x: ' '.join((x or '').split())
    for p in payloads:
        t = call('GET', '/theorems/' + ids[p['theorem_name']]); t = t.get('theorem', t)
        bad = [k for k in ('formal_statement', 'preamble', 'natural_language_statement', 'theorem_title', 'source')
               if norm(t.get(k)) != norm(p[k])]
        print('PUBLISHED %s %s %s  %s' % (p['theorem_name'], ids[p['theorem_name']], t.get('status'),
                                          'all fields match' if not bad else 'MISMATCH: %s' % bad))


if __name__ == '__main__':
    main()
