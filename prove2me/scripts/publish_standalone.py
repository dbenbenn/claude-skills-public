#!/usr/bin/env python3
"""Publish a folder's standalone statements (POST /submit-problem), wait for the jobs, record ids in
published_ids.json, and verify every published field against the folder.

usage: publish_standalone.py DIR [--dry]

DIR/mission.py supplies NAMESPACE, TAGS, THEOREMS [{name, page, result, ...}], PROSE {name: {title,
nls}}, src(page, result, extra, ref), and optionally DEFINITIONS [{name, title, nls, page, result[,
extra, tags]}] with code in DIR/lib/Def_<name>.lean, published first; DIR/lib/Thm_<name>.lean holds the statement (imports, then
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
    from p2mlib.mission import load
    M = load(here)
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
    defs = []
    for D in getattr(M, 'DEFINITIONS', []):
        defs.append({'definition_name': D['name'], 'definition_title': D['title'],
                     'definition': open(os.path.join(here, 'lib', 'Def_%s.lean' % D['name']), encoding='utf-8').read(),
                     'natural_language_statement': D['nls'],
                     'source': M.src(D['page'], D['result'], D.get('extra'), D.get('ref')),
                     'tags': D.get('tags', M.TAGS)})
    for d in defs:
        print('Def_' + d['definition_name']); print('   ', d['source'])
    for p in payloads:
        print(p['theorem_name']); print('   ', p['source'])
    if '--dry' in sys.argv:
        return
    ids_path = os.path.join(here, 'published_ids.json')
    ids = json.load(open(ids_path)) if os.path.exists(ids_path) else {}
    # definitions bundles first (POST /submit-definition, one per call): the statements import them
    # (Lodha–Moore positive-commutation bundle, 2026-10-02); recorded as Def_<name>
    for d in defs:
        key = 'Def_' + d['definition_name']
        if key in ids:
            continue
        r = call('POST', '/submit-definition', d)
        assert isinstance(r, dict) and '__error' not in r and r.get('job_id'), r
        while True:
            j = call('GET', '/publish-jobs/' + r['job_id'])
            if j.get('status') in ('PUBLISHED', 'FAILED', 'ERROR'):
                break
            time.sleep(8)
        assert j.get('status') == 'PUBLISHED', (key, j.get('status'), j.get('error_message'))
        ids[key] = j.get('theorem_id') or j.get('definition_id')
        json.dump(ids, open(ids_path, 'w'), indent=1)
    for d in defs:
        key = 'Def_' + d['definition_name']
        t = call('GET', '/theorems/' + ids[key]); t = t.get('theorem', t)
        nm = lambda x: ' '.join((x or '').split())
        bad = [k for k, tk in (('natural_language_statement', 'natural_language_statement'), ('source', 'source'),
                               ('definition_title', 'theorem_title')) if nm(t.get(tk)) != nm(d[k])]
        print('PUBLISHED %s %s %s  %s' % (key, ids[key], t.get('status'),
                                          'title/prose/source match' if not bad else 'MISMATCH: %s' % bad))
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
