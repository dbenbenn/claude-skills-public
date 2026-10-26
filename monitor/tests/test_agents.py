"""agents.py: safe file serving, summaries, phases, goals and the quota sampler."""
import json
import os

import agents as A

NOW = 1793010000


def rl(five, seven, r5=1793012400, r7=1793289600):
    return json.dumps({'type': 'rate_limit_event', 'rate_limit_info': {'unifiedWindows': {
        'five_hour': {'utilization': five, 'resetsAt': r5}, 'seven_day': {'utilization': seven, 'resetsAt': r7}}}}) + '\n'


def make_agent(root, name, state='running', ended=None, cost=1.5, key='none', transcript=''):
    d = root / name
    d.mkdir()
    (d / 'meta.json').write_text(json.dumps({'name': name, 'model': 'claude-sonnet-5-5', 'mode': 'dry'}))
    st = {'name': name, 'state': state, 'started': '2026-10-26T11:13:23+0100', 'apiKeySource': key,
          'model': 'claude-sonnet-5-5'}
    if ended:
        st['ended'] = ended
    (d / 'state.json').write_text(json.dumps(st))
    (d / 'usage.json').write_text(json.dumps({'estimated_cost_usd': cost, 'cost_is_exact': False}))
    (d / 'last_text.txt').write_text('patching\nthree sites')
    (d / 'transcript.jsonl').write_text(transcript)
    (d / 'brief.md').write_text('# brief')
    return d


# ---- path safety ----

def test_safe_path_allows_only_listed_files_in_plain_names(tmp_path):
    make_agent(tmp_path, 'a1')
    ok = A.safe_path(str(tmp_path), 'a1', 'transcript.jsonl')
    assert ok == str(tmp_path / 'a1' / 'transcript.jsonl')
    for name, f in (('a1', 'last_text.txt'), ('a1', '../a1/state.json'), ('a1', '/etc/passwd'), ('..', 'state.json'),
                    ('a1/..', 'state.json'), ('', 'state.json'), ('.hidden', 'state.json'), ('a1', 'unit.log'),
                    ('missing', 'state.json'), ('a1\x00', 'state.json')):
        assert A.safe_path(str(tmp_path), name, f) is None


def test_safe_path_rejects_symlinks_that_leave_the_agent_dir(tmp_path):
    d = make_agent(tmp_path, 'a1')
    secret = tmp_path / 'secret.txt'
    secret.write_text('x')
    (d / 'brief.md').unlink()
    (d / 'brief.md').symlink_to(secret)
    assert A.safe_path(str(tmp_path), 'a1', 'brief.md') is None
    (tmp_path / 'evil').symlink_to(d)                 # an agent name that is itself a link elsewhere
    outside = tmp_path / 'outside'
    outside.mkdir()
    (outside / 'state.json').write_text('{}')
    (tmp_path / 'link').symlink_to(outside)
    assert A.safe_path(str(tmp_path), 'link', 'state.json') is None


# ---- byte ranges ----

def test_read_range_whole_lines_only(tmp_path):
    p = tmp_path / 't.jsonl'
    p.write_bytes(b'one\ntwo\nthree\nfour-partial')
    data, s, e, size = A.read_range(str(p), 0)
    assert data == b'one\ntwo\nthree\n' and (s, e, size) == (0, 14, 26)
    data, s, e, _ = A.read_range(str(p), 14)           # polling from `end`: the partial line waits
    assert data == b'' and e == 14
    p.write_bytes(b'one\ntwo\nthree\nfour\n')
    data, s, e, _ = A.read_range(str(p), 14)
    assert data == b'four\n' and e == 19
    data, s, e, _ = A.read_range(str(p), -9)           # from the tail, beginning mid-line: skip to the next
    assert data == b'four\n' and s == 14


def test_read_range_cap_and_overlong_lines(tmp_path):
    p = tmp_path / 't.jsonl'
    p.write_bytes(b'aa\n' * 10)
    data, s, e, size = A.read_range(str(p), 0, limit=10)
    assert data == b'aa\naa\naa\n' and e == 9 and size == 30
    p.write_bytes(b'x' * 100 + b'\nok\n')
    data, s, e, _ = A.read_range(str(p), 0, limit=20)  # one line longer than the cap is skipped
    assert data == b'' and e == 20
    data, s, e, _ = A.read_range(str(p), e, limit=200)
    assert data == b'ok\n'


# ---- the summary ----

def test_agents_json_shape_grouping_and_auth(tmp_path):
    make_agent(tmp_path, 'run1')
    make_agent(tmp_path, 'run2', key='ANTHROPIC_API_KEY')
    make_agent(tmp_path, 'fin', state='done', ended='2026-10-26T11:20:00+0100')
    make_agent(tmp_path, 'old', state='done', ended='2026-10-20T11:20:00+0100')
    (tmp_path / 'queue').mkdir()                        # not an agent: no state.json
    now = A.parse_time('2026-10-26T12:00:00+0100')
    out = A.agents_json(str(tmp_path), now, jobs=str(tmp_path / 'nojobs'), ports=str(tmp_path / 'noports'))
    assert [r['name'] for r in out['running']] == ['run1', 'run2'] or [r['name'] for r in out['running']] == ['run2', 'run1']
    assert [r['name'] for r in out['recent']] == ['fin'] and out['hidden'] == 1
    r = {x['name']: x for x in out['running']}
    assert r['run1']['auth'] == 'subscription' and r['run2']['auth'] == 'key'
    one = r['run1']
    assert set(one) >= {'name', 'model', 'auth', 'state', 'started', 'ended', 'cost', 'cost_series', 'last_text',
                        'goals', 'phases'}
    assert one['last_text'] == 'patching three sites' and one['cost'] == 1.5 and one['phases'] is None
    json.dumps(out)


def test_goals_from_registry_by_batch_name():
    reg = {'batches': {'10': {'name': 'oaiq-010', 'modules': ['M.A']}, '11': {'name': 'oaiq-011', 'modules': ['M.B']}},
           'groups': {'M.A': {'goals': ['T.one', 'T.two'], 'ids': {'T.one': 'id-1'}}, 'M.B': {'goals': [], 'ids': {}}}}
    g = A.goals_for('oaiq-010', reg)
    assert g == [{'name': 'T.one', 'id': 'id-1', 'url': 'https://prove2.me/theorems/id-1'},
                 {'name': 'T.two', 'id': None, 'url': None}]
    assert A.goals_for('nobody', reg) == [] and A.goals_for('x', None) == []


def test_cost_history_records_changes_only(tmp_path):
    make_agent(tmp_path, 'a', cost=1.0)
    h = {'gone': [[1, 2]]}
    A.record_costs(h, str(tmp_path), NOW)
    A.record_costs(h, str(tmp_path), NOW + 30)
    (tmp_path / 'a' / 'usage.json').write_text(json.dumps({'estimated_cost_usd': 1.2}))
    A.record_costs(h, str(tmp_path), NOW + 60)
    assert h == {'a': [[NOW, 1.0], [NOW + 60, 1.2]]}
    A.record_costs(h, str(tmp_path), NOW + 3 * 86400)
    assert h['a'] == [[NOW + 3 * 86400, 1.2]] or h['a'][-1][1] == 1.2


# ---- phases ----

def test_pipeline_view_collapses_steps_into_stages():
    st = {'steps': {'fetch': {'status': 'done'}, 'filter_patches': {'status': 'skipped'}, 'port': {'status': 'done'},
                    'build': {'status': 'done'}, 'wsbuild': {'status': 'running'}}}
    v = A.pipeline_view(st)
    by = {s['name']: s['status'] for s in v['stages']}
    assert by['fetch'] == 'done' and by['port'] == 'done'
    assert by['build'] == 'running' and by['graph'] == 'pending' and v['current'] == 'build'
    assert [s['name'] for s in v['stages']][-1] == 'publish'
    st['steps']['wsbuild']['status'] = 'failed'
    assert A.pipeline_view(st)['current'] == 'build'
    assert A.pipeline_view({'steps': {'build': {'status': 'done'}}})['stages'][2]['status'] == 'partial'
    assert A.pipeline_view({})['current'] == 'fetch'


def test_phases_find_carve_dirs_and_count_live_items(tmp_path):
    jobs, ports = tmp_path / 'jobs', tmp_path / 'ports'
    t1 = jobs / 'ag' / 't1'
    (t1 / 'publish').mkdir(parents=True)
    (t1 / 'pipeline_state.json').write_text(json.dumps({'steps': {'fetch': {'status': 'done'}, 'publish': {'status': 'running'}}}))
    (t1 / 'publish' / 'run_state.json').write_text(json.dumps({
        'bundle:B': {'state': 'live'}, 'piece:P1': {'state': 'live'}, 'piece:P2': {'state': 'pending'},
        'statement:P1': {'state': 'live'}}))
    (ports / 'ag').mkdir(parents=True)
    (ports / 'ag' / 'pipeline_state.json').write_text(json.dumps({'steps': {'fetch': {'status': 'running'}}}))
    ph = A.phases_for('ag', str(jobs), str(ports))
    assert sorted(d['name'] for d in ph['dirs']) == ['ag', 't1']
    d = {x['name']: x for x in ph['dirs']}
    assert (d['t1']['live'], d['t1']['total']) == (2, 3) and d['t1']['current'] == 'publish'
    assert d['ag']['live'] is None
    assert A.phases_for('other', str(jobs), str(ports)) is None


# ---- quota ----

def test_quota_event_takes_last_and_survives_garbage():
    text = rl(0.1, 0.36) + 'not json rate_limit_event\n' + rl(0.11, 0.37)
    assert A.quota_event(text) == {'five_hour': (11.0, 1793012400), 'seven_day': (37.0, 1793289600)}
    assert A.quota_event('{"type":"assistant"}\n') is None
    assert A.quota_event('{"type":"rate_limit_event","rate_limit_info":{}}\n') is None


def test_update_quota_reads_only_new_bytes_and_prefers_newest_file(tmp_path):
    a = make_agent(tmp_path, 'a', transcript='{"type":"x"}\n' + rl(0.10, 0.30))
    b = make_agent(tmp_path, 'b', transcript=rl(0.50, 0.60))
    os.utime(a / 'transcript.jsonl', (NOW - 100, NOW - 100))
    os.utime(b / 'transcript.jsonl', (NOW - 200, NOW - 200))
    q = A.update_quota({}, str(tmp_path), NOW)
    assert q['series'] == [[NOW, 10.0, 1793012400, 30.0, 1793289600]]       # a was written later than b
    pos = dict(q['offsets'])
    A.update_quota(q, str(tmp_path), NOW + 30)
    assert q['offsets'] == pos and len(q['series']) == 1                     # nothing new: nothing read, no sample
    with open(a / 'transcript.jsonl', 'a') as f:
        f.write(rl(0.12, 0.31) + '{"type":"partial"')                        # an unfinished line is left unread
    A.update_quota(q, str(tmp_path), NOW + 60)
    assert q['series'][-1] == [NOW + 60, 12.0, 1793012400, 31.0, 1793289600]
    assert q['offsets'][str(a / 'transcript.jsonl')] < os.path.getsize(a / 'transcript.jsonl')
    A.update_quota(q, str(tmp_path), NOW + 8 * 86400)
    assert all(r[0] >= NOW + 86400 for r in q['series'])                     # 7 days kept
    (a / 'transcript.jsonl').unlink()
    A.update_quota(q, str(tmp_path), NOW + 8 * 86400 + 30)
    assert str(a / 'transcript.jsonl') not in q['offsets']


def test_update_quota_big_first_file_reads_only_the_tail(tmp_path):
    big = '{"type":"x","pad":"' + 'p' * 1000 + '"}\n'
    make_agent(tmp_path, 'a', transcript=rl(0.9, 0.9) + big * 600 + rl(0.2, 0.4))
    q = A.update_quota({}, str(tmp_path), NOW)
    assert q['series'][-1][1] == 20.0
