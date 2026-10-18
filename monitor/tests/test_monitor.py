"""monitor.py: reading sections, history and rates, process grouping, pressure, alerts."""
import json
import os

import monitor as M
import section as S

PSI = {'cpu': 'some avg10=1.50 avg60=0.00 avg300=0.00 total=1\nfull avg10=0.00 avg60=0.00 avg300=0.00 total=0\n',
       'memory': 'some avg10=2.00 avg60=0.00 avg300=0.00 total=1\nfull avg10=6.25 avg60=0.00 avg300=0.00 total=1\n',
       'io': 'some avg10=4.00 avg60=0.00 avg300=0.00 total=1\nfull avg10=3.00 avg60=0.00 avg300=0.00 total=1\n'}


def test_parse_psi():
    assert M.parse_psi(PSI) == [1.5, 2.0, 6.25, 4.0, 3.0]
    assert M.parse_psi({'cpu': 'garbage'}) is None


def test_pressure_alerts():
    assert M.pressure_alerts([0, 0, 6.25, 0, 0], free_gib=30) == ['memory stalls 6% (full)']
    assert M.pressure_alerts([60, 0, 0, 0, 25], free_gib=2.5) == [
        'I/O stalls 25% (full)', 'CPU stalls 60%', 'only 2.5 GiB memory free']
    assert M.pressure_alerts(None, free_gib=None) == []


def test_classify_lean_first_then_sections():
    groups = [('erdos3-v2', [r'split_run\.py']), ('artin', [r'python3 .*artin'])]
    assert M.classify('/home/u/.elan/bin/lean Foo.lean', groups) == 'lean'
    assert M.classify('lake build Foo', groups) == 'lean'
    assert M.classify('python3 /x/split_run.py run.json --go', groups) == 'erdos3-v2'
    assert M.classify('python3 /y/artin/run.py', groups) == 'artin'
    assert M.classify('bash', groups) is None
    assert M.classify('python3 /x/leanblah.py', groups) is None


def test_load_sections_flags_stale_hides_expired_reports_malformed(tmp_path):
    h = str(tmp_path)
    S.publish('fresh', title='Fresh', home=h, now=1000)
    S.publish('quiet', title='Quiet', heartbeat_secs=60, home=h, now=1000)
    S.publish('old-done', title='Old', state='done', home=h, now=1000)
    S.publish('new-done', title='New', state='done', home=h, now=1000 + 86000)
    (tmp_path / 'sections' / 'broken.json').write_text('{not json')
    (tmp_path / 'sections' / 'notes.txt').write_text('ignored')
    secs, problems = M.load_sections(os.path.join(h, 'sections'), now=1000 + 86401)
    ids = [s['id'] for s in secs]
    assert 'old-done' not in ids and 'new-done' in ids
    by = {s['id']: s for s in secs}
    assert by['quiet']['stale'] and by['fresh']['stale']        # 3 heartbeats without an update
    assert not by['new-done']['stale']                          # finished sections are never stale
    assert len(problems) == 1 and 'broken.json' in problems[0]


def test_load_sections_orders_alerts_then_running_then_rest(tmp_path):
    h = str(tmp_path)
    S.publish('b-done', title='B', state='done', home=h, now=100)
    S.publish('a-run', title='A', home=h, now=100)
    S.publish('c-alert', title='C', state='waiting', alerts=['look'], home=h, now=100)
    secs, _ = M.load_sections(os.path.join(h, 'sections'), now=110)
    assert [s['id'] for s in secs] == ['c-alert', 'a-run', 'b-done']


def test_track_records_changes_and_estimates_rate():
    hist = {}
    sec = {'id': 's', 'phases': [{'name': 'P', 'done': 0, 'total': 100, 'state': 'running'}]}
    for t, d in ((0, 0), (30, 0), (600, 10), (1200, 20)):
        sec['phases'][0]['done'] = d
        M.track(hist, [sec], now=t)
    assert hist['s']['P'] == [[0, 0], [600, 10], [1200, 20]]   # unchanged samples are not stored
    p = sec['phases'][0]
    assert p['rate_per_min'] == 1.0 and p['eta'] == 1200 + 80 * 60


def test_track_forgets_sections_and_phases_that_left():
    hist = {'gone': {'P': [[0, 1]]}, 's': {'old': [[0, 1]]}}
    M.track(hist, [{'id': 's', 'phases': [{'name': 'new', 'done': 1, 'total': 2, 'state': 'running'}]}], now=10)
    assert 'gone' not in hist and 'old' not in hist['s'] and 'new' in hist['s']


def test_health_flags_last_day(tmp_path):
    f = tmp_path / 'flags'
    f.write_text('=== 2026-10-16 10:00:00\nFLAG: old\n=== 2026-10-18 06:00:00\nFLAG: two Lean jobs race\n')
    import datetime
    now = datetime.datetime(2026, 10, 18, 7, 0).timestamp()
    assert M.health_flags(str(f), now) == ['2026-10-18 06:00:00 FLAG: two Lean jobs race']
    assert M.health_flags(str(tmp_path / 'missing'), now) == []


def test_machine_row_splits_memory_and_cpu_by_group():
    G = 2 ** 30
    meminfo = {'MemTotal': 64 * G, 'MemAvailable': 40 * G}
    procs = [{'pid': '1', 'group': 'lean', 'anon': 4 * G, 'ticks': 100},
             {'pid': '2', 'group': 'job', 'anon': 2 * G, 'ticks': 50},
             {'pid': '3', 'group': None, 'anon': 1 * G, 'ticks': 10}]
    row, prev = M.machine_row(1000, procs, meminfo, [1000, 500], None, ncpu=8)
    assert row['mem'] == {'lean': 4.0, 'job': 2.0, 'rest': 18.0} and row['cpu'] is None
    procs[0]['ticks'] = 100 + 100 * 30          # one core for 30 s, at 100 ticks per second
    row, _ = M.machine_row(1030, procs, meminfo, [1000 + 800, 500 + 400], prev, ncpu=8, clk=100)
    assert row['cpu']['lean'] == 1.0 and row['cpu']['job'] == 0.0
    assert row['cpu']['rest'] == 3.0             # 4 of 8 cores busy in all, minus Lean's 1


def test_build_status_merges_alerts(tmp_path):
    h = str(tmp_path)
    S.publish('job', title='Job', alerts=['NEEDS A PERSON: B1'], home=h, now=100)
    secs, problems = M.load_sections(os.path.join(h, 'sections'), now=110)
    st = M.build_status(now=110, sections=secs, problems=problems + ['broken.json: bad'],
                        system={'machine': [], 'psi': [[110, 0, 0, 9, 0, 0]], 'free_gib': 20},
                        flags=['FLAG: x'], lean=[])
    assert st['alerts'] == ['memory stalls 9% (full)', 'Lean health: FLAG: x',
                            'Job: NEEDS A PERSON: B1', 'broken.json: bad']
    json.dumps(st)
