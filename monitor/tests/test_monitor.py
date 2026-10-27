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
        'I/O stalls 25% (full)', 'CPU stalls 60%', 'only 2.5 GiB of memory and swap free']
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


def at(hhmm, day=26):
    import datetime
    h, m = map(int, hhmm.split(':'))
    return datetime.datetime(2026, 10, day, h, m).timestamp()


def flags_file(tmp_path, *blocks):
    f = tmp_path / 'flags'
    f.write_text(''.join('=== 2026-10-%02d %s:00\n%s\n' % (day, hhmm, '\n'.join('FLAG: ' + l for l in lines))
                         for day, hhmm, lines in blocks))
    return str(f)


NUC = 'pid %d (/home/u/ws/Solutions/OAIQ019_Nuc/SOS.lean) at %d MiB'


def test_health_flags_merge_repeats_keep_the_peak_and_drop_the_old_day(tmp_path):
    f = flags_file(tmp_path, (25, '06:00', ['two Lean jobs race']),
                   (26, '16:47', [NUC % (11, 14284)]), (26, '16:57', [NUC % (11, 11759)]),
                   (26, '18:37', [NUC % (22, 14866)]))
    eps = M.health_flags(f, at('20:00'), home='/home/u')
    assert [(e['first'], e['last'], e['n']) for e in eps] == [(at('16:47'), at('16:57'), 2), (at('18:37'), at('18:37'), 1)]
    assert eps[0]['worst'] == 'pid 11 (~/ws/Solutions/OAIQ019_Nuc/SOS.lean) at 14284 MiB'
    assert eps[0]['text'] == 'pid 11 (~/ws/Solutions/OAIQ019_Nuc/SOS.lean) at 11759 MiB'
    assert not any(e['active'] for e in eps)
    assert M.health_flags(str(tmp_path / 'missing'), at('20:00')) == []


def test_health_flag_is_active_until_a_later_check_leaves_it_out(tmp_path):
    f = flags_file(tmp_path, (26, '21:27', ['Lean holds 19.3 of its 24.0 GiB of swap', 'Lean holds 24.0 of its 24.0 GiB of swap']))
    assert [e['active'] for e in M.health_flags(f, at('21:37'))] == [True]      # one episode, still the latest check
    assert [e['active'] for e in M.health_flags(f, at('21:47'))] == [False]     # the 21:37 check had no flag
    assert M.health_flags(f, at('21:47'))[0]['worst'] == 'Lean holds 24.0 of its 24.0 GiB of swap'


def test_race_is_active_while_both_jobs_run(tmp_path):
    f = flags_file(tmp_path, (26, '11:24', ["race: '/home/u/ws|Solutions.OAIQ12_ED.Edit_Defs' started by pid 7 (python3 x) while pid 5 is already on it (both still on it after 30 s)"]))
    running = {}
    def alive(pid, needle):
        assert needle == 'Edit_Defs'
        return pid in running
    running.update({'5': 1, '7': 1})
    assert M.health_flags(f, at('23:00'), alive=alive)[0]['active']
    del running['5']
    assert not M.health_flags(f, at('11:25'), alive=alive)[0]['active']


def test_oom_kill_is_active_for_an_hour(tmp_path):
    f = flags_file(tmp_path, (26, '10:00', ['1 Lean job(s) OOM-killed inside lean.slice since last check']))
    assert M.health_flags(f, at('10:59'))[0]['active']
    assert not M.health_flags(f, at('11:01'))[0]['active']


def test_machine_row_splits_memory_and_cpu_by_category():
    G = 2 ** 30
    meminfo = {'MemTotal': 64 * G, 'MemAvailable': 40 * G}
    procs = [{'pid': '1', 'cat': 'lean', 'anon': 4 * G, 'ticks': 100},
             {'pid': '2', 'cat': 'queue', 'anon': 2 * G, 'ticks': 50},
             {'pid': '3', 'cat': None, 'anon': 1 * G, 'ticks': 10}]
    row, prev = M.machine_row(1000, procs, meminfo, [1000, 500], None, ncpu=8)
    assert row['mem'] == {'lean': 4.0, 'queue': 2.0, 'claude': 0.0, 'rest': 18.0} and row['cpu'] is None
    procs[0]['ticks'] = 100 + 100 * 30          # one core for 30 s, at 100 ticks per second
    row, _ = M.machine_row(1030, procs, meminfo, [1000 + 800, 500 + 400], prev, ncpu=8, clk=100)
    assert row['cpu']['lean'] == 1.0 and row['cpu']['queue'] == 0.0
    assert row['cpu']['rest'] == 3.0             # 4 of 8 cores busy in all, minus Lean's 1


# 2026-10-27: the charts had one group per section, ~100 "Headless agent: oaiq-0NN" entries; now a few
# categories by where a process lives (dbenbenn): Lean, queue workers, Claude sessions, the rest.
UNIT = '0::/user.slice/user-1000.slice/user@1000.service/app.slice/%s\n'


def test_category_by_command_unit_and_ancestry():
    claude = '/home/u/.local/bin/claude --resume abc'
    assert M.category('lean -j1 Foo.lean', UNIT % 'headless-oaiq-031.service', []) == 'lean'
    assert M.category('/x/lake.orig env lean -R . F.lean', UNIT % 'lean.slice/run-p1-i2.scope', []) == 'lean'
    for unit in ('headless-oaiq-031.service', 'oai-queue.service', 'carve-f3faf27c0d.service'):
        assert M.category('python3 agent.py', UNIT % unit, []) == 'queue', unit
    # a headless agent's own claude process is queue work, not a Claude session
    assert M.category(claude, UNIT % 'headless-oaiq-031.service', []) == 'queue'
    assert M.category('rg foo', '0::/user.slice/user-1000.slice/session-2.scope\n', ['bash', claude, 'konsole']) == 'claude'
    assert M.category(claude, '0::/user.slice/user-1000.slice/session-2.scope\n', ['konsole']) == 'claude'
    v = '/home/u/.local/share/claude/versions/2.1.310 --print'
    assert M.category('node x.js', '0::/user.slice/user-1000.slice/session-2.scope\n', [v, 'bash']) == 'claude'
    assert M.category('plasmashell', '0::/user.slice/user-1000.slice/session-2.scope\n', ['systemd']) is None
    assert M.category('python3 monitor.py', '0::/system.slice/monitor.service\n', ['systemd']) is None


def test_old_rows_fold_into_the_categories():
    row = {'t': 1, 'mem': {'lean': 1.0, 'headless-oaiq-031': 0.5, 'oai-queue': 0.25, 'wifi-watch': 0.5, 'rest': 2.0},
           'cpu': {'lean': 1.0, 'headless-oaiq-031': 0.5, 'rest': 1.0}}
    M.fold_row(row)
    assert row['mem'] == {'lean': 1.0, 'queue': 0.75, 'claude': 0.5, 'rest': 2.0}
    assert row['cpu'] == {'lean': 1.0, 'queue': 0.5, 'claude': 0.0, 'rest': 1.0}


def test_inboxes_count_waiting_items(tmp_path):
    d = tmp_path / 'inbox'
    d.mkdir()
    (d / 'README.md').write_text('how to file')
    (d / 'a.md').write_text('x')
    (d / 'b.md').write_text('y')
    os.utime(d / 'a.md', (900, 900))
    cfg = tmp_path / 'inboxes.json'
    cfg.write_text(json.dumps([{'label': 'Lessons inbox', 'dir': str(d), 'ignore': ['README.md']},
                               {'label': 'Gone', 'dir': str(tmp_path / 'absent')}]))
    out = M.inboxes(str(cfg), 1000)
    assert out[0] == {'label': 'Lessons inbox', 'dir': str(d), 'count': 2, 'items': ['a.md', 'b.md'],
                      'oldest_s': 100}
    assert out[1]['count'] == 0 and out[1].get('missing')
    assert M.inboxes(str(tmp_path / 'none.json'), 1000) == []


def test_banner_is_for_the_machine_only(tmp_path):
    # the top banner is for machine trouble; a project's own alerts stay in its section
    h = str(tmp_path)
    S.publish('job', title='Job', alerts=['NEEDS A PERSON: B1'], home=h, now=100)
    secs, problems = M.load_sections(os.path.join(h, 'sections'), now=110)
    flags = [dict(text='x', worst='x', first=at('21:27'), last=at('21:27'), n=1, active=True),
             dict(text='y', worst='y!', first=at('16:47'), last=at('17:27'), n=5, active=False)]
    st = M.build_status(now=110, sections=secs, problems=problems + ['broken.json: bad'],
                        system={'machine': [], 'psi': [[110, 0, 0, 9, 0, 0]], 'free_gib': 20},
                        flags=flags, lean=[])
    assert st['alerts'] == ['memory stalls 9% (full)', 'Lean health: x (since 21:27)']
    assert st['cleared'] == [{'what': 'Lean health', 'text': 'y!', 'first': at('16:47'), 'last': at('17:27'), 'n': 5}]
    assert st['sections'][0]['alerts'] == ['NEEDS A PERSON: B1']
    assert st['problems'] == ['broken.json: bad']
    json.dumps(st)


def test_machine_trouble_moves_to_cleared_when_it_stops_and_back_when_it_returns():
    trouble = []
    def status(now, mem_full):
        return M.build_status(now=now, sections=[], problems=[], flags=[], lean=[], trouble=trouble,
                              system={'machine': [], 'psi': [[now, 0, 0, mem_full, 0, 0]], 'free_gib': 20})
    assert status(100, 12)['alerts'] == ['memory stalls 12% (full)']
    assert status(130, 9)['alerts'] == ['memory stalls 9% (full)']
    st = status(160, 0)
    assert st['alerts'] == [] and st['cleared'] == [
        {'what': 'machine', 'text': 'memory stalls 12% (full)', 'first': 100, 'last': 130, 'n': 2}]
    assert status(700, 7)['cleared'] == []                     # back within 10 min: the same episode
    assert status(730, 0)['cleared'][0]['first'] == 100
    assert status(100 + 86400 + 731, 0)['cleared'] == []      # forgotten after a day


def test_free_memory_alert_counts_swap():
    # with swap, little free RAM is normal under load; the alert is for RAM and swap both running out
    def alerts(**mem):
        return M.build_status(now=1, sections=[], problems=[], flags=[], lean=[],
                              system=dict({'machine': [], 'psi': []}, **mem))['alerts']
    assert alerts(free_gib=1.0, swap_free_gib=20.0) == []
    assert alerts(free_gib=1.0, swap_free_gib=2.0) == ['only 3.0 GiB of memory and swap free']
    assert alerts(free_gib=2.5) == ['only 2.5 GiB of memory and swap free']   # no swap


def test_cpu_of_lean_and_queue_comes_from_their_cgroups():
    # 2026-10-27: per-process ticks see only processes alive at both samples; most Lean compiles
    # live seconds, so lean.slice used 3.66 cores while the chart showed 1.01 and "rest" the other
    # 2.6. A cgroup's usage_usec counts its exited processes too.
    G = 2 ** 30
    meminfo = {'MemTotal': 64 * G, 'MemAvailable': 40 * G}
    procs = [{'pid': '1', 'cat': 'lean', 'anon': 4 * G, 'ticks': 100},
             {'pid': '2', 'cat': 'claude', 'anon': 1 * G, 'ticks': 0}]
    cg0 = {'lean': {'/lean.slice': 1_000_000}, 'queue': {'/a.service': 0, '/gone.service': 5_000_000}}
    row, prev = M.machine_row(1000, procs, meminfo, [1000, 500], None, ncpu=8, cg=cg0)
    procs[1]['ticks'] = 100 * 30                 # the session: one core by its own ticks
    cg1 = {'lean': {'/lean.slice': 1_000_000 + 90_000_000},           # 3 cores over 30 s
           'queue': {'/a.service': 15_000_000, '/new.service': 15_000_000}}   # a unit that started meanwhile
    row, _ = M.machine_row(1030, procs, meminfo, [1000 + 2400, 500 + 900], prev, ncpu=8, clk=100, cg=cg1)
    assert row['cpu']['lean'] == 3.0             # not the 0 its one long-lived process's ticks show
    assert row['cpu']['queue'] == 1.0            # a.service's 0.5 + the new unit's 0.5; a gone unit drops out
    assert row['cpu']['claude'] == 1.0
    assert row['cpu']['rest'] == 0.0             # 5 of 8 cores busy, all accounted for


def test_cgroup_usage_reads_lean_slice_and_queue_units(tmp_path):
    base = tmp_path / 'user@1000.service'
    for d, us in (('lean.slice', 7), ('app.slice/headless-oaiq-1.service', 3), ('app.slice/oai-queue.service', 2),
                  ('app.slice/carve-abc.service', 1), ('app.slice/konsole.service', 99)):
        (base / d).mkdir(parents=True)
        (base / d / 'cpu.stat').write_text('usage_usec %d\nuser_usec 0\n' % us)
    u = M.cgroup_usage(str(base))
    assert sum(u['lean'].values()) == 7 and sum(u['queue'].values()) == 6
