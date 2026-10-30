"""p2mlib/carvemonitor.py: a carve's section on the machine monitoring page. Every test writes sections
under a tmp MONITOR_HOME (conftest), never the real page."""
import json
import os
import re
import shutil
import sys
import threading
import time

import pytest

from conftest import SCRIPTS
from p2mlib import carvemonitor as M, runlock

SKILLS = os.path.dirname(os.path.dirname(SCRIPTS))
SECTION_PY = os.path.join(SKILLS, 'monitor', 'section.py')
needs_monitor = pytest.mark.skipif(not os.path.isfile(SECTION_PY), reason='monitor skill not beside prove2me')


def wj(p, obj):
    os.makedirs(os.path.dirname(str(p)), exist_ok=True)
    with open(str(p), 'w') as f:
        json.dump(obj, f)


STEPS_DONE_TO = lambda last: {s: {'status': 'done', 'started': '2026-10-30T09:00:00', 'finished': '2026-10-30T09:01:00'}
                              for s in M._STEPS[:M._STEPS.index(last)]}


@pytest.fixture
def carve(tmp_path):
    """A carve in overlap mode, measuring its pieces while its bundles and statements publish."""
    d = tmp_path / 'openai-ports' / 'oaiq-123' / 'cc'
    d.mkdir(parents=True)
    wj(d / 'pipeline.json', {'folder': 'OAIQ123_CC', 'root_module': 'OAI.Foo.Main', 'targets': ['OAI.Foo.main'],
                             'bundle_prefix': 'B', 'overlap': True})
    steps = STEPS_DONE_TO('measure_pieces')
    steps['measure_pieces'] = {'status': 'running', 'started': '2026-10-30T10:26:57'}
    wj(d / 'pipeline_state.json', {'steps': steps, 'replans': 1})
    (d / 'build.log').write_text('✔ [1/3] Replayed Solutions.OAIQ123_CC.A\n✖ [2/3] FAILED Solutions.OAIQ123_CC.B (1.0s)\n'
                                 '✔ [3/3] Built Solutions.OAIQ123_CC.Main (2.0s)\n')
    wj(d / 'config.json', {'work': str(d / 'work'), 'external': ['OAI.Foo.main']})
    plan = {'bundles': [{'name': 'B0'}, {'name': 'B1'}], 'stubs': {'S1': {}, 'S2': {}, 'OAI.Foo.main': {}},
            'pieces': {'S1': {}, 'S2': {}, 'OAI.Foo.main': {}}, 'external': []}
    wj(d / 'work' / 'plan.json', plan)
    wj(d / 'work' / 'times.json', {'bundle:B0': {'ok': True, 'secs': 3}, 'bundle:B1': {'ok': True, 'secs': 3},
                                   'statement:S1': {'ok': True}, 'statement:S2': {'ok': False},
                                   'statement:OLD': {'ok': True}, 'piece:S1': {'ok': True}})
    (d / 'logs').mkdir()
    (d / 'logs' / 'measure_pieces.log').write_text(
        '==== 2026-10-30T08:00:00 measure_pieces (skill a)\npiece      1.0 s ok S1 \npiece      1.0 s ok S2 \n'
        '==== 2026-10-30T10:26:58 measure_pieces (skill b)\n$ python3 carve_measure.py config.json --kinds piece\n'
        'piece       29.5 s FAIL S1 some error\npiece       29.5 s ok S1 \n  edge  USED S1 -> X\n')
    pub = dict(plan, external=['OAI.Foo.main'])
    wj(d / 'publish' / 'plan.json', pub)
    wj(d / 'publish' / 'run_state.json', {'bundle:B0': {'state': 'live'}, 'bundle:B1': {'state': 'inflight'},
                                          'statement:S1': {'state': 'live'}, 'statement:S2': {'state': 'stop'},
                                          'piece:S1': {'state': 'todo'}})
    return d


def phase(sec, name):
    return next(p for p in sec['phases'] if p['name'] == name)


def test_section_id_is_the_units_hash(carve):
    import carve_pipeline
    assert M.section_id(str(carve)) == carve_pipeline.unit_name(str(carve))
    assert re.fullmatch(r'carve-[0-9a-f]{10}', M.section_id(str(carve)))


def test_worker_of_both_layouts(tmp_path):
    assert M.worker_of('/home/u/claude/p2m-standalone/openai-ports/oaiq-011') == 'oaiq-011'
    assert M.worker_of('/home/u/claude/p2m-standalone/openai-ports/oaiq-081/sat') == 'oaiq-081'
    assert M.worker_of('/home/u/.claude/jobs/oaiq-107/cc') == 'oaiq-107'
    assert M.worker_of(str(tmp_path / 'somewhere' / 'carve')) is None


def test_compose_reads_steps_build_measure_and_publish(carve):
    sec = M.Reporter(str(carve), go=True, lib=False).compose()
    assert sec['state'] == 'running'
    assert sec['title'].startswith('oaiq-123 carve ') and sec['title'].endswith(': OAI.Foo.Main')
    assert 'oaiq-123' in sec['owner'] and M.section_id(str(carve)) in sec['owner']
    assert sec['note'].startswith('step measure_pieces (21 of 24), since 10:26') and 're-plans 1' in sec['note']
    st = phase(sec, 'Steps')
    assert (st['done'], st['total'], st['state']) == (20, 24, 'running')
    b = phase(sec, 'Build (modules)')
    assert (b['done'], b['total'], b['state']) == (3, 3, 'done') and '1 failed' in b['note']
    m = phase(sec, 'Measure bundles+statements')          # done: from times.json, planned items only
    assert (m['done'], m['total'], m['state']) == (4, 4, 'done') and '1 failed' in m['note']
    p = phase(sec, 'Measure pieces')                      # running: this run's log lines, the last result each
    assert (p['done'], p['total'], p['state']) == (1, 2, 'running') and 'failed' not in p['note']
    pub = phase(sec, 'Publish (live)')
    assert (pub['done'], pub['total']) == (2, 6)
    assert '1 in flight' in pub['note'] and '1 stopped' in pub['note'] and 'held until released' in pub['note']
    assert sec['alerts'] == []


@needs_monitor
def test_composed_section_is_valid_for_the_monitor(carve, tmp_path):
    lib = M.section_lib()
    assert lib is not None
    r = M.Reporter(str(carve), go=True, lib=lib, home=str(tmp_path / 'mon'))
    assert r.refresh()
    sec = json.load(open(lib.path_of(r.sid, str(tmp_path / 'mon'))))
    assert lib.validate(sec) == []
    assert sec['heartbeat_secs'] >= 3 * M.INTERVAL


def test_running_step_with_leaninfo_progress_gets_its_own_phase(carve):
    wj(carve / 'pipeline_state.json', {'steps': dict(STEPS_DONE_TO('graph'), graph={'status': 'running'})})
    (carve / 'logs' / 'graph.log').write_text('==== t graph (skill a)\nLeanInfo 7/94 Solutions.X.A\nLeanInfo 8/94 Solutions.X.B\n')
    sec = M.Reporter(str(carve), lib=False).compose()
    g = phase(sec, 'Graph (modules)')
    assert (g['done'], g['total'], g['state']) == (8, 94, 'running')


def test_without_publish_the_publishing_steps_are_not_counted(carve):
    sec = M.Reporter(str(carve), go=False, lib=False).compose()
    assert phase(sec, 'Steps')['total'] == 22


def test_classic_carve_measures_everything_in_one_phase(carve):
    p = json.load(open(carve / 'pipeline.json'))
    p.pop('overlap')
    wj(carve / 'pipeline.json', p)
    wj(carve / 'pipeline_state.json', {'steps': dict(STEPS_DONE_TO('measure'), measure={'status': 'running'})})
    (carve / 'logs' / 'measure.log').write_text('==== t measure (skill a)\nbundle      3.0 s ok B0 \nstatement   1.0 s ok S1 \n')
    sec = M.Reporter(str(carve), lib=False).compose()
    m = phase(sec, 'Measure')
    assert (m['done'], m['total']) == (2, 6) and m['note'] == 'bundles 1/2, statements 1/2, pieces 0/2'
    assert phase(sec, 'Steps')['total'] == 20


def cmdlines(d, folder='OAIQ123_CC'):
    return {
        'driver': ['/run/current-system/sw/bin/python3 /home/u/.cache/p2m/skill/abc/prove2me/scripts/carve_pipeline.py %s --publish' % d,
                   '/bin/sh -c /usr/bin/python3 /x/carve_pipeline.py %s --publish >> %s/logs/driver.log 2>&1; echo' % (d, d)],
        'publisher': ['/bin/sh -c /usr/bin/python3 /x/prove2me/scripts/split_run.py publish/run_early.json --go >> '
                      '%s/logs/publish_early.log 2>&1; echo "== publisher exit $?" >> %s/logs/publish_early.log' % (d, d)],
        'lean': ['/home/u/.elan/toolchains/v/bin/lean -j1 -DautoImplicit=false -R %s/stage -o %s/olean/EdgeChk/Chk_X.olean' % (d, d),
                 '/home/u/.cache/p2m/leaninfo-bin/h/.lake/build/bin/leaninfo /home/u/ws/Solutions/%s/Main.lean --idents' % folder,
                 '/home/u/.elan/toolchains/v/bin/lake env /home/u/.cache/leaninfo /home/u/ws/Solutions/%s/A.lean' % folder],
        'none': ['/usr/bin/python3 /x/carve_pipeline.py %s --wait 100' % d,
                 '/usr/bin/python3 /x/carve_pipeline.py %s-other --publish' % d,
                 '/home/u/.elan/toolchains/v/bin/lean -R /home/u/other/stage -o /home/u/other/olean/X.olean',
                 '/home/u/.cache/leaninfo /home/u/ws/Solutions/%s2/Main.lean' % folder],
    }


def test_processes_match_this_carves_driver_publisher_and_lean_only(carve):
    procs = M.Carve(str(carve)).processes()
    for label, lines in cmdlines(str(carve)).items():
        for line in lines:
            got = [p['label'] for p in procs if re.search(p['match'], line)]
            assert got == ([] if label == 'none' else [label]), (label, line, got)


@needs_monitor
def test_reporter_publishes_at_start_and_marks_the_end(carve, tmp_path):
    home = str(tmp_path / 'mon')
    r = M.Reporter(str(carve), go=True, lib=M.section_lib(), home=home, interval=3600, poll=0.05).start()
    f = os.path.join(home, 'sections', r.sid + '.json')
    try:
        assert json.load(open(f))['state'] == 'running'
        assert r._thread.daemon and r._thread.is_alive()
    finally:
        r.finish('failed', 'stopped at calibrate_pieces: 3 pieces over')
    sec = json.load(open(f))
    assert sec['state'] == 'failed' and sec['note'] == 'stopped at calibrate_pieces: 3 pieces over'
    assert sec['alerts'] == ['stopped at calibrate_pieces: 3 pieces over']
    assert phase(sec, 'Steps')['state'] == 'failed'
    assert not r._thread.is_alive()
    r.finish('done', 'again')                       # a second finish changes nothing
    assert json.load(open(f))['state'] == 'failed'


@needs_monitor
def test_a_step_boundary_refreshes_at_once(carve, tmp_path):
    home = str(tmp_path / 'mon')
    r = M.Reporter(str(carve), go=True, lib=M.section_lib(), home=home, interval=3600, poll=0.02).start()
    f = os.path.join(home, 'sections', r.sid + '.json')
    try:
        st = json.load(open(carve / 'pipeline_state.json'))
        st['steps']['measure_pieces']['status'] = 'done'
        st['steps']['calibrate_pieces'] = {'status': 'running', 'started': '2026-10-30T11:00:00'}
        time.sleep(0.01)
        wj(carve / 'pipeline_state.json', st)
        deadline = time.time() + 5
        while time.time() < deadline and 'calibrate_pieces' not in json.load(open(f))['note']:
            time.sleep(0.02)
        assert json.load(open(f))['note'].startswith('step calibrate_pieces')
    finally:
        r.finish('done', 'x')


def test_no_monitor_skill_is_a_silent_no_op(carve, monkeypatch, tmp_path):
    monkeypatch.setenv('P2M_MONITOR_SECTION', str(tmp_path / 'absent' / 'section.py'))
    assert M.section_lib() is None
    monkeypatch.setenv('P2M_MONITOR_SECTION', '')
    assert M.section_lib() is None
    r = M.Reporter(str(carve)).start()
    assert r.lib is None and r._thread is None
    assert r.refresh() is False
    r.finish('done', 'x')


def test_a_failing_monitor_never_raises(carve):
    class Broken:
        calls = 0

        def publish(self, *a, **k):
            Broken.calls += 1
            raise OSError('disk full')

        def path_of(self, *a):
            raise OSError('nope')
    r = M.Reporter(str(carve), lib=Broken(), interval=3600, poll=0.02).start()
    r.finish('failed', 'x')
    assert Broken.calls == 2 and r.errors == 2 and 'disk full' in r.last_error


def test_a_broken_carve_dir_never_raises(tmp_path):
    d = tmp_path / 'c'
    d.mkdir()
    (d / 'pipeline_state.json').write_text('{not json')
    (d / 'pipeline.json').write_text('[]')
    got = []

    class Lib:
        def publish(self, sid, **k):
            got.append(k)
    r = M.Reporter(str(d), lib=Lib())
    assert r.refresh() and r.errors == 0
    assert got[0]['phases'][0]['name'] == 'Steps' and got[0]['title'].endswith(': ?')


def test_waiting_for_the_background_publisher(carve):
    p = type('P', (), {'waiting': 'the background publisher (carve-pub-x)'})()
    sec = M.Reporter(str(carve), go=True, lib=False, pipeline=p).compose()
    assert sec['state'] == 'waiting' and 'waiting for the background publisher (carve-pub-x)' in sec['note']


@needs_monitor
def test_publisher_role_writes_only_while_no_driver_runs(carve, tmp_path, monkeypatch):
    home = str(tmp_path / 'mon')
    lib = M.section_lib()
    drv = M.Reporter(str(carve), go=True, lib=lib, home=home)
    drv.refresh(final=('failed', 'stopped at calibrate_pieces: piece:S2 over'))
    pub = M.Reporter(str(carve), role='publisher', lib=lib, home=home)
    f = os.path.join(home, 'sections', drv.sid + '.json')
    monkeypatch.setattr(M.Carve, 'driver_alive', lambda self: True)
    before = open(f).read()
    assert pub.refresh() is False and open(f).read() == before
    monkeypatch.setattr(M.Carve, 'driver_alive', lambda self: False)
    rs = json.load(open(carve / 'publish' / 'run_state.json'))
    rs['bundle:B1']['state'] = 'live'
    wj(carve / 'publish' / 'run_state.json', rs)
    assert pub.refresh()
    sec = json.load(open(f))
    assert sec['state'] == 'failed' and sec['alerts'] == ['stopped at calibrate_pieces: piece:S2 over']
    assert sec['note'] == 'stopped at calibrate_pieces: piece:S2 over' + M.PUB_SEP + 'still publishing'
    assert phase(sec, 'Publish (live)')['done'] == 3
    pub.finish('done', 'ended: 3 live of 6, 1 stopped')
    sec = json.load(open(f))
    assert sec['state'] == 'failed' and sec['note'].endswith(M.PUB_SEP + 'ended: 3 live of 6, 1 stopped')
    assert sec['note'].count(M.PUB_SEP) == 1


def test_publisher_reporter_finds_the_carve_of_its_run_file(carve, tmp_path, monkeypatch):
    monkeypatch.setenv('P2M_MONITOR_SECTION', '')
    r = M.publisher_reporter(str(carve / 'publish' / 'run_early.json'))
    assert r is not None and r.d == str(carve) and r.role == 'publisher'
    assert M.publisher_reporter(str(tmp_path / 'elsewhere' / 'run.json')) is None


def test_stop_reason():
    assert M.stop_reason("step 'build' failed (exit 1); log /c/logs/build.log\n$ python3 oai_build_modules.py\n"
                         "✖ [3/9] FAILED X\n2 modules failed: X, Y; 1 skipped because they import one\n(exit 1)\n") == \
        'stopped at build: (exit 1): 2 modules failed: X, Y; 1 skipped because they import one'
    assert M.stop_reason("step 'calibrate_pieces': piece(s) over the 88 s limit after the bundles and statements began "
                         "publishing:\n  piece:A: 130 s, x\n  piece:B: 140 s, y\n  piece:C: 150 s\nThe published part") == \
        ('stopped at calibrate_pieces: piece(s) over the 88 s limit after the bundles and statements began publishing: '
         'piece:A: 130 s, x (3 items listed)')
    assert M.stop_reason("step 'config' failed: no /c/oai_meta.json: write it") == 'stopped at config: no /c/oai_meta.json: write it'
    assert M.stop_reason('refused, nothing was run:\n  Solutions/F belongs to carve /x') == \
        'stopped: refused, nothing was run: Solutions/F belongs to carve /x'
    assert len(M.stop_reason('x' * 5000)) <= 600


def test_runlock_at_stop_runs_hooks_and_ignores_their_failures(monkeypatch):
    got = []
    monkeypatch.setattr(runlock, '_on_stop', [])
    monkeypatch.setattr(runlock, 'stop_tree', lambda: got.append('tree'))
    runlock.at_stop(lambda s: 1 / 0)
    runlock.at_stop(lambda s: got.append(s))
    with pytest.raises(KeyboardInterrupt):
        runlock._stop_and_exit(2, None)
    assert got == ['tree', 2]


def test_runlock_peek_takes_no_lock_and_checks_the_command(tmp_path, monkeypatch):
    monkeypatch.setenv('P2M_LOCK_DIR', str(tmp_path / 'locks'))
    key = runlock.dir_key('pipeline', str(tmp_path / 'c'))
    assert runlock.peek(key, 'python') is None
    os.makedirs(str(tmp_path / 'locks'))
    open(runlock._path(key), 'w').write(json.dumps({'pid': os.getpid()}))
    assert runlock.peek(key, 'python') or runlock.peek(key, 'pytest')
    assert runlock.peek(key, 'carve_pipeline-no-such') is None
    assert runlock.held_by(key) is None              # the file is there, nobody holds it
