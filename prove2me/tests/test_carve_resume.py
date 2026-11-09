"""carve_resume.py: after a reboot or power cut, resume the carves whose detached driver (and publisher) were
running. q153 (2026-11-09): three power cuts in an afternoon; the transient systemd units did not come back, and
nothing ran for hours each time until a person noticed."""
import json
import os
import time

import pytest


def _carve(tmp_path, name='c', driver=None, publisher=None, detached=None, state=None, age=0):
    d = tmp_path / 'jobs' / name / 'pp'
    (d / 'logs').mkdir(parents=True)
    (d / 'pipeline.json').write_text('{}')
    (d / 'pipeline_state.json').write_text(json.dumps(state or {'steps': {}}))
    if driver is not None:
        (d / 'logs' / 'driver.log').write_text(driver)
        t = time.time() - age
        os.utime(d / 'logs' / 'driver.log', (t, t))
    if publisher is not None:
        (d / 'logs' / 'publish_early.log').write_text(publisher)
        t = time.time() - age
        os.utime(d / 'logs' / 'publish_early.log', (t, t))
    if detached is not None:
        (d / 'logs' / 'detached.json').write_text(json.dumps(detached))
    return d


RUNNING = '== detached 2026-11-09 16:38:40 run R1\n== measure 2026-11-09T16:40:00\n'
ENDED = RUNNING + '== driver exit 0 run R1\n'
PUB_RUNNING = ('== publisher exit 1\n== 2026-11-09T16:50:19 background publisher (streaming: bundles, statements and '
               'pieces as released), skill abc\n')
PUB_ENDED = PUB_RUNNING + '== publisher exit 0\n'


def test_resume_argv_drops_one_shot_options_and_the_upgrade():
    import carve_resume as CR
    argv = ['--upgrade', '--publish', '--redo', 'gen', '--from', 'measure', '--split-piece', 'P=3', '--detach',
            '--snapshot', 'abc', '--allow-dirty', '--claim-folder']
    assert CR.resume_argv(argv) == ['--publish', '--snapshot', 'abc', '--allow-dirty']


def test_a_driver_interrupted_by_the_reboot_is_resumed_with_its_recorded_arguments(tmp_path):
    import carve_resume as CR
    d = _carve(tmp_path, driver=RUNNING, detached={'run_id': 'R1', 'argv': ['--publish', '--stop-after', 'measure']})
    a = CR.driver_action(str(d), since=time.time() - 3600, active=lambda u: False)
    assert a['resume'] and a['argv'] == ['--publish', '--stop-after', 'measure']


def test_a_driver_is_left_alone_when_its_run_ended_its_unit_runs_it_is_stale_or_held(tmp_path):
    import carve_resume as CR
    since = time.time() - 3600
    assert not CR.driver_action(str(_carve(tmp_path, 'a', driver=ENDED)), since, lambda u: False)['resume']
    assert not CR.driver_action(str(_carve(tmp_path, 'b', driver=RUNNING)), since, lambda u: True)['resume']
    stale = CR.driver_action(str(_carve(tmp_path, 'c', driver=RUNNING, age=7200)), since, lambda u: False)
    assert not stale['resume'] and 'before the previous boot' in stale['why']
    held = _carve(tmp_path, 'd', driver=RUNNING)
    (held / 'NO_RESUME').write_text('dbenbenn stopped it\n')
    assert not CR.driver_action(str(held), since, lambda u: False)['resume']


def test_a_run_from_before_detached_json_resumes_with_publish_once_publishing_began(tmp_path):
    import carve_resume as CR
    d = _carve(tmp_path, driver=RUNNING, state={'steps': {}, 'publishing_started': 'x'})
    assert CR.driver_action(str(d), time.time() - 3600, lambda u: False)['argv'] == ['--publish']
    d = _carve(tmp_path, 'e', driver=RUNNING, detached={'run_id': 'OTHER', 'argv': ['--x']})
    assert CR.driver_action(str(d), time.time() - 3600, lambda u: False)['argv'] == []


def test_a_publisher_that_was_running_is_restarted_on_the_recorded_snapshot(tmp_path):
    import carve_resume as CR
    st = {'steps': {}, 'publisher': {'gated': True}, 'snapshot': {'path': '/snap/abc'}}
    d = _carve(tmp_path, publisher=PUB_RUNNING, state=st)
    a = CR.publisher_action(str(d), time.time() - 3600, lambda u: False)
    assert a['resume'] and a['gated'] is True and a['snap'] == '/snap/abc'
    assert not CR.publisher_action(str(_carve(tmp_path, 'b', publisher=PUB_ENDED, state=st)),
                                   time.time() - 3600, lambda u: False)['resume']
    assert not CR.publisher_action(str(_carve(tmp_path, 'c2', publisher=PUB_RUNNING, state=st)),
                                   time.time() - 3600, lambda u: True)['resume']


def test_dry_run_lists_without_starting_anything(tmp_path, capsys, monkeypatch):
    import carve_resume as CR
    _carve(tmp_path, driver=RUNNING, publisher=PUB_RUNNING,
           state={'steps': {}, 'publisher': {'gated': True}, 'snapshot': {'path': '/snap/abc'}})
    started = []
    monkeypatch.setattr(CR, 'start', lambda *a, **k: started.append(a))
    monkeypatch.setattr(CR, 'unit_active', lambda u: False)
    CR.main(['--roots', str(tmp_path / 'jobs'), '--since', str(time.time() - 3600), '--dry-run'])
    out = capsys.readouterr().out
    assert 'would resume driver' in out and 'would restart publisher' in out and started == []
    CR.main(['--roots', str(tmp_path / 'jobs'), '--since', str(time.time() - 3600)])
    assert [a[0] for a in started] == ['publisher', 'driver']
    assert 'resumed by carve_resume' in (tmp_path / 'jobs' / 'c' / 'pp' / 'logs' / 'driver.log').read_text()


def test_detach_records_its_run_and_arguments_for_a_resume(tmp_path):
    import carve_resume as CR
    (tmp_path / 'logs').mkdir()
    CR.CPL.write_detached(str(tmp_path), 'R9', ['--upgrade', '--publish'])
    rec = json.load(open(tmp_path / 'logs' / 'detached.json'))
    assert rec['run_id'] == 'R9' and rec['argv'] == ['--upgrade', '--publish'] and rec['at']
