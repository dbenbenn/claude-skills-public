"""p2mlib.runlock: one live run per carve (2026-10-23: a resumed agent restarted a PosteriorReplicas
pipeline it had already started an hour before, and two builds wrote the same .olean files)."""
import os
import signal
import subprocess
import sys
import textwrap
import time

import pytest

from conftest import SCRIPTS

ROOT = os.path.dirname(SCRIPTS)
HOLDER = textwrap.dedent('''
    import sys, time
    sys.path.insert(0, %r)
    from p2mlib import runlock
    runlock.hold(sys.argv[1], 'test holder')
    print('held', flush=True)
    time.sleep(60)
''') % ROOT


@pytest.fixture
def lockdir(tmp_path, monkeypatch):
    d = tmp_path / 'locks'
    monkeypatch.setenv('P2M_LOCK_DIR', str(d))
    return d


def start_holder(key):
    p = subprocess.Popen([sys.executable, '-c', HOLDER, key], stdout=subprocess.PIPE, text=True,
                         env=os.environ.copy())
    assert p.stdout.readline().strip() == 'held'
    return p


def test_second_holder_exits_3_naming_the_first(lockdir):
    from p2mlib import runlock
    p = start_holder('carve|/x/posteriorreplicas')
    try:
        with pytest.raises(SystemExit) as e:
            runlock.hold('carve|/x/posteriorreplicas', 'second')
        assert e.value.code == 3
        msg = runlock.last_refusal
        assert 'pid %d' % p.pid in msg and 'test holder' in msg
    finally:
        p.kill()
        p.wait()


def test_other_keys_and_released_locks_are_free(lockdir):
    from p2mlib import runlock
    p = start_holder('build|/ws|A')
    try:
        assert runlock.held_by('build|/ws|B') is None
        assert runlock.held_by('build|/ws|A')['pid'] == p.pid
    finally:
        p.kill()
        p.wait()
    time.sleep(0.1)
    assert runlock.held_by('build|/ws|A') is None        # the kernel drops a dead holder's flock


def test_keys_name_real_paths(tmp_path):
    from p2mlib import runlock
    (tmp_path / 'real').mkdir()
    os.symlink(tmp_path / 'real', tmp_path / 'link')
    assert runlock.dir_key('carve', str(tmp_path / 'link' / 'config.json')) == \
        runlock.dir_key('carve', str(tmp_path / 'real' / 'config.json'))
    assert runlock.build_key(str(tmp_path / 'link'), 'F') == runlock.build_key(str(tmp_path / 'real'), 'F')


@pytest.mark.parametrize('script,argv,key', [
    ('oai_build_modules.py', ['FOLDER', 'Main', '--ws', '{ws}'], ('build', '{ws}', 'FOLDER')),
    ('carve.py', ['graph', '{cfg}'], ('carve', '{cfg}')),
    ('carve_measure.py', ['{cfg}'], ('measure', '{cfg}')),
])
def test_scripts_refuse_while_their_carve_is_held(lockdir, tmp_path, script, argv, key):
    from p2mlib import runlock
    ws = tmp_path / 'ws'
    ws.mkdir()
    cfg = tmp_path / 'carve' / 'config.json'
    cfg.parent.mkdir()
    cfg.write_text('{}')
    sub = {'{ws}': str(ws), '{cfg}': str(cfg)}
    k = [sub.get(x, x) for x in key]
    k = runlock.build_key(k[1], k[2]) if k[0] == 'build' else runlock.dir_key(k[0], k[1])
    p = start_holder(k)
    try:
        r = subprocess.run([sys.executable, os.path.join(SCRIPTS, script)] + [sub.get(a, a) for a in argv],
                           capture_output=True, text=True, timeout=60, env=os.environ.copy())
        assert r.returncode == 3, r.stderr
        assert 'already running' in r.stderr and 'pid %d' % p.pid in r.stderr
    finally:
        p.kill()
        p.wait()


# A holder whose child starts a grandchild, as lake starts lean. SIGHUP and SIGINT are reset to their
# defaults first, as for a run started in the foreground (this test may itself run under nohup).
TREE_HOLDER = textwrap.dedent('''
    import signal, subprocess, sys, time
    sys.path.insert(0, %r)
    signal.signal(signal.SIGHUP, signal.SIG_DFL)
    signal.signal(signal.SIGINT, signal.default_int_handler)
    if sys.argv[2] == 'nohup':
        signal.signal(signal.SIGHUP, signal.SIG_IGN)
    from p2mlib import runlock
    runlock.hold(sys.argv[1], 'test holder')
    c = subprocess.Popen(['sh', '-c', 'sleep 60 & echo $!; wait'], stdout=subprocess.PIPE, text=True)
    print('held', c.pid, c.stdout.readline().strip(), flush=True)
    c.wait()
''') % ROOT


def running(pid):
    try:
        return open('/proc/%s/stat' % pid).read().rsplit(')', 1)[1].split()[0] != 'Z'
    except OSError:
        return False


def gone(*pids):
    deadline = time.time() + 5
    while time.time() < deadline and any(running(x) for x in pids):
        time.sleep(0.05)
    return not any(running(x) for x in pids)


def start_tree(key, mode='plain'):
    p = subprocess.Popen([sys.executable, '-c', TREE_HOLDER, key, mode], stdout=subprocess.PIPE, text=True,
                         env=os.environ.copy())
    word, child, grandchild = p.stdout.readline().split()
    assert word == 'held' and running(child) and running(grandchild)
    return p, child, grandchild


@pytest.mark.parametrize('sig', [signal.SIGTERM, signal.SIGHUP, signal.SIGINT])
def test_stopping_a_holder_stops_everything_it_started(lockdir, sig):
    # 2026-10-26 (oaiq-003, oaiq-012): killing carve_pipeline left its lake/lean children compiling
    # for minutes, and the restarted run raced them over the same .olean files
    from p2mlib import runlock
    p, child, grandchild = start_tree('build|/ws|T')
    p.send_signal(sig)
    assert p.wait(timeout=15) == -sig
    assert gone(child, grandchild)
    assert runlock.held_by('build|/ws|T') is None


def test_a_nohup_run_survives_a_hangup(lockdir):
    p, child, grandchild = start_tree('build|/ws|N', 'nohup')
    try:
        p.send_signal(signal.SIGHUP)
        time.sleep(0.5)
        assert p.poll() is None and running(child) and running(grandchild)
    finally:
        p.terminate()
        p.wait(timeout=15)
    assert gone(child, grandchild)
