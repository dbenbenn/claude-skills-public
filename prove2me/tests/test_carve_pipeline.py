"""scripts/carve_pipeline.py: the one driver for the module-route carve, run from a skill snapshot.
All sub-tools are stubs in a synthetic skills repo (the real carve tools need Lean); nothing here
touches prove2.me."""
import json
import os
import shutil
import stat
import subprocess
import sys
import textwrap

import pytest

from conftest import SCRIPTS

ROOT = os.path.dirname(SCRIPTS)
STUB = textwrap.dedent('''
    import json, os, sys
    NAME = %r
    VERSION = %r
    with open(os.environ['STUB_LOG'], 'a') as f:
        f.write(json.dumps({'tool': NAME, 'version': VERSION, 'file': os.path.abspath(__file__),
                            'argv': sys.argv[1:], 'cwd': os.getcwd(),
                            'skill': os.environ.get('P2M_SKILL_ROOT')}) + '\\n')
    if os.environ.get('STUB_FAIL') == NAME + ' ' + (sys.argv[1] if len(sys.argv) > 1 else ''):
        print('boom from ' + NAME)
        sys.exit(1)
    if NAME == 'carve_prep' and sys.argv[1] == 'config':
        json.dump({'targets': [], 'external': ['E']}, open(os.path.join(sys.argv[2], 'config.json'), 'w'))
    if NAME == 'carve_prep' and sys.argv[1] == 'prose-template':
        print('needs written prose: goal (goal)')
''')
TOOLS = ['oai_fetch', 'oai_port_modules', 'oai_build_modules', 'carve_prep', 'carve', 'carve_measure', 'split_run']


def git(repo, *a):
    return subprocess.run(['git', '-C', str(repo), '-c', 'user.name=t', '-c', 'user.email=t@t', *a],
                          check=True, capture_output=True, text=True).stdout.strip()


def write_tools(repo, version):
    d = repo / 'prove2me' / 'scripts'
    d.mkdir(parents=True, exist_ok=True)
    for t in TOOLS:
        (d / (t + '.py')).write_text(STUB % (t, version))


@pytest.fixture
def env(tmp_path, monkeypatch):
    repo = tmp_path / 'skills'
    write_tools(repo, 'v1')
    shutil.copytree(os.path.join(ROOT, 'p2mlib'), repo / 'prove2me' / 'p2mlib',
                    ignore=shutil.ignore_patterns('__pycache__'))
    shutil.copy(os.path.join(SCRIPTS, 'carve_pipeline.py'), repo / 'prove2me' / 'scripts' / 'carve_pipeline.py')
    (repo / '.gitignore').write_text('__pycache__/\n')
    git(repo, 'init', '-q', '-b', 'main')
    git(repo, 'add', '-A')
    git(repo, 'commit', '-qm', 'v1')
    ws = tmp_path / 'ws'
    (ws / 'Solutions' / 'F').mkdir(parents=True)
    (ws / 'Solutions' / 'F' / 'Pre_Main.lean').write_text('')
    (ws / 'Theorems').mkdir()
    (ws / 'Theorems' / 'Thm_OAI_X_main.lean').write_text('import Mathlib\nimport Definitions.Def_A\n\ntheorem OAI.X.main : True := by sorry\n')
    d = tmp_path / 'carve'
    (d / 'src' / 'lean' / 'OAI' / 'Pre').mkdir(parents=True)
    (d / 'oai_meta.json').write_text('{"title": "T", "date": "d", "family": "1"}')
    bin = tmp_path / 'bin'
    bin.mkdir()
    lake = bin / 'lake'
    lake.write_text('#!/bin/sh\necho "lake $@ (cwd $PWD)" >> "$STUB_LOG"\n')
    lake.chmod(lake.stat().st_mode | stat.S_IXUSR)
    log = tmp_path / 'stub.log'
    for k, v in {'P2M_SKILL_REPO': str(repo), 'P2M_SNAPSHOT_CACHE': str(tmp_path / 'cache'), 'P2M_WORKSPACE': str(ws),
                 'STUB_LOG': str(log), 'P2M_LOCK_DIR': str(tmp_path / 'locks'), 'P2M_LEAN_CAP': '',
                 'PATH': str(bin) + os.pathsep + os.environ['PATH']}.items():
        monkeypatch.setenv(k, v)
    monkeypatch.delenv('STUB_FAIL', raising=False)
    return type('E', (), dict(repo=repo, ws=ws, dir=d, log=log, tmp=tmp_path))


ARGS = ['--folder', 'F', '--root-module', 'OAI.Pre.Main', '--target', 'OAI.X.main', '--bundle-prefix', 'B']


def run(env, *extra, dir=True):
    live = env.repo / 'prove2me' / 'scripts' / 'carve_pipeline.py'
    return subprocess.run([sys.executable, str(live), str(env.dir), *extra], capture_output=True, text=True)


def calls(env):
    return [json.loads(l) for l in env.log.read_text().splitlines() if l.startswith('{')] if env.log.exists() else []


def tools_called(env):
    return [(c['tool'], c['argv'][0] if c['argv'] else '') for c in calls(env) if 'tool' in c]


def test_full_run_calls_every_step_in_order_from_one_snapshot(env):
    r = run(env, *ARGS)
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert ('carve', 'graph') in seq and seq.index(('carve', 'graph')) < seq.index(('carve', 'plan')) < seq.index(('carve', 'gen'))
    assert seq.index(('carve_prep', 'config')) < seq.index(('carve', 'graph'))
    assert seq.index(('carve_prep', 'publish-prep')) < seq.index(('carve_prep', 'prose-template')) < seq.index(('carve_prep', 'check-text'))
    assert seq[-1][0] == 'split_run'
    sha = git(env.repo, 'rev-parse', 'HEAD')
    snap = str(env.tmp / 'cache' / sha)
    for c in calls(env):
        if 'tool' in c:
            assert c['file'].startswith(snap + os.sep), c
            assert c['skill'] == snap
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['snapshot']['sha'] == sha and all(v['status'] in ('done', 'skipped') for v in st['steps'].values())
    cfg = json.load(open(env.dir / 'config.json'))
    assert cfg['targets'] == ['OAI.X.main'] and 'OAI.X.main' in cfg['external']
    assert any('lake build' in l for l in env.log.read_text().splitlines() if l.startswith('lake'))
    assert (env.dir / 'logs' / 'graph.log').exists()


def test_dry_run_step_never_passes_go_and_publish_does(env):
    run(env, *ARGS)
    assert not any('--go' in c['argv'] for c in calls(env) if c.get('tool') == 'split_run')
    env.log.unlink()
    r = run(env, '--publish')
    assert r.returncode == 0, r.stdout + r.stderr
    assert [c['argv'] for c in calls(env) if c.get('tool') == 'split_run'] == [['publish/run.json', '--go']]


def test_failure_stops_with_message_and_resume_skips_done_steps(env, monkeypatch):
    monkeypatch.setenv('STUB_FAIL', 'carve plan')
    r = run(env, *ARGS)
    assert r.returncode == 1
    assert "step 'plan' failed" in r.stderr and 'boom from carve' in r.stderr and 'logs/plan.log' in r.stderr
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['steps']['plan']['status'] == 'failed' and st['steps']['graph']['status'] == 'done'
    assert 'gen' not in st['steps']
    before = tools_called(env)
    monkeypatch.delenv('STUB_FAIL')
    r = run(env)                                           # resume: no parameters needed
    assert r.returncode == 0, r.stdout + r.stderr
    after = tools_called(env)[len(before):]
    assert ('carve', 'graph') not in after and ('oai_build_modules', 'F') not in after
    assert after[0] == ('carve', 'plan') and after[-1][0] == 'split_run'


def test_resume_stays_on_its_snapshot_until_upgrade(env, monkeypatch):
    monkeypatch.setenv('STUB_FAIL', 'carve plan')
    run(env, *ARGS)
    sha1 = git(env.repo, 'rev-parse', 'HEAD')
    write_tools(env.repo, 'v2')                           # a skill fix is pushed mid-carve
    git(env.repo, 'add', '-A')
    git(env.repo, 'commit', '-qm', 'v2')
    monkeypatch.delenv('STUB_FAIL')
    env.log.write_text('')
    r = run(env)
    assert r.returncode == 0, r.stderr
    assert {c['version'] for c in calls(env)} == {'v1'}
    assert json.load(open(env.dir / 'pipeline_state.json'))['snapshot']['sha'] == sha1
    env.log.write_text('')
    r = run(env, '--upgrade', '--redo', 'dryrun')
    assert r.returncode == 0, r.stderr
    assert {c['version'] for c in calls(env)} == {'v2'}
    assert json.load(open(env.dir / 'pipeline_state.json'))['snapshot']['sha'] == git(env.repo, 'rev-parse', 'HEAD')


def test_live_edit_during_a_run_does_not_reach_the_run(env, monkeypatch):
    # the stub carve.py graph edits the live repo's tools (uncommitted, as a careless agent would)
    live = env.repo / 'prove2me' / 'scripts' / 'carve.py'
    text = live.read_text()
    live.write_text(text.replace("if os.environ.get('STUB_FAIL')", "open(%r, 'w').write('x')\nif os.environ.get('STUB_FAIL')" % str(env.tmp / 'touched')))
    git(env.repo, 'commit', '-qam', 'carve touches')
    r = run(env, *ARGS)
    assert r.returncode == 0, r.stderr
    (env.repo / 'prove2me' / 'scripts' / 'carve.py').write_text('raise SystemExit("live edit reached the run")\n')
    # resume (all done) must not care, and --redo plan must still use the snapshot
    r = run(env, '--redo', 'plan')
    assert r.returncode == 0, r.stdout + r.stderr


def test_dirty_skill_tree_is_refused_unless_allowed(env):
    (env.repo / 'prove2me' / 'scripts' / 'carve.py').write_text('# edited\n')
    r = run(env, *ARGS)
    assert r.returncode != 0 and 'dirty' in (r.stderr + r.stdout).lower()
    assert not (env.dir / 'pipeline_state.json').exists()


def test_stop_after_and_from_and_redo(env):
    r = run(env, *ARGS, '--stop-after', 'graph')
    assert r.returncode == 0 and tools_called(env)[-1] == ('carve', 'graph')
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert 'plan' not in st['steps']
    env.log.write_text('')
    run(env, '--from', 'gen', '--stop-after', 'gen')       # earlier steps still done: gen first needs extdefs and plan
    assert [t for t in tools_called(env)] == [('carve_prep', 'ext-defs'), ('carve', 'plan'), ('carve', 'gen')]
    env.log.write_text('')
    run(env, '--redo', 'gen', '--stop-after', 'gen')
    assert tools_called(env) == [('carve', 'gen')]


def test_parameters_are_remembered_and_a_change_is_refused(env):
    run(env, *ARGS, '--stop-after', 'config')
    p = json.load(open(env.dir / 'pipeline.json'))
    assert p['folder'] == 'F' and p['targets'] == ['OAI.X.main']
    r = run(env, '--folder', 'G')
    assert r.returncode != 0 and 'differ' in r.stderr


def test_options_reach_the_tools(env):
    (env.tmp / 'patches.json').write_text('[]')
    r = run(env, *ARGS, '--patches', str(env.tmp / 'patches.json'), '--compat-imports', 'narrow', '--budget', '40',
            '--forced', 'OAI.X.lemma', '--def', 'Definitions.Def_Z', '--measure-flag=--drop-false-edges')
    assert r.returncode == 0, r.stderr
    by = {}
    for c in calls(env):
        if 'tool' in c:
            by.setdefault((c['tool'], c['argv'][0] if c['argv'] else ''), c['argv'])
    port = [c for c in calls(env) if c.get('tool') == 'oai_port_modules'][0]['argv']
    assert '--compat-imports' in port and port[port.index('--compat-imports') + 1] == 'narrow'
    assert '--patches' in port and 'OAI.Pre' in port
    cfg = by[('carve_prep', 'config')]
    assert cfg[cfg.index('--budget') + 1] == '40' and '--forced' in cfg and 'OAI.X.lemma' in cfg
    defs = [cfg[i + 1] for i, a in enumerate(cfg) if a == '--def']
    assert defs == ['Definitions.Def_Z']                    # explicit --def replaces the derived list
    assert '--drop-false-edges' in by[('carve_measure', 'config.json')]
    assert json.load(open(env.dir / 'config.json'))['collapse_mathlib'] is False
    assert ('carve_prep', 'filter-patches') in by


def test_defs_derived_from_the_targets_statement_imports(env):
    run(env, *ARGS, '--stop-after', 'config')
    cfg = [c for c in calls(env) if c.get('tool') == 'carve_prep' and c['argv'][0] == 'config'][0]['argv']
    assert [cfg[i + 1] for i, a in enumerate(cfg) if a == '--def'] == ['Definitions.Def_A']
    assert cfg[2:5] == ['F', 'Pre_Main', 'OAI.X.main']


def test_second_driver_on_the_same_carve_exits_3(env):
    sys.path.insert(0, ROOT)
    from p2mlib import runlock
    key = runlock.dir_key('pipeline', str(env.dir))
    holder = subprocess.Popen([sys.executable, '-c', textwrap.dedent('''
        import sys, time
        sys.path.insert(0, %r)
        from p2mlib import runlock
        runlock.hold(%r, 'holder'); print('held', flush=True); time.sleep(60)''' % (ROOT, key))],
        stdout=subprocess.PIPE, text=True, env=dict(os.environ))
    try:
        assert holder.stdout.readline().strip() == 'held'
        assert run(env, *ARGS).returncode == 3
    finally:
        holder.kill()


def test_module_root_name():
    sys.path.insert(0, ROOT)
    from p2mlib.carvepipeline import module_root_name
    assert module_root_name('OAI.A.B.Main', ['OAI.A.B', 'OAI.A'], ['Main.lean', 'X.lean']) == 'Main'
    assert module_root_name('OAI.A.B.Sub.Main', ['OAI.A.B'], ['Sub_Main.lean']) == 'Sub_Main'
    assert module_root_name('OAI.A.B.Sub.Main', ['OAI.A.B'], ['Q_Sub_Main.lean', 'Main.lean']) == 'Q_Sub_Main'
    assert module_root_name('OAI.A.B', ['OAI.A.B'], ['B.lean']) == 'B'
