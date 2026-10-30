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
    if NAME == 'fetch_theorems':
        ws = os.environ['P2M_WORKSPACE']
        for n in sys.argv[2:]:
            if n.startswith('--'):
                continue
            if '.' in n:
                p = os.path.join(ws, 'Theorems', 'Thm_' + n.replace('.', '_') + '.lean')
                open(p, 'w').write('import Mathlib\\nimport Definitions.Def_A\\n\\ntheorem ' + n + ' : True := by sorry\\n')
                os.makedirs(os.path.join(ws, 'Definitions'), exist_ok=True)
                open(os.path.join(ws, 'Definitions', 'Def_A.lean'), 'w').write('def A := 1\\n')
            else:
                os.makedirs(os.path.join(ws, 'Definitions'), exist_ok=True)
                open(os.path.join(ws, 'Definitions', 'Def_' + n + '.lean'), 'w').write('def X := 1\\n')
    if NAME == 'carve_prep' and sys.argv[1] == 'prose-template':
        print('needs written prose: goal (goal)')
    if NAME == 'carve_prep' and sys.argv[1] == 'publish-prep':
        import shutil
        d = sys.argv[2]
        os.makedirs(os.path.join(d, 'publish', 'out', 'lib'), exist_ok=True)
        if os.path.exists(os.path.join(d, 'carve_work', 'plan.json')):
            shutil.copy(os.path.join(d, 'carve_work', 'plan.json'), os.path.join(d, 'publish', 'plan.json'))
        if os.path.isdir(os.path.join(d, 'out', 'lib')):
            for f in os.listdir(os.path.join(d, 'out', 'lib')):
                shutil.copy(os.path.join(d, 'out', 'lib', f), os.path.join(d, 'publish', 'out', 'lib', f))
        open(os.path.join(d, 'publish', 'run_early.json'), 'w').write('{}')
    # a test scripts a tool's behaviour: STUB_HOOK_<tool>_<first argument, . and - as _>
    exec(os.environ.get('STUB_HOOK_' + NAME + '_' + (sys.argv[1] if len(sys.argv) > 1 else '').replace('.', '_').replace('-', '_'), ''))
''')
TOOLS = ['fetch_theorems', 'oai_fetch', 'oai_port_modules', 'oai_build_modules', 'carve_prep', 'carve', 'carve_measure', 'split_run']


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
    (ws / 'Definitions').mkdir()
    (ws / 'Definitions' / 'Def_A.lean').write_text('def A := 1\n')
    d = tmp_path / 'carve'
    (d / 'src' / 'lean' / 'OAI' / 'Pre').mkdir(parents=True)
    (d / 'oai_meta.json').write_text('{"title": "T", "date": "d", "family": "1", "commit": "%s", "prefixes": ["OAI.Pre"]}' % ('a' * 40))
    bin = tmp_path / 'bin'
    bin.mkdir()
    lake = bin / 'lake'
    lake.write_text('#!/bin/sh\necho "lake $@ (cwd $PWD)" >> "$STUB_LOG"\n')
    lake.chmod(lake.stat().st_mode | stat.S_IXUSR)
    # never the real systemd: a --detach in a test must not start a user unit
    for name, body in (('systemd-run', 'echo "systemd-run $@" >> "$STUB_LOG"\n'), ('systemctl', 'exit 3\n')):
        f = bin / name
        f.write_text('#!/bin/sh\n' + body)
        f.chmod(f.stat().st_mode | stat.S_IXUSR)
    log = tmp_path / 'stub.log'
    for k, v in {'P2M_SKILL_REPO': str(repo), 'P2M_SNAPSHOT_CACHE': str(tmp_path / 'cache'), 'P2M_WORKSPACE': str(ws),
                 'STUB_LOG': str(log), 'P2M_LOCK_DIR': str(tmp_path / 'locks'), 'P2M_LEAN_CAP': '',
                 'PATH': str(bin) + os.pathsep + os.environ['PATH']}.items():
        monkeypatch.setenv(k, v)
    monkeypatch.delenv('STUB_FAIL', raising=False)
    return type('E', (), dict(repo=repo, ws=ws, dir=d, log=log, tmp=tmp_path))


ARGS = ['--folder', 'F', '--root-module', 'OAI.Pre.Main', '--target', 'OAI.X.main', '--bundle-prefix', 'B', '--no-overlap']
ARGS_NEW = ARGS[:-1]                    # a carve created now: overlap mode by default


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


def test_a_dirty_skill_tree_runs_from_head_with_a_warning(env):
    (env.repo / 'prove2me' / 'scripts' / 'carve.py').write_text('# edited\n')
    r = run(env, *ARGS, '--stop-after', 'config')
    assert r.returncode == 0, r.stderr
    assert 'not in this snapshot' in r.stderr
    assert {c['version'] for c in calls(env)} == {'v1'}            # the committed tools ran


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
    fp = by[('carve_prep', 'filter-patches')]
    assert fp[fp.index('--folder') + 1] == json.load(open(env.dir / 'pipeline.json'))['folder']


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


# ---------------------------------------------------------------- calibration of the cost model

from p2mlib import carvepipeline as CP


def _plan(costs, pieces=None):
    return {'bundles': [{'name': n, 'cost': c} for n, c in costs.items()],
            'pieces': {n: {'cost': c} for n, c in (pieces or {}).items()}}


def _t(secs, ok=True):
    return {'secs': secs, 'ok': ok}


def test_calibration_leaves_a_model_that_fits_alone():
    r = CP.calibration(_plan({'B0': 55, 'B1': 55}, {'P': 50}),
                       {'bundle:B0': _t(15), 'bundle:B1': _t(80), 'piece:P': _t(60)}, 1.2, 55)
    assert r['over'] == [] and r['new_scale'] == 1.2 and r['measured'] == 3
    assert r['slowest'] == ('bundle:B1', 80)


def test_calibration_scales_by_the_worst_item_over_the_limit():
    # Kirchberg's first plan: bundles of planned cost 55 measured 85-128 s (limit 1.6 x 55 = 88 s)
    r = CP.calibration(_plan({'B0': 55, 'B1': 55, 'B2': 30}, {'P': 50}),
                       {'bundle:B0': _t(85), 'bundle:B1': _t(128), 'bundle:B2': _t(20), 'piece:P': _t(90)},
                       1.2, 55)
    assert [x[0] for x in r['over']] == ['bundle:B1']             # a piece under the cap is resubmittable
    assert r['new_scale'] == round(1.2 * 128 / 55, 1) == 2.8
    # the old key form of times.json (the bare bundle name) counts
    assert CP.calibration(_plan({'B0': 55}), {'B0': _t(128)}, 1.2, 55)['over']


def test_calibration_ignores_published_failed_and_unmeasured_items_and_caps_the_scale():
    plan = _plan({'B0': 55, 'B1': 55, 'B2': 55, 'B3': 1})
    r = CP.calibration(plan, {'bundle:B0': _t(200), 'bundle:B1': _t(200, ok=False), 'bundle:B3': _t(500)},
                       2.0, 55, frozen=['B0'])
    assert [x[0] for x in r['over']] == ['bundle:B3']             # B0 is live, B1 failed, B2 unmeasured
    assert r['new_scale'] == CP.MAX_SCALE                          # 500 s against a planned 1 s
    assert CP.calibration(_plan({'B': 55}), {'bundle:B': _t(89)}, 2.0, 55)['new_scale'] == 3.2
    # always a real step up, never the same scale again
    assert CP.calibration(_plan({'B': 100}), {'bundle:B': _t(89)}, 2.0, 55)['new_scale'] == 2.2


CALIBRATING_MEASURE = textwrap.dedent('''
    import json, os, sys
    d = os.path.join(os.getcwd(), 'carve_work')
    n = len(open(os.environ['STUB_LOG']).read().split('"tool": "carve_measure"')) - 1
    after = os.environ.get('STUB_TIMES_AFTER')
    with open(os.environ['STUB_LOG'], 'a') as f:
        f.write(json.dumps({'tool': 'carve_measure', 'version': 'cal', 'file': os.path.abspath(__file__),
                            'argv': sys.argv[1:], 'cwd': os.getcwd(), 'skill': os.environ.get('P2M_SKILL_ROOT')}) + '\\n')
    if after and n >= 1:
        open(os.path.join(d, 'times.json'), 'w').write(after)
''')


def _calibration_setup(env, monkeypatch, after):
    work = env.dir / 'carve_work'
    work.mkdir(parents=True, exist_ok=True)
    (work / 'plan.json').write_text(json.dumps(_plan({'B0': 55, 'B1': 55})))
    (work / 'times.json').write_text(json.dumps({'bundle:B0': _t(20), 'bundle:B1': _t(128)}))
    (env.repo / 'prove2me' / 'scripts' / 'carve_measure.py').write_text(CALIBRATING_MEASURE)
    git(env.repo, 'add', '-A')
    git(env.repo, 'commit', '-qm', 'calibrating measure stub')
    if after is not None:
        monkeypatch.setenv('STUB_TIMES_AFTER', json.dumps(after))


def test_a_measure_over_the_limit_raises_the_scale_and_replans_before_anything_is_published(env, monkeypatch):
    _calibration_setup(env, monkeypatch, {'bundle:B0': _t(30), 'bundle:B1': _t(50)})
    r = run(env, *ARGS, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}))
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    first = [i for i, t in enumerate(seq) if t == ('carve', 'plan')]
    assert len(first) == 2 and [t[0] for t in seq].count('carve_measure') == 2
    assert seq[first[1]:first[1] + 6] == [('carve', 'plan'), ('carve', 'gen'), ('carve_prep', 'name-check'), ('carve', 'order'),
                                          ('carve_measure', 'config.json'), ('carve_prep', 'publish-prep')]
    cfg = json.load(open(env.dir / 'config.json'))
    assert cfg['time_scale'] == round(1.2 * 128 / 55, 1)
    assert json.load(open(env.dir / 'pipeline_state.json'))['replans'] == 1
    assert 'time_scale 1.2 -> 2.8' in (env.dir / 'logs' / 'calibrate.log').read_text()
    # a resume does not plan again
    n = len(calls(env))
    assert run(env).returncode == 0 and len(calls(env)) == n


def test_a_carve_that_still_does_not_fit_after_two_replans_stops_with_the_offenders(env, monkeypatch):
    _calibration_setup(env, monkeypatch, None)
    r = run(env, *ARGS, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}))
    assert r.returncode == 1
    assert 'bundle:B1' in r.stderr and 'carve.py split' in r.stderr
    assert json.load(open(env.dir / 'pipeline_state.json'))['replans'] == CP.MAX_REPLANS
    assert [t[0] for t in tools_called(env)].count('carve_measure') == CP.MAX_REPLANS + 1


def test_a_measure_that_fits_calibrates_nothing(env, monkeypatch):
    _calibration_setup(env, monkeypatch, None)
    (env.dir / 'carve_work' / 'times.json').write_text(json.dumps({'bundle:B0': _t(20), 'bundle:B1': _t(70)}))
    r = run(env, *ARGS, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}))
    assert r.returncode == 0, r.stdout + r.stderr
    assert [t[0] for t in tools_called(env)].count('carve_measure') == 1
    assert 'kept' in (env.dir / 'logs' / 'calibrate.log').read_text()


# ---------------------------------------------------------------- inputs: statements and Def_ bundles

def test_missing_statement_and_bundles_are_fetched_before_wsbuild(env):
    (env.ws / 'Theorems' / 'Thm_OAI_X_main.lean').unlink()
    r = run(env, *ARGS)
    assert r.returncode == 0, r.stdout + r.stderr
    fetch = [c for c in calls(env) if c.get('tool') == 'fetch_theorems']
    assert len(fetch) == 1 and fetch[0]['argv'] == ['--names', 'OAI.X.main', '--no-build']
    lines = [l for l in env.log.read_text().splitlines()]
    i_fetch = next(i for i, l in enumerate(lines) if '"fetch_theorems"' in l)
    i_build = next(i for i, l in enumerate(lines) if l.startswith('lake build'))
    assert i_fetch < i_build


def test_missing_def_bundle_alone_is_fetched_too(env):
    (env.ws / 'Definitions' / 'Def_A.lean').unlink()
    assert run(env, *ARGS).returncode == 0
    assert [c['argv'] for c in calls(env) if c.get('tool') == 'fetch_theorems'] == [['--names', 'OAI.X.main', '--no-build']]


def test_present_inputs_are_not_fetched(env):
    assert run(env, *ARGS).returncode == 0
    assert not [c for c in calls(env) if c.get('tool') == 'fetch_theorems']


def test_explicit_def_missing_from_workspace_is_fetched_by_name(env):
    assert run(env, *ARGS, '--def', 'Definitions.Def_Z').returncode == 0
    f = [c['argv'] for c in calls(env) if c.get('tool') == 'fetch_theorems']
    assert f == [['--names', 'Z', '--no-build']]


# ---------------------------------------------------------------- oai_meta.json is checked at config

def test_missing_meta_fails_at_config(env):
    (env.dir / 'oai_meta.json').unlink()
    r = run(env, *ARGS)
    assert r.returncode == 1 and "step 'config' failed" in r.stderr and 'oai_meta.json' in r.stderr
    assert ('carve_prep', 'config') not in tools_called(env)


def test_meta_without_prefixes_or_with_foreign_prefixes_fails_at_config(env):
    c = '"commit": "%s"' % ('a' * 40)
    for meta in ('{"title": "T", "date": "d", "family": "1", %s}' % c,
                 '{"title": "T", "date": "d", "family": "1", %s, "prefixes": ["OAI.Other"]}' % c):
        (env.dir / 'oai_meta.json').write_text(meta)
        env.log.write_text('')
        r = run(env, *ARGS, '--stop-after', 'config')
        assert r.returncode == 1 and "step 'config' failed" in r.stderr and 'prefixes' in r.stderr, meta
        assert ('carve_prep', 'config') not in tools_called(env)
        (env.dir / 'pipeline_state.json').unlink()


# ---------------------------------------------------------------- stale steps: changed output reaches its consumers

def _patches_setup(env, text='[]'):
    (env.tmp / 'patches.json').write_text(text)
    return ['--patches', str(env.tmp / 'patches.json')]


def test_redo_filter_patches_with_changed_output_reruns_port_and_what_follows(env):
    # six batches: edited the patches, ran `--redo filter_patches`, and the port stayed unpatched
    extra = _patches_setup(env)
    assert run(env, *ARGS, *extra).returncode == 0
    n = len(tools_called(env))
    # the stub filter-patches writes nothing; make the redo change port_patches.json
    pp = env.dir / 'port_patches.json'
    pp.write_text('[{"old": "a", "new": "b"}]')
    env.log.write_text('')
    r = run(env, '--redo', 'filter_patches')
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert seq[0] == ('carve_prep', 'filter-patches') and ('oai_port_modules', next(c['argv'][0] for c in calls(env) if c['tool'] == 'oai_port_modules')) in seq
    assert ('carve_prep', 'config') in seq and ('carve', 'plan') in seq        # everything after was re-run
    assert 'stale' in r.stdout


def test_redo_with_unchanged_output_leaves_later_steps_alone(env):
    extra = _patches_setup(env)
    assert run(env, *ARGS, *extra).returncode == 0
    env.log.write_text('')
    assert run(env, '--redo', 'filter_patches').returncode == 0
    assert tools_called(env) == [('carve_prep', 'filter-patches')]


def test_editing_the_patches_file_alone_marks_filter_patches_stale(env):
    extra = _patches_setup(env)
    assert run(env, *ARGS, *extra).returncode == 0
    (env.tmp / 'patches.json').write_text('[{"old": "a", "new": "b"}]')
    env.log.write_text('')
    r = run(env)
    assert r.returncode == 0, r.stdout + r.stderr
    assert tools_called(env)[0] == ('carve_prep', 'filter-patches') and ('carve', 'plan') in tools_called(env)


def test_editing_the_post_carve_patches_file_reruns_gen(env):
    # oaiq-114: a fix to config `patches` (same path, new text) was not seen; gen kept the broken patch
    cp = env.tmp / 'gen_patches.json'
    cp.write_text('[]')
    assert run(env, *ARGS, '--config-set', json.dumps({'patches': str(cp)})).returncode == 0
    cp.write_text('[{"literal_old": "a", "literal_new": "b", "why": "w"}]')
    env.log.write_text('')
    r = run(env)
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert ('carve', 'gen') in seq and ('carve', 'plan') not in seq and 'stale' in r.stdout


def test_state_from_before_hashes_existed_is_not_called_stale(env):
    assert run(env, *ARGS).returncode == 0
    st = json.load(open(env.dir / 'pipeline_state.json'))
    for rec in st['steps'].values():
        rec.pop('in', None)
    json.dump(st, open(env.dir / 'pipeline_state.json', 'w'))
    (env.dir / 'port_patches.json').write_text('[1]')
    env.log.write_text('')
    assert run(env).returncode == 0 and tools_called(env) == []


def test_a_build_from_before_hashes_is_stale_when_a_ported_file_is_newer(env):
    # oaiq-122: oaiq-011's state (snapshot 59dd682) had no input hashes on build/config; --upgrade re-ported and
    # rewrote Compat.lean (the compat shim grew), build was skipped, and graph paired the old .olean's
    # declaration ranges with the new text: bundle 000 carved `Finset.equivOfEq` for a compat lemma
    assert run(env, *ARGS).returncode == 0
    st = json.load(open(env.dir / 'pipeline_state.json'))
    for rec in st['steps'].values():
        rec.pop('in', None)
    for s in ('build', 'wsbuild', 'config'):
        st['steps'][s]['finished'] = '2026-10-26T13:02:44'
    json.dump(st, open(env.dir / 'pipeline_state.json', 'w'))
    (env.ws / 'Solutions' / 'F' / 'Compat.lean').write_text('-- grown\n')
    env.log.write_text('')
    r = run(env, '--stop-after', 'build')
    assert r.returncode == 0, r.stdout + r.stderr
    assert any(c[0] == 'oai_build_modules' for c in tools_called(env)) and 'stale: build' in r.stdout, (tools_called(env), r.stdout)


def test_patches_added_to_a_state_from_before_hashes_existed_reruns_filter_patches(env):
    # oaiq-119: a carve from before input hashes, run without patches (filter_patches `skipped`, no `in`),
    # got a patches file in pipeline.json; the resume went straight to `measure` on the unpatched port
    assert run(env, *ARGS).returncode == 0
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['steps']['filter_patches']['status'] == 'skipped'
    for rec in st['steps'].values():
        rec.pop('in', None)
    json.dump(st, open(env.dir / 'pipeline_state.json', 'w'))
    (env.tmp / 'patches.json').write_text('[{"old": "a", "new": "b"}]')
    pj = json.load(open(env.dir / 'pipeline.json'))
    pj['patches'] = str(env.tmp / 'patches.json')
    json.dump(pj, open(env.dir / 'pipeline.json', 'w'))
    (env.dir / 'port_patches.json').write_text('[{"old": "a", "new": "b"}]')
    env.log.write_text('')
    r = run(env)
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert seq and seq[0] == ('carve_prep', 'filter-patches') and 'stale' in r.stdout, (seq, r.stdout)
    assert any(c[0] == 'oai_port_modules' for c in seq) and ('carve', 'plan') in seq


def test_from_still_forgets_the_step_and_everything_after(env):
    assert run(env, *ARGS).returncode == 0
    env.log.write_text('')
    assert run(env, '--from', 'graph', '--stop-after', 'plan').returncode == 0
    assert tools_called(env) == [('carve', 'graph'), ('carve_prep', 'ext-defs'), ('carve', 'plan')]


def test_calibration_excuses_accepted_items_under_the_hard_cap():
    # pieces under the cap are excused anyway (test_a_piece_under_the_cap_never_forces_a_replan);
    # accept_over excuses another item, e.g. a bundle one declaration re-planning cannot split
    plan = _plan({'B0': 55, 'B1': 10})
    times = {'bundle:B0': _t(101), 'bundle:B1': _t(5)}
    assert CP.calibration(plan, times, 8.0, 55)['over']
    assert CP.calibration(plan, times, 8.0, 55, accepted=['bundle:B0'])['over'] == []
    # the hard cap still applies to an accepted item
    assert CP.calibration(plan, {'bundle:B0': _t(250)}, 8.0, 55, accepted=['bundle:B0'])['over']


# ---- lean_src must be the root's import closure (2026-10-27) -------------------------------------
# oaiq-033/034/038/040/046/048: after a GitHub 429, workers passed the whole OpenAI tree (1.4 GB,
# 121,736 modules) as --lean-src; filter_patches and port then took every OAI.* module as input
# (25-50 min, then ~340 "not ported" lines, or a port of everything).

def _tree(root, outside):
    lean = root / 'lean'
    (lean / 'OAI' / 'Pre').mkdir(parents=True)
    (lean / 'OAI' / 'Pre' / 'Main.lean').write_text('import Mathlib\nimport OAI.Pre.A\n')
    (lean / 'OAI' / 'Pre' / 'A.lean').write_text('import Mathlib\n')
    (lean / 'OAI' / 'Other').mkdir(parents=True)
    for i in range(outside):
        (lean / 'OAI' / 'Other' / ('M%d.lean' % i)).write_text('import Mathlib\n')
    return lean


def test_closure_check_counts_modules_outside_the_closure(tmp_path):
    sys.path.insert(0, ROOT)
    from p2mlib import carvepipeline as CP
    lean = _tree(tmp_path, 3)
    assert CP.outside_closure(str(lean), 'OAI.Pre.Main') == (3, 2)
    assert CP.outside_closure(str(_tree(tmp_path / 'b', 0)), 'OAI.Pre.Main') == (0, 2)


def test_a_whole_tree_as_lean_src_is_refused_before_port(env):
    lean = _tree(env.tmp / 'whole', 60)
    r = run(env, *ARGS, '--lean-src', str(lean), '--stop-after', 'port')
    assert r.returncode != 0 and 'import closure' in (r.stdout + r.stderr)
    assert ('oai_port_modules', str(lean)) not in tools_called(env)


def test_a_closure_only_lean_src_passes(env):
    lean = _tree(env.tmp / 'closure', 0)
    r = run(env, *ARGS, '--lean-src', str(lean), '--stop-after', 'port')
    assert r.returncode == 0, r.stderr
    assert ('oai_port_modules', str(lean)) in tools_called(env)


def test_a_bare_def_name_means_the_definitions_module(env):
    # oaiq-042: `--def Def_CriticalStripMass` reached `lake build Def_CriticalStripMass` ("unknown
    # target") after an hour of fetch, port and build
    run(env, *ARGS, '--def', 'Def_A', '--stop-after', 'inputs')
    assert json.load(open(env.dir / 'pipeline.json'))['defs'] == ['Definitions.Def_A']


def test_a_bare_def_name_stored_before_the_rule_is_read_as_the_definitions_module(env):
    # oaiq-125: oaiq-022's pipeline.json (2026-10-26) held a bare "Def_AffineBernstein", so its resume
    # reached `lake build Def_AffineBernstein` ("unknown target") in wsbuild
    run(env, *ARGS, '--def', 'Def_A', '--stop-after', 'fetch')
    p = json.load(open(env.dir / 'pipeline.json'))
    p['defs'] = ['Def_A']
    json.dump(p, open(env.dir / 'pipeline.json', 'w'))
    r = run(env, '--def', 'Def_A', '--stop-after', 'inputs')
    assert r.returncode == 0, r.stdout + r.stderr
    assert json.load(open(env.dir / 'pipeline.json'))['defs'] == ['Definitions.Def_A']


# ---- --detach / --wait (2026-10-27) ------------------------------------------------------------
# oaiq-033/034/036/038/041/042/046/049: the driver ran inside a Bash background command, which the
# harness kills at 2 h, mid-build or mid-graph. Detached, the driver is its own systemd user unit;
# what an agent arms is a --wait, and a killed wait costs nothing.

def _cp():
    sys.path.insert(0, SCRIPTS)
    import carve_pipeline
    return carve_pipeline


def test_detach_command_runs_the_same_arguments_as_a_user_unit(tmp_path):
    cp = _cp()
    env = {'PATH': '/x/lean-cap:/usr/bin', 'HOME': '/h', 'P2M_WORKSPACE': '/ws', 'LEAN_PRIORITY': '7', 'SECRET': 's'}
    unit, cmd = cp.detach_command(str(tmp_path / 'carve'), ['--from', 'graph', '--detach'], '/s/carve_pipeline.py', env)
    assert unit.startswith('carve-') and cmd[:3] == ['systemd-run', '--user', '--unit=' + unit]
    assert '--collect' in cmd and '-p' in cmd and 'WorkingDirectory=%s' % (tmp_path / 'carve') in cmd
    for kv in ('PATH=/x/lean-cap:/usr/bin', 'HOME=/h', 'P2M_WORKSPACE=/ws', 'LEAN_PRIORITY=7'):
        assert '--setenv=' + kv in cmd
    assert not any('SECRET' in c for c in cmd)
    inner = cmd[-1]
    assert '/s/carve_pipeline.py' in inner and '--from graph' in inner and '--detach' not in inner
    assert '== driver exit' in inner and 'driver.log' in inner
    assert cp.detach_command(str(tmp_path / 'carve'), [], 'x', env)[0] == unit   # one unit name per carve


def test_wait_reads_the_last_detached_run():
    cp = _cp()
    assert cp.wait_result('') is None
    assert cp.wait_result('== detached 1\n== driver exit 1\n== detached 2\nrunning graph\n') is None
    assert cp.wait_result('== detached 1\n== driver exit 1\n== detached 2\npipeline ok\n== driver exit 0\n') == 0
    assert cp.wait_result('== detached 1\nstep failed\n== driver exit 1\n') == 1



def test_a_piece_under_the_cap_never_forces_a_replan():
    # oaiq-035/037 (KMedian): one piece measured 101-106 s against a 88 s limit; calibrate raised the
    # scale twice (~1 h of measuring each, 11 -> 80 bundles), then stopped. A piece is a proof: it can
    # be resubmitted, and the rule is to submit as is and split after two real timeouts. Bundles and
    # statements freeze at publish, so they keep the strict limit.
    r = CP.calibration(_plan({'B0': 55}, {'P': 46}), {'bundle:B0': _t(20), 'piece:P': _t(106)}, 8, 55)
    assert r['over'] == [] and r['new_scale'] == 8
    r = CP.calibration(_plan({'B0': 55}, {'P': 46}), {'bundle:B0': _t(250), 'piece:P': _t(250)}, 8, 55)
    assert [x[0] for x in r['over']] == ['bundle:B0', 'piece:P']
    # oaiq-031: a 192 s piece timed out three times at the verifier's 300 s; pieces are excused only
    # up to 120 s (dbenbenn 2026-10-29, lowered from 150: 118-126 s timed out 3x in oaiq-078, but 125 s and
    # 162 s passed on a retry; a slow submit costs only wall-clock, a needless re-plan costs hours)
    r = CP.calibration(_plan({'B0': 55}, {'P': 10}), {'bundle:B0': _t(20), 'piece:P': _t(192)}, 8, 55)
    assert [x[0] for x in r['over']] == ['piece:P']
    r = CP.calibration(_plan({'B0': 55}, {'P': 10}), {'bundle:B0': _t(20), 'piece:P': _t(135)}, 8, 55)
    assert [x[0] for x in r['over']] == ['piece:P']
    r = CP.calibration(_plan({'B0': 55}, {'P': 10}), {'bundle:B0': _t(20), 'piece:P': _t(118)}, 8, 55)
    assert r['over'] == []
    r = CP.calibration(_plan({'B0': 55}), {'bundle:B0': _t(106)}, 8, 55)
    assert [x[0] for x in r['over']] == ['bundle:B0']


def test_upgrade_works_when_run_from_the_old_snapshot(env, monkeypatch):
    # oaiq-034: `--upgrade` invoked through the carve's old snapshot (the path an agent had recorded)
    # silently kept the old sha, and the port re-ran with the old rewrite in 2 s
    monkeypatch.setenv('STUB_FAIL', 'carve plan')
    run(env, *ARGS)
    old = json.load(open(env.dir / 'pipeline_state.json'))['snapshot']['path']
    write_tools(env.repo, 'v2')
    git(env.repo, 'add', '-A')
    git(env.repo, 'commit', '-qm', 'v2')
    monkeypatch.delenv('STUB_FAIL')
    env.log.write_text('')
    r = subprocess.run([sys.executable, os.path.join(old, 'prove2me', 'scripts', 'carve_pipeline.py'), str(env.dir),
                        '--upgrade', '--redo', 'dryrun'], capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert {c['version'] for c in calls(env)} == {'v2'}
    assert json.load(open(env.dir / 'pipeline_state.json'))['snapshot']['sha'] == git(env.repo, 'rev-parse', 'HEAD')


def test_prose_template_gets_the_sources_for_its_module_links(env):
    # oaiq-035: with oai_meta.json lacking lean_root, the guessed module paths doubled a directory
    # (KMedian/KMedian/Analysis/..., 225 broken links); the pipeline knows the sources, so it says
    run(env, *ARGS, '--stop-after', 'prose')
    prose = [c for c in calls(env) if c.get('tool') == 'carve_prep' and c['argv'][0] == 'prose-template']
    a = prose[0]['argv']
    assert a[a.index('--lean-root') + 1] == str(env.dir / 'src' / 'lean')



def test_a_slow_piece_alone_stops_calibrate_with_the_forcing_hint(env, monkeypatch):
    # oaiq-031: a piece of 20 private `decide +kernel` lemmas measured 192 s (planned 10 s); re-planning
    # does not shrink a piece (KMedian's stayed at 106 s through two), so calibrate stops at once and
    # says what worked: force the lemmas by their graph node names (20 pieces of ~11 s)
    work = env.dir / 'carve_work'
    work.mkdir(parents=True, exist_ok=True)
    (work / 'plan.json').write_text(json.dumps(_plan({'B0': 55}, {'OAI.X.certificate_valid': 10})))
    (work / 'times.json').write_text(json.dumps({'bundle:B0': _t(20), 'piece:OAI.X.certificate_valid': _t(192)}))
    r = run(env, *ARGS, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}))
    assert r.returncode == 1
    assert 'piece:OAI.X.certificate_valid' in r.stderr and 'forced' in r.stderr and 'decide +kernel' in r.stderr
    assert json.load(open(env.dir / 'pipeline_state.json')).get('replans', 0) == 0
    assert [t[0] for t in tools_called(env)].count('carve_measure') == 1


def test_meta_prefixes_must_be_the_ports(tmp_path):
    # oaiq-031: prefixes ["OAI.Algebra.AuslanderReiten"] (the result's folder) while the port strips
    # OAI.Algebra: 181 prose files linked lean/OAI/Algebra/AuslanderReiten/AuslanderReiten/... (404)
    lean = tmp_path / 'lean'
    (lean / 'OAI' / 'Algebra' / 'AuslanderReiten').mkdir(parents=True)
    meta = tmp_path / 'oai_meta.json'
    base = {'title': 'T', 'date': 'd', 'family': '1', 'commit': 'a' * 40}
    meta.write_text(json.dumps(dict(base, prefixes=['OAI.Algebra.AuslanderReiten'])))
    why = CP.check_meta(str(meta), str(lean), 'OAI.Algebra.AuslanderReiten.All')
    assert why and 'OAI.Algebra' in why and 'port' in why
    meta.write_text(json.dumps(dict(base, prefixes=['OAI.Algebra'])))
    assert CP.check_meta(str(meta), str(lean), 'OAI.Algebra.AuslanderReiten.All') is None


def test_vendored_packages_are_ported_with_the_oai_prefixes(tmp_path):
    # oaiq-083: JointDickman imports PrimeNumberTheoremAnd and StrongPNT, third-party packages the
    # openai/math repo does not ship; their sources placed beside OAI/ in src/lean must be ported
    # (as modules under their own top directory) and must not make the OAI-only meta prefixes wrong
    lean = tmp_path / 'lean'
    (lean / 'OAI' / 'NumberTheory').mkdir(parents=True)
    (lean / 'PrimeNumberTheoremAnd' / 'Erdos970').mkdir(parents=True)
    (lean / 'PrimeNumberTheoremAnd' / 'Erdos970' / 'A.lean').write_text('import Mathlib\n')
    (lean / 'StrongPNT').mkdir()
    (lean / 'StrongPNT' / 'B.lean').write_text('import Mathlib\n')
    (lean / 'Empty').mkdir()
    assert CP.openai_prefixes(str(lean)) == ['OAI.NumberTheory', 'PrimeNumberTheoremAnd', 'StrongPNT']
    meta = tmp_path / 'oai_meta.json'
    meta.write_text(json.dumps({'title': 'T', 'date': 'd', 'family': '12', 'commit': 'a' * 40,
                                'prefixes': ['OAI.NumberTheory']}))
    assert CP.check_meta(str(meta), str(lean), 'OAI.NumberTheory.Main') is None


# ---- config_set edits after `config` ran (oaiq-051, 2026-10-27) ----------------------------------
# A post-carve proof fix goes in config `patches`; set in pipeline.json's config_set on a resume, it
# never reached config.json (the config step was done), so measure kept failing on unpatched text.

def test_a_changed_config_set_reaches_config_json_and_reruns_from_gen(env):
    run(env, *ARGS, '--config-set', json.dumps({'budget_note': 'a'}), '--stop-after', 'measure')
    cfg_path = env.dir / 'config.json'
    cfg = json.load(open(cfg_path))
    cfg['time_scale'] = 8                                    # what calibrate wrote: must survive
    json.dump(cfg, open(cfg_path, 'w'))
    p = json.load(open(env.dir / 'pipeline.json'))
    p['config_set'] = {'budget_note': 'a', 'patches': 'carve_patches.json'}
    json.dump(p, open(env.dir / 'pipeline.json', 'w'))
    env.log.write_text('')
    r = run(env, '--stop-after', 'measure')
    assert r.returncode == 0, r.stderr
    cfg = json.load(open(cfg_path))
    assert cfg['patches'] == 'carve_patches.json' and cfg['time_scale'] == 8
    called = tools_called(env)
    assert ('carve_prep', 'config') not in called and called[0] == ('carve', 'gen')
    assert 'config_set changed' in r.stdout
    # another key re-plans
    p['config_set']['forced_note'] = 1
    json.dump(p, open(env.dir / 'pipeline.json', 'w'))
    env.log.write_text('')
    run(env, '--stop-after', 'measure')
    assert tools_called(env)[0] == ('carve', 'plan')


def test_a_config_set_added_to_a_state_from_before_the_record_still_applies(env):
    # oaiq-120: a carve from before `config_set_applied` was recorded; config_set gained `frozen`/`forced` on the
    # resume, which took it as already applied, so the run went straight to publish with the old plan
    run(env, *ARGS, '--stop-after', 'measure')
    sp = env.dir / 'pipeline_state.json'
    st = json.load(open(sp))
    st.pop('config_set_applied', None)
    json.dump(st, open(sp, 'w'))
    p = json.load(open(env.dir / 'pipeline.json'))
    p['config_set'] = {'forced_note': 1}
    json.dump(p, open(env.dir / 'pipeline.json', 'w'))
    env.log.write_text('')
    r = run(env, '--stop-after', 'measure')
    assert r.returncode == 0, r.stderr
    assert json.load(open(env.dir / 'config.json'))['forced_note'] == 1
    assert tools_called(env)[0] == ('carve', 'plan')
    # nothing changed: nothing re-runs
    env.log.write_text('')
    run(env, '--stop-after', 'measure')
    assert ('carve', 'plan') not in tools_called(env)


def test_measure_keeps_going_past_a_failed_file(env):
    # oaiq-051: carve_measure stopped at the first failing proof, ~12 min per fix
    run(env, *ARGS, '--stop-after', 'measure')
    m = [c for c in calls(env) if c.get('tool') == 'carve_measure'][0]
    assert '--keep-going' in m['argv']


def test_a_replan_sets_aside_the_repairs_of_the_old_bundle_numbering(env, monkeypatch):
    # work/repairs.json keys cuts by file name (Def_X030.lean); a re-plan renumbers the bundles, so
    # the old cuts would be re-applied to different files (oaiq-039: C030 lost two needed imports)
    _calibration_setup(env, monkeypatch, {'bundle:B0': _t(30), 'bundle:B1': _t(50)})
    (env.dir / 'carve_work' / 'repairs.json').write_text(json.dumps({'Def_X030.lean': ['import Definitions.Def_X007']}))
    r = run(env, *ARGS, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}))
    assert r.returncode == 0, r.stdout + r.stderr
    assert not (env.dir / 'carve_work' / 'repairs.json').exists()
    assert (env.dir / 'carve_work' / 'repairs.before-replan-1.json').exists()



def test_meta_needs_the_prose_keys_at_config(tmp_path):
    # oaiq-066: a meta without `family` passed config and crashed publish_prep with a KeyError after the
    # hour of measuring; the prose template's own check came later still
    lean = tmp_path / 'lean'
    (lean / 'OAI' / 'Pre').mkdir(parents=True)
    meta = tmp_path / 'oai_meta.json'
    good = {'title': 'T', 'date': 'd', 'family': '250', 'commit': 'a' * 40, 'prefixes': ['OAI.Pre']}
    meta.write_text(json.dumps(good))
    assert CP.check_meta(str(meta), str(lean), 'OAI.Pre.Main') is None
    for k in ('title', 'date', 'family', 'commit'):
        meta.write_text(json.dumps({x: v for x, v in good.items() if x != k}))
        why = CP.check_meta(str(meta), str(lean), 'OAI.Pre.Main')
        assert why and repr(k) in why, k
    meta.write_text(json.dumps(dict(good, commit='adc7f12')))
    assert '40' in CP.check_meta(str(meta), str(lean), 'OAI.Pre.Main')


def test_publish_runs_again_whenever_publish_is_asked(env):
    # oaiq-065/071: after a re-split, `--publish` said "pipeline ok" in 2 s because the publish step
    # was recorded done; split_run resumes from its run state, so running it again is always safe
    assert run(env, *ARGS, '--publish').returncode == 0
    env.log.write_text('')
    assert run(env, '--publish').returncode == 0
    assert ('split_run', 'publish/run.json') in tools_called(env)
    go = [c['argv'] for c in calls(env) if c.get('tool') == 'split_run']
    assert any('--go' in a for a in go)


def _pieces_over(env, times):
    work = env.dir / 'carve_work'
    work.mkdir(parents=True, exist_ok=True)
    plan = _plan({'B0': 55}, {'P%d' % i: 40 for i in range(len(times))})
    (work / 'plan.json').write_text(json.dumps(plan))
    t = {'bundle:B0': _t(20)}
    t.update({'piece:P%d' % i: _t(s) for i, s in enumerate(times)})
    (work / 'times.json').write_text(json.dumps(t))


def test_pieces_uniformly_over_plan_replan_at_their_ratio(env, monkeypatch):
    # oaiq-073 (VlasovMaxwell): 10 pieces at 151-203 s against plans of 32-52 s (ratio 3.5-4.3, heavy
    # analysis, no kernel computation); calibrate stopped, and raising time_scale to ~4 by hand re-planned
    # into 364 items that all fitted. Several pieces over by a similar large ratio: the model underestimates
    # this port, so re-plan at the median ratio.
    _pieces_over(env, [160, 170, 155])
    (env.repo / 'prove2me' / 'scripts' / 'carve_measure.py').write_text(CALIBRATING_MEASURE)
    git(env.repo, 'add', '-A')
    git(env.repo, 'commit', '-qm', 'calibrating measure stub')
    monkeypatch.setenv('STUB_TIMES_AFTER', json.dumps({'bundle:B0': _t(20), 'piece:P0': _t(40),
                                                       'piece:P1': _t(45), 'piece:P2': _t(38)}))
    r = run(env, *ARGS, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}), '--stop-after', 'calibrate')
    assert r.returncode == 0, r.stderr
    cfg = json.load(open(env.dir / 'config.json'))
    assert cfg['time_scale'] == round(1.2 * 160 / 40, 1)
    assert json.load(open(env.dir / 'pipeline_state.json'))['replans'] == 1


def test_a_lone_or_scattered_slow_piece_still_stops_with_the_profiling_hint(env, monkeypatch):
    # oaiq-031/075: one slow piece is something specific (kernel computation; or oaiq-075's statement whose
    # .olean serialization took 316 s while elaboration took 4 s): profile it, don't re-plan
    _pieces_over(env, [192])
    r = run(env, *ARGS, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}))
    assert r.returncode == 1 and 'olean' in r.stderr and 'profiler' in r.stderr
    assert json.load(open(env.dir / 'pipeline_state.json')).get('replans', 0) == 0


def test_names_are_checked_right_after_gen(env):
    # oaiq-068, oaiq-074: names already live with other text stopped publish after ~6 h of porting and
    # measuring; the same lookup split_run's dry run does now runs right after gen
    run(env, *ARGS, '--stop-after', 'measure')
    seq = tools_called(env)
    i = seq.index(('carve', 'gen'))
    assert seq[i + 1] == ('carve_prep', 'name-check')
    assert seq.index(('carve_prep', 'name-check')) < [t[0] for t in seq].index('carve_measure')


def test_name_check_builds_a_read_only_run_from_the_carve(tmp_path, monkeypatch):
    sys.path.insert(0, SCRIPTS)
    import carve_prep as CPR
    from p2mlib import splitrun as R
    work, out = tmp_path / 'work', tmp_path / 'out'
    (out / 'lib').mkdir(parents=True)
    work.mkdir()
    (work / 'plan.json').write_text('{}')
    seen = {}

    class FakeRunner:
        def __init__(self, cfg, api):
            seen['cfg'] = cfg
            seen['readonly'] = isinstance(api, R.ReadOnly)

        def reconcile(self, write=True):
            seen['write'] = write
            return {'statement:A.t': 'id1'}, [{'item': 'bundle:B0', 'kind': 'bundle', 'name': 'B0', 'id': 'x',
                                                'author': 'someone', 'file': str(out / 'lib' / 'Def_B0.lean'),
                                                'diff': 'their text'}]
    monkeypatch.setattr(R, 'Runner', FakeRunner)
    monkeypatch.setattr(R, 'LiveApi', lambda: object())
    cfg = {'plan': str(work / 'plan.json'), 'out': str(out), 'work': str(work)}
    ok, msg = CPR.name_check(cfg)
    assert not ok and 'B0' in msg and 'statement_suffix' in msg
    assert seen['readonly'] and seen['write'] is False
    assert seen['cfg']['plan'] == str(work / 'plan.json') and seen['cfg']['out'] == str(out)
    assert not os.path.exists(seen['cfg']['state'])            # nothing written


def test_calibration_reports_a_slow_statement_apart_and_accept_over_does_not_excuse_it():
    # opus-kadison (oaiq-039): statements at 110 s and 176 s published, then every verify that imported
    # them failed ("Failed to resolve platform imports: Module compilation timed out"); calibrate never
    # looked at statements
    plan = dict(_plan({'B0': 55}), stubs={'A.slow': {}, 'A.fine': {}, 'A.live': {}}, external=['A.ext'])
    times = {'bundle:B0': _t(20), 'statement:A.slow': _t(110), 'statement:A.fine': _t(16),
             'statement:A.live': _t(120), 'statement:A.ext': _t(300)}
    r = CP.calibration(plan, times, 1.2, 55, frozen=['A.live'], accepted=['statement:A.slow'])
    assert r['over'] == [] and r['statements_over'] == [('statement:A.slow', 110)]


def test_a_slow_statement_stops_calibrate_with_the_abbrev_remedy(env):
    work = env.dir / 'carve_work'
    work.mkdir(parents=True, exist_ok=True)
    (work / 'plan.json').write_text(json.dumps(dict(_plan({'B0': 55}), stubs={'A.big': {}})))
    (work / 'times.json').write_text(json.dumps({'bundle:B0': _t(20), 'statement:A.big': _t(176)}))
    r = run(env, *ARGS, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}))
    assert r.returncode == 1 and 'A.big' in r.stderr and 'abbrev' in r.stderr
    assert json.load(open(env.dir / 'pipeline_state.json')).get('replans', 0) == 0


# ---- port rules, LeanInfo and config consumers are step inputs (oaiq-047, oaiq-085, oaiq-092) ----------

def _commit(env, rel, text, msg='edit'):
    p = env.repo / 'prove2me' / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    git(env.repo, 'add', '-A')
    git(env.repo, 'commit', '-qm', msg)


def _ported(env):
    return [c for c in calls(env) if c.get('tool') == 'oai_port_modules']


def test_upgrade_with_changed_port_rules_ports_again_by_itself(env):
    # oaiq-085/092: after a skill fix to an oaiport rewrite, `--upgrade` kept the old ported text and the
    # build failed the same way; it took `--upgrade --redo port`
    assert run(env, *ARGS).returncode == 0
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# a new rewrite\n')
    env.log.write_text('')
    r = run(env, '--upgrade')
    assert r.returncode == 0, r.stdout + r.stderr
    assert _ported(env) and 'stale: port' in r.stdout and 'port rules' in r.stdout


def test_a_changed_compat_source_ports_again_too(env):
    _commit(env, 'lean/compat_4_34.lean', '-- compat v1\n')
    assert run(env, *ARGS).returncode == 0
    _commit(env, 'lean/compat_4_34.lean', '-- compat v2\n')
    env.log.write_text('')
    r = run(env, '--upgrade', '--stop-after', 'port')
    assert r.returncode == 0 and _ported(env), r.stdout + r.stderr


def test_a_compat_change_after_the_build_warns_that_every_module_rebuilds(env):
    # oaiq-088: four snapshot changes rebuilt all 2,385 modules, each starting `Built ...Compat`: every
    # snapshot's compat_4_34.lean differed, and every ported module imports Compat. The build depends on
    # nothing else of the snapshot (an unchanged port replays: test_oai_build_modules); say it up front
    sys.path.insert(0, ROOT)
    from p2mlib import oaiport
    _commit(env, 'lean/compat_4_34.lean', 'theorem v1 : True := trivial\n')
    assert run(env, *ARGS, '--stop-after', 'build').returncode == 0
    compat = env.ws / 'Solutions' / 'F' / 'Compat.lean'
    compat.write_text('import Mathlib\n\n' + oaiport.compat_block('theorem v1 : True := trivial\n')[0])
    _commit(env, 'scripts/carve.py', (env.repo / 'prove2me' / 'scripts' / 'carve.py').read_text() + '\n# other fix\n')
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# a new rewrite\n')
    r = run(env, '--upgrade', '--stop-after', 'port')
    assert r.returncode == 0 and 'stale: port' in r.stdout and 'WARNING' not in r.stdout, r.stdout
    _commit(env, 'lean/compat_4_34.lean', 'theorem v1 : True := trivial\ntheorem v2 : True := trivial\n')
    r = run(env, '--upgrade', '--stop-after', 'port')
    assert r.returncode == 0 and 'compat shims' in r.stdout and '--keep-port' in r.stdout, r.stdout


def test_upgrade_that_leaves_the_port_rules_alone_does_not_port_again(env):
    assert run(env, *ARGS).returncode == 0
    _commit(env, 'scripts/carve.py', (env.repo / 'prove2me' / 'scripts' / 'carve.py').read_text() + '\n# other fix\n')
    env.log.write_text('')
    r = run(env, '--upgrade')
    assert r.returncode == 0, r.stdout + r.stderr
    assert not _ported(env) and ('carve', 'graph') not in tools_called(env)


def test_changed_port_options_port_again(env):
    assert run(env, *ARGS).returncode == 0
    p = json.load(open(env.dir / 'pipeline.json'))
    p['compat_imports'] = 'narrow'
    json.dump(p, open(env.dir / 'pipeline.json', 'w'))
    env.log.write_text('')
    r = run(env, '--stop-after', 'port')
    assert r.returncode == 0 and _ported(env), r.stdout + r.stderr
    assert '--compat-imports' in _ported(env)[0]['argv']


def test_hide_instances_reach_every_ported_module_and_port_again(env):
    # oaiq-122: FactorGeneration builds its own CStarAlgebra/order instances on `M.toStarSubalgebra`, and the compat
    # block's global von Neumann instances (for Kadison similarity, whose closure shares modules with it) made `whnf`
    # time out; pipeline.json `hide_instances` hides them in every module through the port's --header
    assert run(env, *ARGS).returncode == 0
    p = json.load(open(env.dir / 'pipeline.json'))
    p['hide_instances'] = ['OAI.vonNeumannToStarSubalgebraIsClosed', 'OAI.starSubalgebraStarOrderedRing']
    json.dump(p, open(env.dir / 'pipeline.json', 'w'))
    env.log.write_text('')
    r = run(env, '--stop-after', 'port')
    assert r.returncode == 0 and _ported(env), r.stdout + r.stderr
    argv = _ported(env)[0]['argv']
    h = argv[argv.index('--header') + 1]
    assert open(h).read() == ('attribute [-instance] OAI.vonNeumannToStarSubalgebraIsClosed '
                              'OAI.starSubalgebraStarOrderedRing\n')
    filt = [c for c in calls(env) if c.get('tool') == 'carve_prep' and c['argv'][0] == 'filter-patches']
    assert all('--header' in c['argv'] for c in filt)


def _forget_rule_hashes(env):
    """A state written before the rule hashes were recorded."""
    st = json.load(open(env.dir / 'pipeline_state.json'))
    for rec in st['steps'].values():
        for k in list(rec.get('in') or {}):
            if k in ('port rules', 'filter rules', 'port options', 'LeanInfo tool'):
                del rec['in'][k]
    json.dump(st, open(env.dir / 'pipeline_state.json', 'w'))


def test_a_state_without_rule_hashes_compares_with_the_snapshot_that_ported(env):
    # the live carves of 2026-10-29 have no rule hash recorded; logs/port.log names the snapshot
    # that ported, so an --upgrade over a rule change still re-ports
    assert run(env, *ARGS).returncode == 0
    _forget_rule_hashes(env)
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# a new rewrite\n')
    env.log.write_text('')
    r = run(env, '--upgrade')
    assert r.returncode == 0 and _ported(env), r.stdout + r.stderr


def test_a_state_without_rule_hashes_is_not_stale_without_an_upgrade(env):
    assert run(env, *ARGS).returncode == 0
    _forget_rule_hashes(env)
    env.log.write_text('')
    assert run(env).returncode == 0 and tools_called(env) == []


def test_a_changed_leaninfo_reruns_graph_with_a_warning_before_plan(env):
    # oaiq-047: an upgrade across a LeanInfo.lean change left `graph` done, and `plan` re-ran LeanInfo
    # on 1259 modules one at a time for ~3 h with no output. Re-running `graph` instead does it in
    # parallel with progress, and the driver says what is coming first.
    _commit(env, 'lean/LeanInfo.lean', '-- v1\n')
    assert run(env, *ARGS, '--stop-after', 'graph').returncode == 0
    _commit(env, 'lean/LeanInfo.lean', '-- v2\n')
    env.log.write_text('')
    r = run(env, '--upgrade')
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert seq.index(('carve', 'graph')) < seq.index(('carve', 'plan')) and not _ported(env)
    assert 'LeanInfo' in r.stdout and '1 module' in r.stdout
    # once every step that loads the graph is done, a LeanInfo change costs nothing
    _commit(env, 'lean/LeanInfo.lean', '-- v3\n')
    env.log.write_text('')
    r = run(env, '--upgrade')
    assert r.returncode == 0 and tools_called(env) == [], r.stdout


def test_redo_config_that_changes_config_json_reruns_its_consumers(env):
    # oaiq-047: `--redo config` reset time_scale but left `plan` done; the old 2758-node plan was measured
    assert run(env, *ARGS).returncode == 0
    cfg = json.load(open(env.dir / 'config.json'))
    cfg['time_scale'] = 6.6                                  # what calibrate wrote
    json.dump(cfg, open(env.dir / 'config.json', 'w'))
    env.log.write_text('')
    r = run(env, '--redo', 'config')
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert seq[0] == ('carve_prep', 'config') and ('carve_prep', 'ext-defs') in seq and ('carve', 'plan') in seq
    assert ('carve', 'graph') not in seq                     # what graph reads did not change


def test_redo_config_with_the_same_config_json_leaves_the_rest(env):
    assert run(env, *ARGS).returncode == 0
    env.log.write_text('')
    assert run(env, '--redo', 'config').returncode == 0
    assert tools_called(env) == [('carve_prep', 'config')]


# ---- --wait reports this run's exit; --detach names what holds the carve (oaiq-084) -------------------

def test_wait_ignores_an_exit_line_of_another_run():
    # oaiq-084: `--wait` returned 0 at once while the unit was still in `publish`, reading an old
    # "driver exit 0". Each detached run carries an id, and only its own exit line ends it.
    cp = _cp()
    old = '== detached 1 run r1\npipeline ok\n== driver exit 0 run r1\n'
    assert cp.wait_result(old) == 0
    # a second --detach whose unit never started, then the first run's exit line lands after it
    assert cp.wait_result('== detached 1 run r1\n== detached 2 run r2\n== driver exit 0 run r1\n') is None
    assert cp.wait_result(old + '== detached 2 run r2\n== publish\n== driver exit 1 run r2\n') == 1
    # a log from before run ids
    assert cp.wait_result('== detached 1\n== driver exit 1\n') == 1


def test_detach_command_tags_the_exit_line_with_the_run(tmp_path):
    cp = _cp()
    unit, cmd = cp.detach_command(str(tmp_path / 'carve'), [], '/s/carve_pipeline.py', {}, run_id='r7')
    assert '== driver exit $? run r7' in cmd[-1]


def _wait_args(d, minutes):
    return type('A', (), {'dir': str(d), 'wait': minutes})()


def test_wait_keeps_waiting_while_the_unit_is_active(tmp_path, monkeypatch, capsys):
    # whatever the log says, an active unit is a run that has not ended
    cp = _cp()
    log = tmp_path / 'logs' / 'driver.log'
    log.parent.mkdir(parents=True)
    log.write_text('== detached 2026-10-28 22:51:00 run r1\npipeline ok\n== driver exit 0 run r1\n')
    states = iter([True, True, False])
    monkeypatch.setattr(cp, 'unit_active', lambda unit: next(states))
    monkeypatch.setattr(cp.time, 'sleep', lambda s: None)
    assert cp.wait(_wait_args(tmp_path, 100)) == 0
    out = capsys.readouterr().out
    assert 'run r1' in out and '2026-10-28 22:51:00' in out
    monkeypatch.setattr(cp, 'unit_active', lambda unit: True)
    assert cp.wait(_wait_args(tmp_path, 0)) == 4


def test_wait_says_when_the_run_had_already_ended(tmp_path, monkeypatch, capsys):
    cp = _cp()
    log = tmp_path / 'logs' / 'driver.log'
    log.parent.mkdir(parents=True)
    log.write_text('== detached 2026-10-28 22:51:00 run r1\npipeline ok\n== driver exit 0 run r1\n')
    monkeypatch.setattr(cp, 'unit_active', lambda unit: False)
    assert cp.wait(_wait_args(tmp_path, 100)) == 0
    assert 'already ended' in capsys.readouterr().out


def test_detach_refuses_at_once_naming_the_driver_that_holds_the_carve(env):
    # oaiq-084: a foreground `--stop-after prose` run kept the lock for 10 min after the harness
    # backgrounded it; the later --detach "started", its unit exited 3, and an hour went on stale logs
    assert run(env, *ARGS, '--stop-after', 'config').returncode == 0
    sys.path.insert(0, ROOT)
    from p2mlib import runlock
    key = runlock.dir_key('pipeline', str(env.dir))
    holder = subprocess.Popen([sys.executable, '-c', textwrap.dedent('''
        import sys, time
        sys.path.insert(0, %r)
        from p2mlib import runlock
        runlock.hold(%r, 'holder'); print('held', flush=True); time.sleep(60)''' % (ROOT, key)),
        '--stop-after', 'prose'], stdout=subprocess.PIPE, text=True, env=dict(os.environ))
    try:
        assert holder.stdout.readline().strip() == 'held'
        r = run(env, '--detach')
        assert r.returncode == 3, r.stdout + r.stderr
        assert 'pid %d' % holder.pid in r.stderr and '--stop-after prose' in r.stderr
        assert 'run' not in (env.dir / 'logs' / 'driver.log').read_text() if (env.dir / 'logs' / 'driver.log').exists() else True
    finally:
        holder.kill()


def test_once_publishing_started_a_port_rule_change_keeps_the_port_and_says_so(env):
    # live items freeze their text: a carve that has started publishing never re-ports by itself
    assert run(env, *ARGS, '--publish').returncode == 0
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# a new rewrite\n')
    env.log.write_text('')
    r = run(env, '--upgrade')
    assert r.returncode == 0, r.stdout + r.stderr
    assert not _ported(env) and 'publishing has started' in r.stdout and '--redo port' in r.stdout
    # the same once split_run has a run state (a --go run outside the pipeline)
    st = json.load(open(env.dir / 'pipeline_state.json'))
    st['steps'].pop('publish', None)
    json.dump(st, open(env.dir / 'pipeline_state.json', 'w'))
    (env.dir / 'publish').mkdir(exist_ok=True)
    (env.dir / 'publish' / 'run_state.json').write_text('{}')
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# another\n')
    env.log.write_text('')
    r = run(env, '--upgrade')
    assert r.returncode == 0 and not _ported(env), r.stdout + r.stderr


def test_closure_follows_module_system_imports(tmp_path):
    # `public import`, `meta import` and `import all M` are imports too (leantext.import_names)
    lean = tmp_path / 'lean' / 'OAI' / 'Pre'
    lean.mkdir(parents=True)
    (lean / 'Main.lean').write_text('module\npublic import OAI.Pre.A\nmeta import OAI.Pre.B\nimport all OAI.Pre.C\n')
    for m in 'ABC':
        (lean / (m + '.lean')).write_text('module\n')
    (lean / 'Other.lean').write_text('')
    assert CP.outside_closure(str(tmp_path / 'lean'), 'OAI.Pre.Main') == (1, 4)


# ---------------------------------------------------------------- overlap mode (2026-10-29)
# dbenbenn: "a slow proof really shouldn't need to block submitting definition bundles". Bundles and
# statements are measured, calibrated and checked first and published from a background publisher
# while the pieces are measured (oaiq-081: 194 bundles and 696 statements fine after ~1.5 h of
# measuring, then ~4 h more of pieces, five of them slow, before anything could publish).

MEASURE_HOOK = textwrap.dedent('''
    _kinds = sys.argv[sys.argv.index('--kinds') + 1].split(',') if '--kinds' in sys.argv else ['bundle', 'statement', 'piece']
    _i = open(os.environ['STUB_LOG']).read().count('"tool": "carve_measure"') - 1
    _seq = json.loads(os.environ.get('STUB_TIMES_SEQ', '[]'))
    _tp = os.path.join(os.getcwd(), 'carve_work', 'times.json')
    _t = json.load(open(_tp)) if os.path.exists(_tp) else {}
    if _i < len(_seq):
        _t.update({k: v for k, v in _seq[_i].items() if k.split(':')[0] in _kinds})
    json.dump(_t, open(_tp, 'w'))
    if os.environ.get('STUB_MEASURE_FAIL') in _kinds:
        print('piece FAIL'); sys.exit(1)
''')


def _overlap_carve(env, monkeypatch, pieces=None, bundles=None, stimes=None, seq=()):
    """A carve whose plan has bundles B0..., statements and pieces P0...; times all fine unless given."""
    work = env.dir / 'carve_work'
    work.mkdir(parents=True, exist_ok=True)
    pieces = pieces or {'P0': (10, 30), 'P1': (40, 30)}            # name: (planned cost, measured s)
    bundles = bundles or {'B0': (55, 20), 'B1': (55, 20)}
    plan = {'bundles': [{'name': n, 'cost': c, 'nodes': ['d_' + n, 'e_' + n], 'imports': []} for n, (c, _) in bundles.items()],
            'stubs': {n: {'bundles': ['B0']} for n in pieces},
            'pieces': {n: {'cost': c, 'keep': [n, 'lemma_' + n], 'bundles': ['B0'], 'imports': []}
                       for n, (c, _) in pieces.items()},
            'external': []}
    (work / 'plan.json').write_text(json.dumps(plan))
    t = {'bundle:' + n: _t(s) for n, (_, s) in bundles.items()}
    t.update({'statement:' + n: _t((stimes or {}).get(n, 5)) for n in pieces})
    t.update({'piece:' + n: _t(s) for n, (_, s) in pieces.items()})
    (work / 'times.json').write_text(json.dumps(t))
    monkeypatch.setenv('STUB_HOOK_carve_measure_config_json', MEASURE_HOOK)
    monkeypatch.setenv('STUB_TIMES_SEQ', json.dumps(list(seq)))
    return plan


def _raw(env):
    return env.log.read_text().splitlines()


def _index(lines, pred):
    return next(i for i, l in enumerate(lines) if pred(l))


def test_a_new_carve_is_in_overlap_mode_and_an_old_one_stays_classic(env):
    assert run(env, *ARGS_NEW, '--stop-after', 'config').returncode == 0
    assert json.load(open(env.dir / 'pipeline.json'))['overlap'] is True
    listing = run(env, '--list').stdout.split()
    assert 'measure_pieces' in listing and 'publish_early' in listing
    # a pipeline.json from before (no key): classic, also after --upgrade
    p = json.load(open(env.dir / 'pipeline.json'))
    del p['overlap']
    (env.dir / 'pipeline.json').write_text(json.dumps(p))
    assert 'measure_pieces' not in run(env, '--list').stdout.split()
    r = run(env, '--upgrade', '--stop-after', 'calibrate')
    assert r.returncode == 0, r.stderr
    measure = [c['argv'] for c in calls(env) if c.get('tool') == 'carve_measure']
    assert measure and all('--kinds' not in a for a in measure)


def test_overlap_measures_and_checks_bundles_and_statements_before_the_pieces(env, monkeypatch):
    _overlap_carve(env, monkeypatch)
    r = run(env, *ARGS_NEW)
    assert r.returncode == 0, r.stdout + r.stderr
    seq = [(c['tool'], c['argv']) for c in calls(env)]
    i = seq.index(('carve_measure', ['config.json', '--keep-going', '--kinds', 'bundle,statement']))
    j = seq.index(('carve_measure', ['config.json', '--keep-going', '--kinds', 'piece']))
    tail = [(t, a[0]) for t, a in seq[i:]]
    assert tail[:6] == [('carve_measure', 'config.json'), ('carve_prep', 'publish-prep'), ('carve_prep', 'prose-template'),
                        ('carve_prep', 'check-text'), ('split_run', 'publish/run_early.json'), ('carve_measure', 'config.json')]
    assert seq[i + 3][1][-2:] == ['--kinds', 'bundle,statement']           # check-text: no explanations yet
    after = [(t, a) for t, a in seq[j + 1:]]
    assert [x[0] for x in after] == ['carve_prep', 'carve_prep', 'carve_prep', 'split_run']
    assert after[0][1][0] == 'publish-prep' and after[0][1][-1] == '--sync'
    assert after[2][1][0] == 'check-text' and after[2][1][-2:] == ['--kinds', 'piece']   # prose checked before
    assert after[3][1] == ['publish/run.json']                                # the full dry run
    # without --publish nothing is published, and nothing started in the background
    assert not any(l.startswith('systemd-run') for l in _raw(env))
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert 'publish_early' not in st['steps'] and 'auto_config' not in st
    assert 'pieces fit' in (env.dir / 'logs' / 'calibrate.log').read_text()


def test_with_publish_bundles_and_statements_go_in_the_background_before_the_pieces_are_measured(env, monkeypatch):
    plan = _overlap_carve(env, monkeypatch)
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 0, r.stdout + r.stderr
    lines = _raw(env)
    i_bg = _index(lines, lambda l: l.startswith('systemd-run'))
    i_pieces = _index(lines, lambda l: '"--kinds", "piece"' in l)
    i_final = _index(lines, lambda l: '"tool": "split_run"' in l and '"--go"' in l)
    assert i_bg < i_pieces < i_final
    bg = lines[i_bg]
    assert '--unit=carve-pub-' in bg and 'split_run.py publish/run_early.json --go' in bg
    assert json.loads(lines[i_final])['argv'] == ['publish/run.json', '--go']
    # what goes out is frozen first: a later re-plan keeps every bundle and statement
    cfg = json.load(open(env.dir / 'config.json'))
    assert cfg['frozen']['bundles'] == ['B0', 'B1'] and cfg['frozen']['plan'] == str(env.dir / 'published' / 'plan.json')
    assert set(cfg['forced']) >= {'P0', 'P1'} and set(cfg['template_forced']) == {'P0', 'P1'}
    assert json.load(open(env.dir / 'published' / 'plan.json')) == plan
    # the pieces are released for exactly this plan
    import hashlib
    rel = json.load(open(env.dir / 'publish' / 'release.json'))
    assert rel['pieces'] == 'all'
    assert rel['plan_sha'] == hashlib.sha1((env.dir / 'publish' / 'plan.json').read_bytes()).hexdigest()
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['publisher']['unit'].startswith('carve-pub-') and st['steps']['publish_early']['status'] == 'done'


def test_publish_early_freezes_only_the_plans_bundles_and_statements(env, monkeypatch):
    # oaiq-122: publish/out/lib kept the files of earlier plans (an automatic split's statements, old bundle
    # numbers: 227 beside 83 published); freezing them all made every later re-plan that reused one of those
    # names fail "published or being published changed", though none was ever posted
    _overlap_carve(env, monkeypatch)
    lib = env.dir / 'out' / 'lib'
    lib.mkdir(parents=True)
    for f in ('Def_B0.lean', 'Def_B1.lean', 'Thm_P0.lean', 'Thm_P1.lean', 'Def_B7.lean', 'Thm_Stale_lemma.lean'):
        (lib / f).write_text('-- ' + f + '\n')
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 0, r.stdout + r.stderr
    assert sorted(os.listdir(env.dir / 'published' / 'lib')) == ['Def_B0.lean', 'Def_B1.lean', 'Thm_P0.lean', 'Thm_P1.lean']


def test_a_failing_piece_does_not_hold_back_the_bundles_and_statements(env, monkeypatch):
    # oaiq-081: rounds of piece compile errors (08:40: 6 pieces, nothing else) each held back everything
    _overlap_carve(env, monkeypatch)
    monkeypatch.setenv('STUB_MEASURE_FAIL', 'piece')
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 1 and "step 'measure_pieces' failed" in r.stderr
    assert any(l.startswith('systemd-run') for l in _raw(env))
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['steps']['publish_early']['status'] == 'done' and st['steps']['measure_pieces']['status'] == 'failed'


def test_forced_named_results_keep_their_written_prose_requirement(env, monkeypatch):
    _overlap_carve(env, monkeypatch)
    r = run(env, *ARGS_NEW, '--forced', 'P1', '--publish')
    assert r.returncode == 0, r.stderr
    cfg = json.load(open(env.dir / 'config.json'))
    assert cfg['template_forced'] == ['P0'] and set(cfg['forced']) >= {'P0', 'P1'}


def test_a_slow_piece_after_publishing_is_split_by_a_frozen_replan_of_that_piece_alone(env, monkeypatch):
    # oaiq-081: HighQueryCorrect.marked 283 s against a plan of 40 s. Its statements are live, so the
    # whole carve is not re-planned: only the declarations the piece kept cost their measured ratio
    _overlap_carve(env, monkeypatch, pieces={'P0': (10, 192), 'P1': (40, 30)},
                   seq=[{}, {}, {}, {'piece:P0': _t(40)}])
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 0, r.stdout + r.stderr
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['auto_config']['cost_factors'] == {'P0': 19.2, 'lemma_P0': 19.2}
    assert st['auto_split']['P0']['secs'] == 192 and st['piece_replans'] == 1 and st.get('replans', 0) == 0
    cfg = json.load(open(env.dir / 'config.json'))
    assert cfg['cost_factors'] == {'P0': 19.2, 'lemma_P0': 19.2} and cfg['frozen']['bundles'] == ['B0', 'B1']
    assert cfg.get('time_scale', 1.5) == 1.5 or 'time_scale' not in cfg
    seq = tools_called(env)
    assert seq.count(('carve', 'plan')) == 2 and seq.count(('carve', 'split')) == 0
    assert 'frozen re-plan' in (env.dir / 'logs' / 'calibrate.log').read_text()
    # a resumed config keeps the frozen part and the factors (they live in pipeline_state.json too)
    assert run(env, '--redo', 'config', '--stop-after', 'config').returncode == 0
    cfg = json.load(open(env.dir / 'config.json'))
    assert cfg['cost_factors'] == {'P0': 19.2, 'lemma_P0': 19.2} and 'frozen' in cfg and 'P0' in cfg['forced']


def test_the_automatic_split_may_promote_the_slow_pieces_private_lemmas(env, monkeypatch):
    # oaiq-091: pieces of 60 and 394 private lemmas (`traceLift_*`, `B_ACE_*`); the frozen re-plan could
    # promote public lemmas only, so each private one needed a hand `forced` entry by graph node name
    plan = _overlap_carve(env, monkeypatch, pieces={'P0': (10, 192), 'P1': (40, 30)},
                          seq=[{}, {}, {}, {'piece:P0': _t(40)}])
    priv = '_private.Solutions.F.M.0.OAI.X.traceLift_1'
    plan['pieces']['P0']['keep'].append(priv)
    plan['pieces']['P1']['keep'].append('_private.Solutions.F.M.0.OAI.X.other')
    (env.dir / 'carve_work' / 'plan.json').write_text(json.dumps(plan))
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 0, r.stdout + r.stderr
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['auto_config']['promote_private'] == [priv]          # the slow piece's only
    cfg = json.load(open(env.dir / 'config.json'))
    assert cfg['promote_private'] == [priv] and cfg['cost_factors'][priv] == 19.2
    assert run(env, '--redo', 'config', '--stop-after', 'config').returncode == 0
    assert json.load(open(env.dir / 'config.json'))['promote_private'] == [priv]


def test_a_piece_still_slow_after_its_automatic_split_stops_for_a_person(env, monkeypatch):
    _overlap_carve(env, monkeypatch, pieces={'P0': (10, 192), 'P1': (40, 30)}, seq=[{}, {}, {}, {'piece:P0': _t(180)}])
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 1
    assert "step 'calibrate_pieces'" in r.stderr and 'still over after an automatic split' in r.stderr
    assert 'accept_over' in r.stderr and 'frozen' in r.stderr
    assert not (env.dir / 'publish' / 'release.json').exists()
    assert tools_called(env).count(('carve', 'plan')) == 2


def test_a_slow_piece_whose_statement_is_the_cost_is_not_split(env, monkeypatch):
    # oaiq-075: 316 s of 328 in .olean serialization of the statement's type (`sorry` just as slow):
    # forcing lemmas cannot help, so no automatic split; the statement itself fits (80 s), so it is live
    _overlap_carve(env, monkeypatch, pieces={'P0': (10, 150), 'P1': (40, 30)}, stimes={'P0': 80})
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 1, r.stdout + r.stderr
    assert "step 'calibrate_pieces'" in r.stderr and 'the type is the cost' in r.stderr
    assert 'theorem _root_.solution' in r.stderr
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert not st['auto_config'].get('cost_factors') and st['steps']['publish_early']['status'] == 'done'
    assert tools_called(env).count(('carve', 'plan')) == 1


def test_a_lone_slow_piece_before_anything_is_published_stops_as_before(env, monkeypatch):
    _overlap_carve(env, monkeypatch, pieces={'P0': (10, 192), 'P1': (40, 30)})
    r = run(env, *ARGS_NEW)
    assert r.returncode == 1 and "step 'calibrate_pieces'" in r.stderr and 'profiler' in r.stderr
    assert 'auto_config' not in json.load(open(env.dir / 'pipeline_state.json'))


def test_one_late_slow_bundle_is_split_alone_and_only_what_imports_it_is_regenerated(env, monkeypatch):
    # dbenbenn 2026-10-29: oaiq-081's first calibrate re-planned all 194 bundles for three slow ones;
    # split just the slow bundle (carve.py split --only), keep every other bundle (and its time), and
    # regenerate and re-measure: gen rewrites the files, measure re-runs only changed text
    bundles = {'B%d' % i: (55, 20) for i in range(12)}
    bundles['B10'] = (55, 150)
    _overlap_carve(env, monkeypatch, bundles=bundles, seq=[{}, {'bundle:B10': _t(40), 'bundle:B12': _t(30)}])
    r = run(env, *ARGS_NEW, '--stop-after', 'calibrate')
    assert r.returncode == 0, r.stdout + r.stderr
    split = [c['argv'] for c in calls(env) if c.get('tool') == 'carve' and c['argv'][0] == 'split']
    assert len(split) == 1
    a = split[0]
    assert a[a.index('--only') + 1] == 'B10' and a[a.index('--limit') + 1] == '55'
    assert a[2] == str(env.dir / 'carve_work' / 'times.json')
    seq = tools_called(env)
    assert seq.count(('carve', 'plan')) == 1 and seq.count(('carve', 'gen')) == 2
    after_split = seq[seq.index(('carve', 'split')) + 1:]
    assert after_split[:4] == [('carve', 'gen'), ('carve_prep', 'name-check'), ('carve', 'order'), ('carve_measure', 'config.json')]
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['bundle_splits'] == 1 and st.get('replans', 0) == 0
    times = json.load(open(env.dir / 'carve_work' / 'times.json'))
    assert all(times['bundle:B%d' % i] == _t(20) for i in range(10))     # no other time was touched
    assert 'splitting B10 alone' in (env.dir / 'logs' / 'calibrate.log').read_text()


PROFILE_HOOK = textwrap.dedent('''
    if '--profile' in sys.argv:
        _w = os.path.join(os.getcwd(), 'carve_work')
        _p = os.path.join(_w, 'profiles.json')
        _all = json.load(open(_p)) if os.path.exists(_p) else {}
        for _it in sys.argv[sys.argv.index('--profile') + 1].split(','):
            _all[_it] = {'kind': 'serialization', 'message': 'serialization-bound: `.olean serialization` 91 s of 92 s '
                         '(its one declaration: OAI.KL.bottInterKernelFirst_surjective); name the large sides '
                         'with `abbrev`s', 'key': None}
        json.dump(_all, open(_p, 'w'))
        sys.exit(0)
''')


def _profiled(env):
    return [c['argv'] for c in calls(env) if c.get('tool') == 'carve_measure' and '--profile' in c['argv']]


def test_a_slow_bundle_of_one_declaration_is_profiled_not_split(env, monkeypatch):
    # oaiq-124: calibrate split OAIQ124K032 until it was one 7-line theorem, still 92 s (limit 88):
    # `.olean serialization` 91 s. A bundle of one declaration cannot be split: profile it once, and stop
    # with the diagnosis naming the declaration
    plan = _overlap_carve(env, monkeypatch, bundles={'B0': (55, 20), 'B1': (55, 20), 'K032': (55, 92)})
    plan['bundles'][2]['nodes'] = ['OAI.KL.bottInterKernelFirst_surjective']
    (env.dir / 'carve_work' / 'plan.json').write_text(json.dumps(plan))
    monkeypatch.setenv('STUB_HOOK_carve_measure_config_json', PROFILE_HOOK + MEASURE_HOOK)
    r = run(env, *ARGS_NEW, '--stop-after', 'calibrate')
    assert r.returncode == 1
    assert 'splitting cannot shrink' in r.stderr and 'K032 (92 s): serialization-bound' in r.stderr
    assert 'bottInterKernelFirst_surjective' in r.stderr and 'accept_over' in r.stderr
    assert _profiled(env) == [['config.json', '--profile', 'bundle:K032']]
    assert ('carve', 'split') not in tools_called(env) and tools_called(env).count(('carve', 'plan')) == 1
    assert 'cannot shrink: K032' in (env.dir / 'logs' / 'calibrate.log').read_text()
    # a resume reuses the recorded profile of the same text instead of compiling again
    times = json.load(open(env.dir / 'carve_work' / 'times.json'))
    times['bundle:K032']['key'] = 'k1'
    (env.dir / 'carve_work' / 'times.json').write_text(json.dumps(times))
    prof = json.load(open(env.dir / 'carve_work' / 'profiles.json'))
    prof['bundle:K032']['key'] = 'k1'
    (env.dir / 'carve_work' / 'profiles.json').write_text(json.dumps(prof))
    r = run(env, '--stop-after', 'calibrate')
    assert r.returncode == 1 and 'serialization-bound' in r.stderr and len(_profiled(env)) == 1


def test_a_split_that_returns_the_bundle_unchanged_profiles_it_instead_of_another_round(env, monkeypatch):
    # oaiq-124: "34 bundles -> 34": `carve.py split --only` returned the slow bundle as it was; the next
    # rounds cannot do better. Other slow bundles are still split first; the unshrinkable one is profiled
    # once only it is left
    _overlap_carve(env, monkeypatch, bundles={'B%d' % i: (55, 20) for i in range(10)} | {'B10': (55, 150)},
                   seq=[{}, {'bundle:B10': _t(140)}])
    monkeypatch.setenv('STUB_HOOK_carve_measure_config_json', PROFILE_HOOK + MEASURE_HOOK)
    r = run(env, *ARGS_NEW, '--stop-after', 'calibrate')
    assert r.returncode == 1, r.stdout + r.stderr
    assert tools_called(env).count(('carve', 'split')) == 1          # the stub split returned it unchanged
    assert _profiled(env) == [['config.json', '--profile', 'bundle:B10']]
    assert "step 'calibrate'" in r.stderr and 'B10 (140 s): serialization-bound' in r.stderr
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['bundle_splits'] == 1 and st['bundle_split_nodes'] == {'B10': ['d_B10', 'e_B10']}


def test_a_classic_carve_whose_only_slow_bundle_is_one_declaration_stops_without_replanning(env, monkeypatch):
    _calibration_setup(env, monkeypatch, None)
    plan = _plan({'B0': 55, 'B1': 55})
    plan['bundles'][1]['nodes'] = ['OAI.P.ratAdd_comp']
    (env.dir / 'carve_work' / 'plan.json').write_text(json.dumps(plan))
    hook = env.repo / 'prove2me' / 'scripts' / 'carve_measure.py'
    hook.write_text(CALIBRATING_MEASURE.replace('import json, os, sys\n', 'import json, os, sys\n' + PROFILE_HOOK, 1))
    git(env.repo, 'add', '-A')
    git(env.repo, 'commit', '-qm', 'profiling measure stub')
    r = run(env, *ARGS, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}))
    assert r.returncode == 1 and 'B1 (128 s)' in r.stderr and 'serialization-bound' in r.stderr
    assert 'replans' not in json.load(open(env.dir / 'pipeline_state.json'))
    assert tools_called(env).count(('carve', 'plan')) == 1


def test_many_uniformly_slow_bundles_before_publishing_replan_globally_as_before(env, monkeypatch):
    # Batch 3 (2026-10-25): QuarticPowerFree / KirchbergRordam, every bundle 85-128 s against 55 s
    bundles = {'B%d' % i: (55, 100 + i) for i in range(6)}
    _overlap_carve(env, monkeypatch, bundles=bundles, seq=[{}, {'bundle:B%d' % i: _t(40) for i in range(6)}])
    r = run(env, *ARGS_NEW, '--config-set', json.dumps({'time_scale': 1.2, 'budget': 55}), '--stop-after', 'calibrate')
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert seq.count(('carve', 'plan')) == 2 and ('carve', 'split') not in seq
    assert json.load(open(env.dir / 'config.json'))['time_scale'] == round(1.2 * 105 / 55, 1)
    assert json.load(open(env.dir / 'pipeline_state.json'))['replans'] == 1


def test_once_published_even_a_systematic_bundle_overrun_is_split_locally(env, monkeypatch):
    bundles = {'B%d' % i: (55, 100 + i) for i in range(6)}
    _overlap_carve(env, monkeypatch, bundles=bundles)
    # an extension of a published carve: its frozen bundles are someone's already
    r = run(env, *ARGS_NEW, '--config-set', json.dumps({'frozen': {'bundles': ['OLD0'], 'plan': 'x.json'}}),
            '--stop-after', 'calibrate')
    split = [c['argv'] for c in calls(env) if c.get('tool') == 'carve' and c['argv'][0] == 'split']
    assert split and split[0][split[0].index('--only') + 1] == 'B0,B1,B2,B3,B4,B5'
    assert tools_called(env).count(('carve', 'plan')) == 1


def test_a_change_to_a_published_statement_stops_at_gen(env, monkeypatch):
    # a carve patch meant for a piece that also rewrites a published stub: caught before measuring
    (env.dir / 'out' / 'lib').mkdir(parents=True)
    (env.dir / 'out' / 'lib' / 'Thm_P0.lean').write_text('theorem P0 : True := by sorry\n')
    _overlap_carve(env, monkeypatch, pieces={'P0': (10, 192), 'P1': (40, 30)})
    monkeypatch.setenv('STUB_HOOK_carve_gen', textwrap.dedent('''
        if open(os.environ['STUB_LOG']).read().count('"gen"') > 1:
            open(os.path.join(os.getcwd(), 'out', 'lib', 'Thm_P0.lean'), 'w').write('theorem P0 : False := by sorry\\n')
    '''))
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 1 and "step 'gen'" in r.stderr and 'Thm_P0.lean' in r.stderr and 'frozen' in r.stderr
    assert (env.dir / 'published' / 'lib' / 'Thm_P0.lean').read_text() == 'theorem P0 : True := by sorry\n'


def test_publish_waits_for_the_background_publisher(env, tmp_path):
    sys.path.insert(0, ROOT)
    from p2mlib import carvepipeline as C
    p = C.Pipeline(str(env.dir), {'overlap': True}, str(env.repo), ws=str(env.ws))
    states = iter([True, True, True, False, False])
    p.publisher_running = lambda: next(states)
    slept = []
    C.time.sleep, real = (lambda s: slept.append(s)), C.time.sleep
    try:
        p.join_publisher('the final publish', poll=7)
    finally:
        C.time.sleep = real
    assert slept == [7, 7]


def test_keep_port_takes_new_tools_without_re_porting_a_planned_carve(env):
    # oaiq-081 (2026-10-29): 1,586 items planned and mostly measured on an old snapshot; the skill's port
    # rules changed since, so `--upgrade` re-ran filter_patches, whose output changed, and that would have
    # re-ported, rebuilt and re-planned the whole carve. --keep-port keeps the port, on this and every
    # later resume (test_keep_port_survives_later_upgrades_until_an_explicit_redo_port)
    (env.tmp / 'patches.json').write_text('[]')
    assert run(env, *ARGS, '--patches', str(env.tmp / 'patches.json'), '--stop-after', 'measure').returncode == 0
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# a new rewrite\n')
    env.log.write_text('')
    r = run(env, '--upgrade', '--keep-port', '--stop-after', 'measure')
    assert r.returncode == 0, r.stdout + r.stderr
    assert not _ported(env) and ('carve_prep', 'filter-patches') not in tools_called(env)
    assert '--keep-port' in r.stdout and 'keep the port' in r.stdout
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert 'port rules' in st['steps']['port']['in'] and 'filter rules' in st['steps']['filter_patches']['in']
    r = run(env, '--stop-after', 'measure')                                # later resumes: still kept
    assert r.returncode == 0 and not _ported(env) and 'stale' not in r.stdout


def test_a_classic_carve_switched_to_overlap_keeps_its_plan_and_measurements(env, monkeypatch):
    # the same carve: every item measured on the classic route, then "overlap": true in pipeline.json
    _overlap_carve(env, monkeypatch)
    assert run(env, *ARGS, '--stop-after', 'measure').returncode == 0
    p = json.load(open(env.dir / 'pipeline.json'))
    p['overlap'] = True
    (env.dir / 'pipeline.json').write_text(json.dumps(p))
    env.log.write_text('')
    r = run(env, '--upgrade', '--keep-port')
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert ('carve', 'plan') not in seq and ('carve', 'gen') not in seq
    measures = [c['argv'] for c in calls(env) if c.get('tool') == 'carve_measure']
    assert measures == [['config.json', '--keep-going', '--kinds', 'piece']]   # the classic measure stands
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert st['steps']['calibrate_pieces']['status'] == 'done' and st.get('replans', 0) == 0


# ---------------------------------------------------------------- 2026-10-29: a rehearsal copy of oaiq-081
# (`cp -a` of the carve dir, its config still on the shared workspace) re-ported and rewrote 228 files of the
# live carve's Solutions/OAIQ081_SAT. The port folder now has an owner, publishing-started is a state fact,
# and --keep-port holds until an explicit --redo port.

def run_in(d, *extra):
    live = os.environ['P2M_SKILL_REPO'] + '/prove2me/scripts/carve_pipeline.py'
    return subprocess.run([sys.executable, live, str(d), *extra], capture_output=True, text=True)


def _folder(env):
    f = env.ws / 'Solutions' / 'F'
    return {p.name: p.read_bytes() for p in sorted(f.iterdir())}


OWNER = '.carve_owner.json'


def test_a_copied_carve_refuses_the_port_folder_of_its_original_and_writes_nothing(env):
    assert run(env, *ARGS).returncode == 0
    marker = json.load(open(env.ws / 'Solutions' / 'F' / OWNER))
    assert marker['carve'] == os.path.realpath(env.dir)
    copy = env.tmp / 'copy'
    shutil.copytree(env.dir, copy, symlinks=True)
    before = _folder(env)
    env.log.write_text('')
    for extra in (['--upgrade', '--redo', 'port'], ['--from', 'port'], []):
        r = run_in(copy, *extra)
        assert r.returncode != 0, r.stdout + r.stderr
        assert 'Solutions/F belongs to carve %s' % os.path.realpath(env.dir) in r.stderr and 'P2M_WORKSPACE' in r.stderr
        assert tools_called(env) == [] and _folder(env) == before
    # the owner goes on
    r = run(env, '--redo', 'port')
    assert r.returncode == 0 and _ported(env), r.stdout + r.stderr


def test_a_legacy_folder_is_adopted_by_the_carve_whose_port_it_holds(env):
    # running carves have no owner file: the carve whose recorded port hash is the folder's adopts it,
    # a copy (its port log names the original carve) does not
    assert run(env, *ARGS).returncode == 0
    (env.ws / 'Solutions' / 'F' / OWNER).unlink()
    copy = env.tmp / 'copy'
    shutil.copytree(env.dir, copy, symlinks=True)
    env.log.write_text('')
    r = run_in(copy, '--redo', 'port')
    assert r.returncode != 0 and tools_called(env) == [], r.stdout + r.stderr
    assert not (env.ws / 'Solutions' / 'F' / OWNER).exists()
    r = run(env, '--redo', 'port')
    assert r.returncode == 0 and _ported(env), r.stdout + r.stderr
    assert json.load(open(env.ws / 'Solutions' / 'F' / OWNER))['carve'] == os.path.realpath(env.dir)


def test_a_legacy_folder_that_changed_since_the_port_needs_claim_folder(env):
    assert run(env, *ARGS).returncode == 0
    (env.ws / 'Solutions' / 'F' / OWNER).unlink()
    (env.ws / 'Solutions' / 'F' / 'Pre_Main.lean').write_text('-- rewritten by someone\n')
    env.log.write_text('')
    r = run(env)
    assert r.returncode != 0 and '--claim-folder' in r.stderr and tools_called(env) == [], r.stdout + r.stderr
    r = run(env, '--claim-folder')
    assert r.returncode == 0, r.stdout + r.stderr
    assert json.load(open(env.ws / 'Solutions' / 'F' / OWNER))['carve'] == os.path.realpath(env.dir)


def test_a_moved_carve_keeps_its_folder(env):
    assert run(env, *ARGS).returncode == 0
    moved = env.tmp / 'moved'
    shutil.move(str(env.dir), str(moved))
    r = run_in(moved, '--redo', 'port')
    assert r.returncode == 0, r.stdout + r.stderr
    assert json.load(open(env.ws / 'Solutions' / 'F' / OWNER))['carve'] == os.path.realpath(moved)


def test_config_paths_into_another_carve_are_refused(env):
    # a copy's config.json still names the original's out/ and work/, which gen and measure write
    assert run(env, *ARGS).returncode == 0
    other = env.tmp / 'other'
    other.mkdir()
    (other / 'pipeline.json').write_text('{}')
    cfg = json.load(open(env.dir / 'config.json'))
    cfg['out'] = str(other / 'out')
    json.dump(cfg, open(env.dir / 'config.json', 'w'))
    env.log.write_text('')
    r = run(env, '--redo', 'gen')
    assert r.returncode != 0 and 'out' in r.stderr and str(other) in r.stderr and tools_called(env) == []


def test_a_frozen_replan_without_a_run_state_still_counts_as_publishing(env, monkeypatch):
    # a frozen re-plan drops publish_early from the step records; with no publish/run_state.json yet
    # (no publisher had written one), a port-rule change was taken as safe to re-port
    _overlap_carve(env, monkeypatch, pieces={'P0': (10, 192), 'P1': (40, 30)}, seq=[{}, {}, {}, {'piece:P0': _t(40)}])
    monkeypatch.setenv('STUB_HOOK_carve_gen', textwrap.dedent('''
        if open(os.environ['STUB_LOG']).read().count('"gen"') > 1:
            sys.exit(1)
    '''))
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 1 and "step 'gen'" in r.stderr, r.stdout + r.stderr
    st = json.load(open(env.dir / 'pipeline_state.json'))
    assert 'publish_early' not in st['steps'] and st['publishing_started']
    assert not (env.dir / 'publish' / 'run_state.json').exists()
    monkeypatch.delenv('STUB_HOOK_carve_gen')
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# a new rewrite\n')
    env.log.write_text('')
    monkeypatch.setenv('STUB_TIMES_SEQ', json.dumps([{}, {'piece:P0': _t(40)}]))   # the split piece fits
    r = run(env, '--upgrade')
    assert r.returncode == 0, r.stdout + r.stderr
    assert not _ported(env) and 'publishing has started' in r.stdout
    prep = [c['argv'] for c in calls(env) if c.get('tool') == 'carve_prep' and c['argv'][0] == 'publish-prep']
    assert prep and all(a[-1] == '--sync' for a in prep)           # publish/ is synced, never rebuilt


def test_after_publishing_a_changed_patches_file_waits_for_an_explicit_redo(env):
    extra = _patches_setup(env)
    assert run(env, *ARGS, *extra, '--publish').returncode == 0
    (env.tmp / 'patches.json').write_text('[{"old": "a", "new": "b"}]')
    env.log.write_text('')
    r = run(env)
    assert r.returncode != 0 and '--redo filter_patches' in r.stderr and tools_called(env) == [], r.stdout + r.stderr
    (env.dir / 'port_patches.json').write_text('[{"old": "a", "new": "b"}]')    # what the redo writes
    r = run(env, '--redo', 'filter_patches', '--stop-after', 'config')
    assert r.returncode == 0 and _ported(env), r.stdout + r.stderr


def test_keep_port_survives_later_upgrades_until_an_explicit_redo_port(env):
    (env.tmp / 'patches.json').write_text('[]')
    assert run(env, *ARGS, '--patches', str(env.tmp / 'patches.json'), '--stop-after', 'measure').returncode == 0
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# a new rewrite\n')
    assert run(env, '--upgrade', '--keep-port', '--stop-after', 'measure').returncode == 0
    assert json.load(open(env.dir / 'pipeline_state.json'))['keep_port']
    # the next skill commits change carve_prep.py and the port rules again
    _commit(env, 'scripts/carve_prep.py', (env.repo / 'prove2me' / 'scripts' / 'carve_prep.py').read_text() + '\n# fix\n')
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# another rewrite\n')
    env.log.write_text('')
    r = run(env, '--upgrade', '--stop-after', 'measure')
    assert r.returncode == 0, r.stdout + r.stderr
    assert not _ported(env) and ('carve_prep', 'filter-patches') not in tools_called(env)
    assert 'stale' not in r.stdout and 'keep-port' in r.stdout
    # --redo port ends it: the port is redone now, and a later rule change re-ports by itself again
    r = run(env, '--redo', 'port', '--stop-after', 'measure')
    assert r.returncode == 0 and _ported(env), r.stdout + r.stderr
    assert 'keep_port' not in json.load(open(env.dir / 'pipeline_state.json'))
    _commit(env, 'p2mlib/oaiport.py', open(os.path.join(ROOT, 'p2mlib', 'oaiport.py')).read() + '\n# a third\n')
    env.log.write_text('')
    r = run(env, '--upgrade', '--stop-after', 'measure')
    assert r.returncode == 0 and _ported(env), r.stdout + r.stderr


def test_filter_patches_is_stale_only_when_its_own_code_changes(env):
    # filter_patches' rule inputs were all of carve_prep.py, which changes almost daily for other reasons
    stub = env.repo / 'prove2me' / 'scripts' / 'carve_prep.py'
    _commit(env, 'scripts/carve_prep.py', stub.read_text() + '\ndef filter_patches(p, t):\n    return p\n')
    extra = _patches_setup(env)
    assert run(env, *ARGS, *extra, '--stop-after', 'measure').returncode == 0
    _commit(env, 'scripts/carve_prep.py', stub.read_text() + '\ndef publish_prep():\n    pass\n')
    env.log.write_text('')
    r = run(env, '--upgrade', '--stop-after', 'measure')
    assert r.returncode == 0 and ('carve_prep', 'filter-patches') not in tools_called(env), r.stdout + r.stderr
    _commit(env, 'scripts/carve_prep.py', stub.read_text().replace('return p', 'return p[:1]'))
    env.log.write_text('')
    r = run(env, '--upgrade', '--stop-after', 'measure')
    assert r.returncode == 0 and ('carve_prep', 'filter-patches') in tools_called(env), r.stdout + r.stderr


def test_publish_early_refuses_a_publish_dir_without_run_early(env, monkeypatch):
    # a classic publish_prep from a snapshot before overlap mode wrote no run_early.json: the background
    # publisher would die at once and the pieces' gate would never open early
    _overlap_carve(env, monkeypatch)
    monkeypatch.setenv('STUB_HOOK_carve_prep_publish_prep', "os.remove(os.path.join(sys.argv[2], 'publish', 'run_early.json'))")
    r = run(env, *ARGS_NEW, '--publish')
    assert r.returncode == 1 and 'run_early.json' in r.stderr and '--redo publish_prep' in r.stderr, r.stdout + r.stderr
    assert not any(l.startswith('systemd-run') for l in _raw(env))
    assert 'auto_config' not in json.load(open(env.dir / 'pipeline_state.json'))


def test_a_legacy_folder_ported_but_not_yet_built_is_adopted_by_its_porter_only(env):
    assert run(env, *ARGS, '--stop-after', 'port').returncode == 0
    (env.ws / 'Solutions' / 'F' / OWNER).unlink()
    copy = env.tmp / 'copy'
    shutil.copytree(env.dir, copy, symlinks=True)
    assert run_in(copy).returncode != 0 and not (env.ws / 'Solutions' / 'F' / OWNER).exists()
    r = run(env, '--stop-after', 'build')
    assert r.returncode == 0, r.stdout + r.stderr
    assert json.load(open(env.ws / 'Solutions' / 'F' / OWNER))['carve'] == os.path.realpath(env.dir)


def test_a_config_on_another_workspace_is_refused(env):
    # a copy run with its own P2M_WORKSPACE whose config.json still reads (and measures in) the old one
    assert run(env, *ARGS).returncode == 0
    cfg = json.load(open(env.dir / 'config.json'))
    cfg['src'] = str(env.tmp / 'other_ws')
    json.dump(cfg, open(env.dir / 'config.json', 'w'))
    env.log.write_text('')
    r = run(env, '--redo', 'gen')
    assert r.returncode != 0 and 'src' in r.stderr and 'other_ws' in r.stderr and tools_called(env) == []
    cfg['src'] = str(env.ws)
    json.dump(cfg, open(env.dir / 'config.json', 'w'))
    assert run(env, '--redo', 'gen').returncode == 0


# ---- a re-run graph whose output changed re-plans (oaiq-123) -------------------------------------------

GRAPH_HOOK = ("w = json.load(open('config.json'))['work']; os.makedirs(w, exist_ok=True); "
              "open(os.path.join(w, 'decl_graph.jsonl'), 'w').write(os.environ.get('GRAPH_TEXT', 'g1'))")


def _graph_carve(env, monkeypatch):
    monkeypatch.setenv('STUB_HOOK_carve_graph', GRAPH_HOOK)
    _commit(env, 'lean/LeanInfo.lean', '-- v1\n')
    r = run(env, *ARGS, '--config-set', json.dumps({'work': str(env.tmp / 'work')}), '--stop-after', 'plan')
    assert r.returncode == 0, r.stdout + r.stderr
    _commit(env, 'lean/LeanInfo.lean', '-- v2\n')
    env.log.write_text('')


def test_a_rerun_graph_with_new_output_reruns_extdefs_and_plan(env, monkeypatch):
    # oaiq-123: an --upgrade across a LeanInfo change re-ran `graph` (gen still to run), whose new edges
    # (830d195: a default-simp call depends on its module's earlier rfl simp lemmas) ran backwards across
    # the old plan's bundles; `plan` stayed done, and calibrate's bundle split died on an import cycle
    _graph_carve(env, monkeypatch)
    monkeypatch.setenv('GRAPH_TEXT', 'g2')
    r = run(env, '--upgrade', '--stop-after', 'plan')
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert seq.index(('carve', 'graph')) < seq.index(('carve_prep', 'ext-defs')) < seq.index(('carve', 'plan')), seq


def test_a_rerun_graph_with_the_same_output_keeps_the_plan(env, monkeypatch):
    _graph_carve(env, monkeypatch)
    r = run(env, '--upgrade', '--stop-after', 'plan')
    assert r.returncode == 0, r.stdout + r.stderr
    assert tools_called(env) == [('carve', 'graph')], tools_called(env)


def test_a_plan_from_before_the_graph_hash_is_stale_when_graph_ran_after_it(env, monkeypatch):
    # oaiq-019's state: plan recorded no graph hash; graph re-ran (finished later than plan)
    _graph_carve(env, monkeypatch)
    st = json.load(open(env.dir / 'pipeline_state.json'))
    for s in ('extdefs', 'plan'):
        st['steps'][s].pop('in', None)
        st['steps'][s]['finished'] = '2026-10-26T19:03:20'
    st['steps']['graph']['finished'] = '2026-10-30T05:38:32'
    json.dump(st, open(env.dir / 'pipeline_state.json', 'w'))
    r = run(env, '--stop-after', 'plan')
    assert r.returncode == 0, r.stdout + r.stderr
    assert ('carve', 'plan') in tools_called(env), tools_called(env)


def with_monitor(env):
    """The synthetic skills repo with the monitor skill's section.py beside prove2me, as in the real one."""
    src = os.path.join(os.path.dirname(ROOT), 'monitor', 'section.py')
    if not os.path.isfile(src):
        pytest.skip('monitor skill not beside prove2me')
    (env.repo / 'monitor').mkdir()
    shutil.copy(src, env.repo / 'monitor' / 'section.py')
    git(env.repo, 'add', '-A')
    git(env.repo, 'commit', '-qm', 'monitor')


def carve_section(env):
    from p2mlib import carvemonitor
    f = os.path.join(os.environ['MONITOR_HOME'], 'sections', carvemonitor.section_id(str(env.dir)) + '.json')
    return json.load(open(f)) if os.path.exists(f) else None


def test_the_driver_keeps_a_monitor_section_and_marks_it_done(env):
    with_monitor(env)
    r = run(env, *ARGS)
    assert r.returncode == 0, r.stdout + r.stderr
    sec = carve_section(env)
    assert sec['state'] == 'done' and sec['alerts'] == []
    assert sec['note'] == 'all steps done; nothing published (run again with --publish)'
    assert sec['title'].endswith(': OAI.Pre.Main')
    steps = sec['phases'][0]
    assert steps['name'] == 'Steps' and steps['done'] == steps['total'] == 19 and steps['state'] == 'done'
    assert {p['label'] for p in sec['processes']} == {'driver', 'publisher', 'lean'}
    r = run(env, '--stop-after', 'dryrun')
    assert carve_section(env)['note'] == 'stopped after dryrun (--stop-after)'


def test_a_failed_step_marks_the_section_failed_with_the_reason(env, monkeypatch):
    with_monitor(env)
    monkeypatch.setenv('STUB_FAIL', 'carve plan')
    r = run(env, *ARGS)
    assert r.returncode == 1
    sec = carve_section(env)
    assert sec['state'] == 'failed' and sec['note'].startswith('stopped at plan: (exit 1): boom from carve')
    assert sec['alerts'] == [sec['note']]
    assert sec['phases'][0]['state'] == 'failed'


def test_without_the_monitor_skill_the_driver_runs_as_before(env):
    r = run(env, *ARGS)                    # the synthetic repo has no monitor/ directory
    assert r.returncode == 0, r.stdout + r.stderr
    assert carve_section(env) is None
