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
    (d / 'oai_meta.json').write_text('{"title": "T", "date": "d", "family": "1", "prefixes": ["OAI.Pre"]}')
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
    assert seq[first[1]:first[1] + 5] == [('carve', 'plan'), ('carve', 'gen'), ('carve', 'order'),
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
    for meta in ('{"title": "T", "date": "d", "family": "1"}',
                 '{"title": "T", "date": "d", "family": "1", "prefixes": ["OAI.Other"]}'):
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


def test_state_from_before_hashes_existed_is_not_called_stale(env):
    assert run(env, *ARGS).returncode == 0
    st = json.load(open(env.dir / 'pipeline_state.json'))
    for rec in st['steps'].values():
        rec.pop('in', None)
    json.dump(st, open(env.dir / 'pipeline_state.json', 'w'))
    (env.dir / 'port_patches.json').write_text('[1]')
    env.log.write_text('')
    assert run(env).returncode == 0 and tools_called(env) == []


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
    r = CP.calibration(_plan({'B0': 55}, {'P': 46}), {'bundle:B0': _t(20), 'piece:P': _t(250)}, 8, 55)
    assert [x[0] for x in r['over']] == ['piece:P']
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
