"""carve_pipeline.py --native: carving a development of our own that already sits built in the workspace
(not an openai/math port). Artin KP (2026-11-16, p2m-standalone artin/proofs/kp/PACKAGING.md): the scoping
trial had to call the carve primitives by hand with a hand-written config, because the driver's first steps,
its config step and its prose all assumed an OpenAI port. Sub-tools are the stubs of test_carve_pipeline;
nothing here runs Lean or touches prove2.me."""
import json
import os
import sys
import time

import pytest

from conftest import SCRIPTS, fake_olean
from test_carve_pipeline import ROOT, calls, env, git, run, tools_called  # noqa: F401  (env is a fixture)

sys.path.insert(0, ROOT)
from p2mlib import carvepipeline as CP  # noqa: E402
from p2mlib import nativecarve as N  # noqa: E402

META = {'title': 'A cubic theta leaf', 'credit': 'A. Author and B. Author',
        'repo': 'https://github.com/example/dev', 'commit': 'c' * 40,
        'paths': {'Solutions.Nat.KP': 'proofs/kp/lean', 'Solutions.Nat.C0': 'proofs/c0/lean'},
        'paper': 'P. Aper, On theta, J. Math. 1 (1984), 1-2'}

SOURCES = {
    'Solutions/Nat/KP/A.lean': 'import Mathlib\nimport Definitions.Def_D1\n\nnamespace Loc\ndef a := 1\nend Loc\n',
    'Solutions/Nat/C0/B.lean': 'import Mathlib\nimport Theorems.Thm_Ext_lemma\n\nnamespace Loc\ndef b := 2\nend Loc\n',
    'Solutions/Nat/KP/Main.lean': ('import Mathlib\nimport Solutions.Nat.KP.A\nimport Solutions.Nat.C0.B\n'
                                   'import Theorems.Thm_Pub_target\n\nnamespace Loc\n'
                                   'theorem goal : type_of% (Pub.target) := sorry\nend Loc\n'),
    'Solutions/Nat/Other.lean': 'import Mathlib\nimport Theorems.Thm_Far_away\n',
    'Theorems/Thm_Ext_lemma.lean': 'import Mathlib\nimport Definitions.Def_D2\n\nnamespace Ext\n\ntheorem lemma : True := by\n  sorry\n\nend Ext\n',
    'Theorems/Thm_Pub_target.lean': 'import Mathlib\nimport Definitions.Def_D1\n\nnamespace Pub\n\ntheorem target : True := by\n  sorry\n\nend Pub\n',
    'Theorems/Thm_Far_away.lean': 'import Mathlib\n\ntheorem Far.away : True := by\n  sorry\n',
    'Definitions/Def_D1.lean': 'import Mathlib\n\ndef D1 := 1\n',
    'Definitions/Def_D2.lean': 'import Mathlib\nimport Definitions.Def_D3\n\ndef D2 := 1\n',
    'Definitions/Def_D3.lean': 'import Mathlib\n\ndef D3 := 1\n',
}
CLOSURE = ['Solutions.Nat.KP.A', 'Solutions.Nat.C0.B', 'Solutions.Nat.KP.Main']


def olean_of(ws, module):
    return os.path.join(str(ws), '.lake', 'build', 'lib', 'lean', *module.split('.')) + '.olean'


def native_ws(ws):
    for rel, text in SOURCES.items():
        p = os.path.join(str(ws), rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'w', encoding='utf-8') as f:
            f.write(text)
    for m in CLOSURE:
        fake_olean(olean_of(ws, m))
    return ws


@pytest.fixture
def nat(env):
    native_ws(env.ws)
    env.dir.mkdir(exist_ok=True)
    (env.dir / 'native_meta.json').write_text(json.dumps(META))
    return env


NARGS = ['--native', '--folder', 'Nat', '--root-module', 'Solutions.Nat.KP.Main', '--target', 'Loc.goal',
         '--proves', 'Loc.goal=Pub.target@8b3180bd', '--bundle-prefix', 'NB', '--no-overlap']
OAI_ONLY = {'fetch_theorems', 'oai_fetch', 'oai_port_modules', 'oai_build_modules'}


# ---------------------------------------------------------------- the pure parts (p2mlib.nativecarve)

def test_closure_follows_project_imports_only(tmp_path):
    ws = native_ws(tmp_path)
    mods, ext = N.closure(str(ws), 'Solutions.Nat', ['Solutions.Nat.KP.Main'])
    assert mods == CLOSURE                                 # imports first; Other is outside
    assert ext == ['Definitions.Def_D1', 'Mathlib', 'Theorems.Thm_Ext_lemma', 'Theorems.Thm_Pub_target']
    with pytest.raises(N.NativeError, match='no source'):
        N.closure(str(ws), 'Solutions.Nat', ['Solutions.Nat.KP.Nope'])
    with pytest.raises(N.NativeError, match='not under'):
        N.closure(str(ws), 'Solutions.Nat', ['Solutions.Else.X'])


def test_external_theorems_are_the_stubs_the_closure_imports(tmp_path):
    ws = native_ws(tmp_path)
    _, ext = N.closure(str(ws), 'Solutions.Nat', ['Solutions.Nat.KP.Main'])
    assert N.external_theorems(str(ws), ext) == {'Ext.lemma': 'Theorems.Thm_Ext_lemma',
                                                 'Pub.target': 'Theorems.Thm_Pub_target'}
    # every Definitions/Theorems module the closure reaches, through stubs and bundles too: the carve's
    # private olean dir shadows the workspace's, so measure needs them all (the trial: 102 modules)
    assert N.published_modules(str(ws), ext) == [
        'Definitions.Def_D1', 'Definitions.Def_D2', 'Definitions.Def_D3',
        'Theorems.Thm_Ext_lemma', 'Theorems.Thm_Pub_target']


def test_a_tree_that_is_not_built_is_refused(tmp_path):
    ws = native_ws(tmp_path)
    assert N.stale_oleans(str(ws), CLOSURE) == []
    os.remove(olean_of(ws, 'Solutions.Nat.C0.B'))
    src = os.path.join(str(ws), 'Solutions', 'Nat', 'KP', 'A.lean')
    os.utime(src, (time.time() + 100, time.time() + 100))          # edited after it was built
    assert N.stale_oleans(str(ws), CLOSURE) == [('Solutions.Nat.KP.A', 'older than its source'),
                                                ('Solutions.Nat.C0.B', 'not built')]


def test_parse_proves():
    assert N.parse_proves(['A.goal=Pub.t@8b3180bd', 'A.other=Pub.u']) == (
        {'A.goal': 'Pub.t', 'A.other': 'Pub.u'}, {'Pub.t': '8b3180bd'})
    assert N.parse_proves(None) == ({}, {})
    for bad in ('A.goal', 'A.goal=', '=Pub.t', 'A.goal=A.goal'):
        with pytest.raises(N.NativeError):
            N.parse_proves([bad])


def test_native_meta_is_checked(tmp_path):
    p = tmp_path / 'native_meta.json'
    assert 'write' in N.meta_problem(str(p)) and '"credit"' in N.meta_problem(str(p))
    p.write_text(json.dumps(META))
    assert N.meta_problem(str(p)) is None
    for k in ('title', 'credit', 'repo', 'commit', 'paths'):
        p.write_text(json.dumps({x: v for x, v in META.items() if x != k}))
        assert k in N.meta_problem(str(p))
    p.write_text(json.dumps(dict(META, commit='abc123')))
    assert '40-hex' in N.meta_problem(str(p))
    p.write_text(json.dumps(dict(META, prefixes=['OAI.X'], family='1', date='d')))
    assert 'oai_meta.json' in N.meta_problem(str(p))       # an OpenAI meta file under the native name


def test_private_source_has_no_links(tmp_path):
    """`"repo": null`: the development's repository is private, so nothing published links to it."""
    priv = dict(META, repo=None, paths={})
    p = tmp_path / 'native_meta.json'
    p.write_text(json.dumps(priv))
    assert N.meta_problem(str(p)) is None
    p.write_text(json.dumps({x: v for x, v in priv.items() if x != 'repo'}))
    assert 'repo' in N.meta_problem(str(p))              # the key must still be there, deliberately null
    assert N.module_link(priv, 'Solutions.Nat.KP.Sub.Main', 3) is None
    assert N.module_link(dict(META, repo=None), 'Solutions.Nat.KP.Sub.Main', 3) is None   # even with paths
    s = N.source_line(priv)
    assert priv['credit'] in s and priv['title'] in s and 'http' not in s and 'commit' not in s
    assert N.is_native_meta(priv)


def test_port_links_the_repo_without_lines(tmp_path):
    """`ported_from`: the workspace tree was edited from the commit (GRHLean, 2026-11-26), so line links would
    be wrong; the repo is linked at the commit, no declaration is, and the texts say it is a port."""
    port = dict(META, paths={}, ported_from='renamed under the namespace GRHLean')
    p = tmp_path / 'native_meta.json'
    p.write_text(json.dumps(port))
    assert N.meta_problem(str(p)) is None
    p.write_text(json.dumps(dict(port, ported_from='')))
    assert 'ported_from' in N.meta_problem(str(p))
    assert N.module_link(port, 'Solutions.Nat.KP.Sub.Main', 3) is None
    assert 'ported: renamed under the namespace GRHLean' in N.source_line(port)
    r = N.repo_ref(port)
    assert port['commit'] in r and 'port of it: renamed' in r


def test_module_paths_and_source_line():
    assert N.module_path(META, 'Solutions.Nat.KP.Sub.Main') == 'proofs/kp/lean/Sub/Main.lean'
    assert N.module_path(META, 'Solutions.Nat.C0.B') == 'proofs/c0/lean/B.lean'
    assert N.module_path(META, 'Solutions.Nat.T12.X') is None
    assert N.module_link(META, 'Solutions.Nat.C0.B', 7) == \
        'https://github.com/example/dev/blob/%s/proofs/c0/lean/B.lean#L7' % ('c' * 40)
    line = N.source_line(META)
    assert line == ('A. Author and B. Author, A cubic theta leaf, https://github.com/example/dev (commit ccccccc); '
                    'after P. Aper, On theta, J. Math. 1 (1984), 1-2')
    assert 'OpenAI' not in line and 'openai' not in line


def test_make_config_writes_what_the_trial_wrote_by_hand(tmp_path):
    ws = native_ws(tmp_path)
    d = tmp_path / 'carve'
    d.mkdir()
    cfg = N.make_config(str(d), str(ws), 'Nat', ['Solutions.Nat.KP.Main'], ['Loc.goal', 'Loc.other'],
                        proves={'Loc.goal': 'Pub.target'}, proves_ids={'Pub.target': '8b3180bd'},
                        bundle_prefix='NB', forced=['Loc.f'], budget=55,
                        old={'patches': 'p.json', 'time_scale': 3.0, 'no_promote': ['x']})
    assert cfg['src'] == str(ws) and cfg['roots'] == ['Solutions.Nat.KP.Main']
    assert cfg['prefix'] == 'Solutions.Nat'                      # a dotted prefix, not a name prefix
    assert cfg['targets'] == ['Loc.goal', 'Loc.other'] and cfg['forced'] == ['Loc.f']
    assert cfg['external'] == ['Loc.goal']                       # only what is published already
    assert cfg['proves'] == {'Loc.goal': 'Pub.target'} and cfg['proves_ids'] == {'Pub.target': '8b3180bd'}
    assert cfg['external_defs'] == {}
    assert cfg['external_theorems'] == {'Ext.lemma': 'Theorems.Thm_Ext_lemma', 'Pub.target': 'Theorems.Thm_Pub_target'}
    assert cfg['extra_olean_modules'] == ['Definitions.Def_D1', 'Definitions.Def_D2', 'Definitions.Def_D3',
                                          'Theorems.Thm_Ext_lemma', 'Theorems.Thm_Pub_target']
    assert cfg['work'] == str(d) + '/work' and cfg['out'] == str(d) + '/out'
    assert cfg['build_logs'] == [str(d) + '/build_adj.log'] and cfg['jobs'] == 1
    assert cfg['collapse_mathlib'] is True and cfg['carry_stub_definitions'] is True and cfg['native'] is True
    assert cfg['bundle_prefix'] == 'NB' and cfg['budget'] == 55 and cfg['bundle_budget'] == 55
    assert cfg['chunker'] == 'schedule' and cfg['time_scale'] == 1.2 and cfg['bundle_size'] == 450000
    assert cfg['patches'] == 'p.json' and 'no_promote' not in cfg     # kept hand-set key; derived ones are not
    with pytest.raises(N.NativeError, match='published statement Pub.nope'):
        N.make_config(str(d), str(ws), 'Nat', ['Solutions.Nat.KP.Main'], ['Loc.goal'], proves={'Loc.goal': 'Pub.nope'})
    with pytest.raises(N.NativeError, match='not a target'):
        N.make_config(str(d), str(ws), 'Nat', ['Solutions.Nat.KP.Main'], ['Loc.other'], proves={'Loc.goal': 'Pub.target'})
    os.remove(olean_of(ws, 'Solutions.Nat.C0.B'))
    with pytest.raises(N.NativeError, match=r'lake build Solutions\.Nat\.KP\.Main'):
        N.make_config(str(d), str(ws), 'Nat', ['Solutions.Nat.KP.Main'], ['Loc.goal'])


def test_build_lines_come_from_the_per_module_measurement():
    secs = {'M.A': 10.0, 'M.B': 3.2, 'M.C': None}
    text, missing = N.build_lines(['M.A', 'M.B', 'M.C'], secs.get)
    assert text == '✔ [1/1] Built M.A (7.0s)\n✔ [1/1] Built M.B (0.2s)\n'      # less the 3 s import; floor 0.1
    assert missing == ['M.C']
    sys.path.insert(0, SCRIPTS)
    from p2mlib import carve as C
    assert C.parse_build_log(text) == {'M.A': 7.0, 'M.B': 0.2}


def test_no_promote_for_what_rests_on_the_published_target():
    class G:
        owner = {}
        nodes = {}
    from p2mlib import carve as C
    g = G()
    mk = lambda deps, thm=True: type('Nd', (), {'deps': set(deps), 'theorem': thm})()
    g.nodes = {'Pub.target': mk([]), 'Loc.pre': mk(['Pub.target']), 'Loc.mid': mk(['Loc.pre']),
               'Loc.goal': mk(['Loc.mid']), 'Loc.free': mk([]), 'Loc.d': mk(['Loc.pre'], thm=False)}
    assert N.target_no_promote(g, {'Loc.goal': 'Pub.target'}, C.target_users) == ['Loc.mid', 'Loc.pre']
    assert N.target_no_promote(g, {}, C.target_users) == []


# ---------------------------------------------------------------- the driver

def test_native_run_skips_the_port_and_runs_the_later_steps(nat):
    r = run(nat, *NARGS)
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(nat)
    assert not OAI_ONLY & {t for t, _ in seq}
    assert ('carve_prep', 'config') not in seq and ('carve_prep', 'ext-defs') not in seq
    assert not any(l.startswith('lake') for l in nat.log.read_text().splitlines())      # nothing is built
    want = [('carve', 'graph'), ('carve_prep', 'native-prep'), ('carve', 'plan'), ('carve', 'gen'),
            ('carve_prep', 'name-check'), ('carve', 'order'), ('carve_measure', 'config.json'),
            ('carve_prep', 'publish-prep'), ('carve_prep', 'prose-template'), ('carve_prep', 'check-text'),
            ('split_run', 'publish/run.json')]
    assert seq == want
    st = json.load(open(nat.dir / 'pipeline_state.json'))
    assert not {'fetch', 'inputs', 'filter_patches', 'port', 'build', 'wsbuild'} & set(st['steps'])
    assert st['steps']['config']['status'] == 'done'
    cfg = json.load(open(nat.dir / 'config.json'))
    assert cfg['prefix'] == 'Solutions.Nat' and cfg['roots'] == ['Solutions.Nat.KP.Main']
    assert cfg['targets'] == ['Loc.goal'] and cfg['external'] == ['Loc.goal']
    assert cfg['proves'] == {'Loc.goal': 'Pub.target'} and cfg['proves_ids'] == {'Pub.target': '8b3180bd'}
    assert set(cfg['external_theorems']) == {'Ext.lemma', 'Pub.target'}
    assert 'Definitions.Def_D3' in cfg['extra_olean_modules']
    assert 'written' in (nat.dir / 'logs' / 'config.log').read_text()
    # nothing of the carve is written into the development's folder
    assert not (nat.ws / 'Solutions' / 'Nat' / '.carve_owner.json').exists()
    by = {(c['tool'], c['argv'][0]): c['argv'] for c in calls(nat) if 'tool' in c}
    pp = by[('carve_prep', 'publish-prep')]
    assert pp[2] == N.source_line(META) and 'OpenAI' not in ' '.join(pp) and pp[3] == 'formalization'
    pt = by[('carve_prep', 'prose-template')]
    assert pt[pt.index('--meta') + 1] == str(nat.dir / 'native_meta.json') and '--lean-root' not in pt
    assert not any('--go' in c['argv'] for c in calls(nat) if c.get('tool') == 'split_run')


def test_native_list_and_resume(nat):
    assert run(nat, *NARGS, '--stop-after', 'graph').returncode == 0
    r = run(nat, '--list')
    steps = [l.split()[0] for l in r.stdout.splitlines()]
    assert steps[:3] == ['config', 'graph', 'extdefs'] and 'port' not in steps and 'build' not in steps
    assert steps[-1] == 'publish'
    nat.log.write_text('')
    r = run(nat)                                            # resume: no parameters
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(nat)
    assert seq[0] == ('carve_prep', 'native-prep') and ('carve', 'graph') not in seq
    nat.log.write_text('')
    assert run(nat).returncode == 0 and tools_called(nat) == []          # all done


def test_native_overlap_mode_is_the_default_and_publish_is_opt_in(nat):
    args = [a for a in NARGS if a != '--no-overlap']
    r = run(nat, *args)
    assert r.returncode == 0, r.stdout + r.stderr
    assert json.load(open(nat.dir / 'pipeline.json'))['overlap'] is True
    assert [c['argv'] for c in calls(nat) if c.get('tool') == 'split_run' and '--go' in c['argv']] == []


def test_native_config_fails_without_meta_or_a_built_tree(nat):
    (nat.dir / 'native_meta.json').unlink()
    r = run(nat, *NARGS)
    assert r.returncode == 1 and 'native_meta.json' in r.stderr and '"credit"' in r.stderr
    assert tools_called(nat) == []
    (nat.dir / 'native_meta.json').write_text(json.dumps(META))
    os.remove(olean_of(nat.ws, 'Solutions.Nat.KP.A'))
    r = run(nat)
    assert r.returncode == 1 and 'Solutions.Nat.KP.A' in r.stderr and 'lake build' in r.stderr
    fake_olean(olean_of(nat.ws, 'Solutions.Nat.KP.A'))
    assert run(nat).returncode == 0


def test_native_source_edit_makes_config_stale(nat):
    assert run(nat, *NARGS).returncode == 0
    src = nat.ws / 'Solutions' / 'Nat' / 'KP' / 'A.lean'
    src.write_text(src.read_text() + '\ndef a2 := 2\n')
    fake_olean(olean_of(nat.ws, 'Solutions.Nat.KP.A'))                  # rebuilt after the edit
    os.utime(olean_of(nat.ws, 'Solutions.Nat.KP.A'), (time.time() + 5, time.time() + 5))
    nat.log.write_text('')
    r = run(nat)
    assert r.returncode == 0, r.stdout + r.stderr
    assert '== stale: config' in r.stdout and 'sources' in r.stdout
    assert ('carve', 'graph') in tools_called(nat)
    # a module outside the closure is not the carve's input
    other = nat.ws / 'Solutions' / 'Nat' / 'Other.lean'
    other.write_text(other.read_text() + '\n-- x\n')
    nat.log.write_text('')
    r = run(nat)
    assert r.returncode == 0 and 'stale' not in r.stdout and tools_called(nat) == []


def test_native_options_reach_the_config(nat):
    forced = nat.tmp / 'forced.json'
    forced.write_text(json.dumps(['Loc.f1', 'Loc.f2']))
    r = run(nat, *NARGS, '--forced', str(forced), '--forced', 'Loc.f3', '--budget', '40', '--tags', 'artin,number-theory',
            '--config-set', '{"chunker": "closure"}', '--stop-after', 'publish_prep')
    assert r.returncode == 0, r.stdout + r.stderr
    cfg = json.load(open(nat.dir / 'config.json'))
    assert cfg['forced'] == ['Loc.f1', 'Loc.f2', 'Loc.f3'] and cfg['budget'] == 40 and cfg['chunker'] == 'closure'
    assert json.load(open(nat.dir / 'pipeline.json'))['forced'] == ['Loc.f1', 'Loc.f2', 'Loc.f3']
    pp = [c['argv'] for c in calls(nat) if c.get('tool') == 'carve_prep' and c['argv'][0] == 'publish-prep'][0]
    assert pp[3] == 'artin,number-theory'
    assert run(nat, '--forced', str(forced), '--forced', 'Loc.f3').returncode == 0     # the same list again


def test_native_refuses_oai_only_options_and_a_bad_proves(nat):
    r = run(nat, *NARGS, '--fetch')
    assert r.returncode != 0 and '--native' in r.stderr and '--fetch' in r.stderr
    assert not (nat.dir / 'pipeline.json').exists()
    r = run(nat, *[a if a != 'Loc.goal=Pub.target@8b3180bd' else 'Loc.goal' for a in NARGS])
    assert r.returncode != 0 and 'LOCAL=PUBLISHED' in r.stderr
    r = run(nat, *[a for a in NARGS if a != '--native'][:-1], '--no-overlap')
    assert r.returncode != 0 and '--proves' in r.stderr and '--native' in r.stderr


def test_an_oai_carve_is_not_touched_by_the_native_code(env):
    # the classic route: every step still runs, in the old order, with the OpenAI source line
    from test_carve_pipeline import ARGS
    r = run(env, *ARGS)
    assert r.returncode == 0, r.stdout + r.stderr
    seq = tools_called(env)
    assert ('oai_port_modules', str(env.dir / 'src' / 'lean')) in seq and ('carve_prep', 'config') in seq
    assert ('carve_prep', 'ext-defs') in seq and ('carve_prep', 'native-prep') not in seq
    pp = [c['argv'] for c in calls(env) if c.get('tool') == 'carve_prep' and c['argv'][0] == 'publish-prep'][0]
    assert pp[2].startswith('OpenAI, T, OpenAI Math Release') and pp[3] == 'openai-math'
    assert CP.steps_for({'overlap': False}) == [s for s in CP.STEPS if s not in CP.OVERLAP_ONLY]
    assert CP.steps_for({'overlap': True}) == CP.STEPS


def test_steps_for_native():
    s = CP.steps_for({'native': True, 'overlap': True})
    assert s[0] == 'config' and not set(CP.NATIVE_SKIP) & set(s) and 'publish_early' in s
    assert CP.NATIVE_SKIP == ('fetch', 'inputs', 'filter_patches', 'port', 'build', 'wsbuild')
    assert 'measure_pieces' not in CP.steps_for({'native': True})


def test_monitor_section_counts_native_steps(nat):
    from p2mlib import carvemonitor
    assert run(nat, *NARGS, '--stop-after', 'graph').returncode == 0
    c = carvemonitor.Carve(str(nat.dir)) if hasattr(carvemonitor, 'Carve') else None
    if c is None:
        pytest.skip('carvemonitor has no Carve reader')
    steps = c.steps(False)
    assert steps[0] == 'config' and 'port' not in steps and 'publish' not in steps
    assert c.current(False)[0] == 'extdefs'


# ---------------------------------------------------------------- carve_prep native-prep, name-check

def _prep(tmp_path, monkeypatch, secs, proves=None, no_promote=None):
    import carve_prep as P
    ws = native_ws(tmp_path / 'ws')
    d = tmp_path / 'carve'
    d.mkdir()
    cfg = N.make_config(str(d), str(ws), 'Nat', ['Solutions.Nat.KP.Main'], ['Loc.goal'], proves=proves or {})
    if no_promote:
        cfg['no_promote'] = no_promote
    (d / 'config.json').write_text(json.dumps(cfg))
    mk = lambda deps, thm=True: type('Nd', (), {'deps': set(deps), 'theorem': thm})()
    g = type('G', (), {'owner': {}, 'modules': CLOSURE + ['Theorems.Thm_Pub_target'], 'nodes': {
        'Pub.target': mk([]), 'Loc.pre': mk(['Pub.target']), 'Loc.goal': mk(['Loc.pre'])}})()
    monkeypatch.setattr(P, 'native_graph', lambda c: g)
    monkeypatch.setattr(P, 'native_secs', lambda w: secs.get)
    return P, d


def test_native_prep_writes_the_build_log_and_no_promote(tmp_path, monkeypatch, capsys):
    secs = {'Solutions.Nat.KP.A': 9.5, 'Solutions.Nat.C0.B': 4.0, 'Solutions.Nat.KP.Main': 63.0}
    P, d = _prep(tmp_path, monkeypatch, secs, proves={'Loc.goal': 'Pub.target'}, no_promote=['Loc.mine'])
    P.cmd_native_prep([str(d / 'config.json')])
    log = (d / 'build_adj.log').read_text()
    assert log == ('✔ [1/1] Built Solutions.Nat.KP.A (6.5s)\n✔ [1/1] Built Solutions.Nat.C0.B (1.0s)\n'
                   '✔ [1/1] Built Solutions.Nat.KP.Main (60.0s)\n')            # project modules only
    cfg = json.load(open(d / 'config.json'))
    assert cfg['no_promote'] == ['Loc.mine', 'Loc.pre']         # a person's entries stay
    assert cfg['external_defs'] == {}
    out = capsys.readouterr().out
    assert '3 modules timed' in out and 'Loc.pre' in out


def test_native_prep_refuses_untimed_modules(tmp_path, monkeypatch):
    P, d = _prep(tmp_path, monkeypatch, {'Solutions.Nat.KP.A': 9.5})
    with pytest.raises(SystemExit) as e:
        P.cmd_native_prep([str(d / 'config.json')])
    assert 'Solutions.Nat.C0.B' in str(e.value) and '--redo graph' in str(e.value)
    assert not (d / 'build_adj.log').exists()


def test_name_check_verifies_the_published_target_and_its_id():
    import carve_prep as P
    cfg = {'proves': {'Loc.goal': 'Pub.target'}, 'proves_ids': {'Pub.target': '8b3180bd'}}
    live = {'Pub.target': {'id': '8b3180bd-1111-2222-3333-444444444444', 'author': 'someone'}}
    look = lambda kind, name: live.get(name) if kind == 'statement' else None
    assert P.proves_id_problems(cfg, look) == []
    assert P.proves_id_problems({}, look) == []
    bad = P.proves_id_problems(dict(cfg, proves_ids={'Pub.target': 'deadbeef'}), look)
    assert len(bad) == 1 and '8b3180bd-1111' in bad[0] and 'deadbeef' in bad[0]
    gone = P.proves_id_problems({'proves': {'Loc.goal': 'Pub.nope'}, 'proves_ids': {}}, look)
    assert len(gone) == 1 and 'Pub.nope' in gone[0] and 'not live' in gone[0]
    # without an id the statement must still be live
    assert P.proves_id_problems({'proves': {'Loc.goal': 'Pub.target'}}, look) == []


# ---------------------------------------------------------------- prose for our own work (p2mlib.prosetemplate)

import carve_prep as CPREP  # noqa: E402
import check_pronouns as PR  # noqa: E402
from p2mlib import explanation as E  # noqa: E402
from p2mlib import prosetemplate as T  # noqa: E402
from p2mlib.mission import front_matter  # noqa: E402

PMETA = {'title': 'A cubic theta leaf', 'credit': 'A. Author and B. Author',
         'repo': 'https://github.com/example/dev', 'commit': 'c' * 40,
         'paths': {'Solutions.Nat.KP': 'proofs/kp/lean'},
         'paper': 'P. Aper, On theta, J. Math. 1 (1984), 1-2, https://doi.org/10.1000/x'}
P_DEF = '''import Mathlib
import Definitions.Def_Pub

section
-- module Solutions.Nat.KP.Basic
namespace Loc

def Foo (n : ℕ) : ℕ := n + Pub.base

structure Bar where
  x : ℕ

theorem foo_pos (n : ℕ) : 0 < Foo n + 1 := Nat.succ_pos _

end Loc
end

section
-- module Solutions.Nat.C0.Deep
namespace Loc
def Baz : ℕ := 3
end Loc
end
'''
P_STUB = '''import Mathlib
import Definitions.Def_NB000

namespace Loc.Lemmas

open Finset

theorem lemA (n : ℕ) (he : 1 ≤ n) (b : Bar) :
    Foo n ≤ Foo (n + b.x) + Baz := by
  sorry

end Loc.Lemmas
'''
P_SOL = '''import Mathlib
import Definitions.Def_Pub
import Definitions.Def_NB000

section
-- module Solutions.Nat.KP.Lemmas
set_option linter.all false
namespace Loc.Lemmas
theorem helper (n : ℕ) : Foo n ≤ Foo n := le_refl _
theorem lemA_oai (n : ℕ) (he : 1 ≤ n) (b : Bar) : Foo n ≤ Foo (n + b.x) + Baz := by
  simp [Foo, Baz]; omega
end Loc.Lemmas
end

theorem solution : type_of% @Loc.Lemmas.lemA_oai := @Loc.Lemmas.lemA_oai
'''
P_GOAL = '''import Mathlib
import Definitions.Def_Pub
import Theorems.Thm_Loc_Lemmas_lemA

namespace Pub
abbrev target_Statement : Prop :=
  True
end Pub

section
-- module Solutions.Nat.KP.Main
namespace Loc
theorem goal : (Pub.target_Statement) := trivial
end Loc
end

theorem solution : type_of% @Loc.goal := @Loc.goal
'''
P_GRAPH = [
    {'n': 'Loc.Foo', 'm': 'Solutions.Nat.KP.Basic', 'k': 'def', 'i': False, 't': [], 'r': [5, 0, 5, 30]},
    {'n': 'Loc.Bar', 'm': 'Solutions.Nat.KP.Basic', 'k': 'inductive', 'i': False, 't': [], 'r': [7, 0, 8, 9]},
    {'n': 'Loc.Bar.x', 'm': 'Solutions.Nat.KP.Basic', 'k': 'def', 'i': False, 't': ['Loc.Bar'], 'r': None},
    {'n': 'Loc.foo_pos', 'm': 'Solutions.Nat.KP.Basic', 'k': 'theorem', 'i': False, 't': ['Loc.Foo'], 'r': [10, 0, 10, 9]},
    {'n': 'Loc.Baz', 'm': 'Solutions.Nat.C0.Deep', 'k': 'def', 'i': False, 't': [], 'r': [2, 0, 2, 9]},
    {'n': 'Loc.Lemmas.helper', 'm': 'Solutions.Nat.KP.Lemmas', 'k': 'theorem', 'i': False, 't': ['Loc.Foo'], 'r': [3, 0, 3, 9]},
    {'n': 'Loc.Lemmas.lemA', 'm': 'Solutions.Nat.KP.Lemmas', 'k': 'theorem', 'i': False,
     't': ['Loc.Foo', 'Loc.Bar', 'Loc.Bar.x', 'Loc.Baz'], 'r': [41, 0, 43, 20]},
    {'n': 'Loc.goal', 'm': 'Solutions.Nat.KP.Main', 'k': 'theorem', 'i': False, 't': [], 'r': [9, 0, 9, 9]},
]
P_PLAN = {
    'bundles': [{'name': 'NB000', 'imports': [], 'cost': 1.0, 'size': 10,
                 'nodes': ['Loc.Foo', 'Loc.Bar', 'Loc.foo_pos', 'Loc.Baz']}],
    'external': ['Loc.goal'], 'targets': ['Loc.goal'], 'forced': [], 'proves': {'Loc.goal': 'Pub.target'},
    'external_defs': {}, 'nodes': ['Loc.Lemmas.lemA', 'Loc.goal'],
    'stubs': {'Loc.Lemmas.lemA': {'bundles': ['NB000']}, 'Loc.goal': {'bundles': []}},
    'pieces': {'Loc.Lemmas.lemA': {'bundles': ['NB000'], 'imports': [],
                                    'keep': ['Loc.Lemmas.helper', 'Loc.Lemmas.lemA']},
               'Loc.goal': {'bundles': [], 'imports': ['Loc.Lemmas.lemA'], 'keep': ['Loc.goal']}},
    'statement_suffix': '', 'sorry': [], 'over': [], 'version': 1,
}


def native_carve(tmp_path):
    d, ws = tmp_path / 'carve', tmp_path / 'ws'
    (ws / 'Definitions').mkdir(parents=True)
    (ws / 'Definitions' / 'Def_Pub.lean').write_text('import Mathlib\nnamespace Pub\ndef base : ℕ := 1\nend Pub\n')
    (ws / 'Theorems').mkdir()
    (ws / 'Theorems' / 'Thm_Pub_target.lean').write_text('import Mathlib\nnamespace Pub\ntheorem target : True := by\n  sorry\nend Pub\n')
    (ws / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    (ws / 'lake-manifest.json').write_text(json.dumps({'packages': [{'name': 'mathlib', 'rev': '0df444a' + '0' * 33}]}))
    for x in ('work', 'publish/out/lib', 'publish/out/solutions', 'publish/prose', 'publish/explanations'):
        (d / x).mkdir(parents=True)
    (d / 'config.json').write_text(json.dumps({'work': str(d / 'work'), 'src': str(ws), 'native': True,
                                               'prefix': 'Solutions.Nat', 'targets': ['Loc.goal'], 'forced': [],
                                               'proves': {'Loc.goal': 'Pub.target'}}))
    (d / 'work' / 'decl_graph.jsonl').write_text(''.join(json.dumps(x) + '\n' for x in P_GRAPH))
    (d / 'native_meta.json').write_text(json.dumps(PMETA))
    P = d / 'publish'
    (P / 'plan.json').write_text(json.dumps(P_PLAN))
    (P / 'out/lib/Def_NB000.lean').write_text(P_DEF)
    (P / 'out/lib/Thm_Loc_Lemmas_lemA.lean').write_text(P_STUB)
    (P / 'out/solutions/Sol_Loc_Lemmas_lemA.lean').write_text(P_SOL)
    (P / 'out/solutions/Sol_Pub_target.lean').write_text(P_GOAL)
    return d, ws


def _no_openai(text):
    import re
    assert 'OpenAI' not in text and 'openai' not in text and 'Apache' not in text, text
    assert not re.search(r'\b(ported|port)\b', text), text


def test_native_templates_are_written_and_the_goal_needs_written_prose(tmp_path):
    d, _ = native_carve(tmp_path)
    rep = T.write_templates(str(d))
    P = d / 'publish'
    assert sorted(os.listdir(P / 'prose')) == [T.MANIFEST, 'Loc_Lemmas_lemA.md', 'NB000.md']
    assert sorted(os.listdir(P / 'explanations')) == [T.MANIFEST, 'Loc_Lemmas_lemA.md']
    # the goal's statement is published already: only its explanation is to write, under the published name
    assert rep['needs_written'] == ['explanation Pub.target (goal): write explanations/Pub_target.md']
    for f in ('prose/Loc_Lemmas_lemA.md', 'prose/NB000.md', 'explanations/Loc_Lemmas_lemA.md'):
        _no_openai((P / f).read_text())


def test_native_statement_prose_credits_the_development_and_links_the_declaration(tmp_path):
    d, _ = native_carve(tmp_path)
    T.write_templates(str(d))
    fields, body = front_matter((d / 'publish/prose/Loc_Lemmas_lemA.md').read_text())
    assert fields['template'] == T.MARK
    assert fields['title'] == 'Loc.Lemmas.lemA: intermediate lemma of A cubic theta leaf'
    link = 'https://github.com/example/dev/blob/%s/proofs/kp/lean/Lemmas.lean#L41' % ('c' * 40)
    assert fields['source'].startswith(N.source_line(PMETA)) and link in fields['source']
    assert 'declaration Loc.Lemmas.lemA' in fields['source']
    assert 'A. Author and B. Author' in body and '*A cubic theta leaf*' in body and link in body
    assert '`Pub.target`' in body and '`Loc.goal`' not in body          # the goal by its published name
    assert 'P. Aper, On theta' in body
    assert ('```lean\ntheorem lemA (n : ℕ) (he : 1 ≤ n) (b : Bar) :\n'
            '    Foo n ≤ Foo (n + b.x) + Baz\n```') in body
    assert '`Loc.Foo`' in body and '`Loc.Bar`' in body and '`NB000`' in body
    assert 'Lean 4.33.1' in body and 'Mathlib 0df444a' in body
    assert 'The proof of `Pub.target` of this split imports it.' in body


def test_native_bundle_prose(tmp_path):
    d, _ = native_carve(tmp_path)
    T.write_templates(str(d))
    fields, body = front_matter((d / 'publish/prose/NB000.md').read_text())
    assert fields['title'] == 'Definitions bundle NB000 of the split of A cubic theta leaf'
    assert fields['source'].startswith(N.source_line(PMETA))
    assert '4 declarations' in body and '`Loc.Foo`' in body
    # a module the meta maps is linked; one it does not map is named only
    assert '[`KP.Basic`](https://github.com/example/dev/blob/%s/proofs/kp/lean/Basic.lean)' % ('c' * 40) in body
    assert '`C0.Deep`' in body and 'C0/Deep.lean' not in body
    assert '`Def_Pub`' in body and '`Loc.Lemmas.lemA`' in body


def test_native_explanation_meets_the_rules(tmp_path):
    d, _ = native_carve(tmp_path)
    T.write_templates(str(d))
    t = (d / 'publish/explanations/Loc_Lemmas_lemA.md').read_text()
    assert E.problems(t) == [] and t.lstrip().startswith('$$') and not t.startswith('---')
    assert '```lean\ntheorem lemA' in t and '`lemA_oai`' in t and '`NB000`' in t and '`Def_Pub`' in t
    assert '2 declarations' in t and 'no `sorry`' in t
    assert 'A. Author and B. Author' in t and 'https://github.com/example/dev' in t and 'ccccccc' in t
    assert 'P. Aper, On theta' in t
    # the goal's own explanation is written by hand, but the function renders any piece, the goal's too
    g = T.explanation(T.Context(str(d)), 'Loc.goal')
    assert E.problems(g) == [] and '`Pub.target`' in g and 'Loc.goal' in g and '`Loc.Lemmas.lemA`' in g
    _no_openai(g)


def test_native_templates_pass_check_text_and_the_pronoun_check(tmp_path, capsys):
    d, ws = native_carve(tmp_path)
    T.write_templates(str(d))
    (d / 'publish/explanations/Pub_target.md').write_text(T.explanation(T.Context(str(d)), 'Loc.goal'))
    with pytest.raises(SystemExit) as e:
        CPREP.cmd_check_text([str(d / 'publish'), '--ws', str(ws)])
    out = capsys.readouterr().out
    assert e.value.code == 0, out
    assert PR.scan_local([str(d / 'publish' / 'prose'), str(d / 'publish' / 'explanations')]) == []


def test_native_templates_for_a_private_source_have_no_links(tmp_path, capsys):
    """`"repo": null`: credit and commit-free text only, in every item, and check-text still passes."""
    d, ws = native_carve(tmp_path)
    (d / 'native_meta.json').write_text(json.dumps(dict(PMETA, repo=None)))
    T.write_templates(str(d))
    P = d / 'publish'
    (P / 'explanations/Pub_target.md').write_text(T.explanation(T.Context(str(d)), 'Loc.goal'))
    for f in ('prose/Loc_Lemmas_lemA.md', 'prose/NB000.md', 'explanations/Loc_Lemmas_lemA.md',
              'explanations/Pub_target.md'):
        t = (P / f).read_text()
        assert 'github.com' not in t and 'example/dev' not in t and 'ccccccc' not in t, (f, t)
        assert 'A. Author and B. Author' in t, f
        _no_openai(t)
    with pytest.raises(SystemExit) as e:
        CPREP.cmd_check_text([str(P), '--ws', str(ws)])
    out = capsys.readouterr().out
    assert e.value.code == 0, out


def test_meta_kind_is_told_from_the_files(tmp_path):
    d, _ = native_carve(tmp_path)
    assert T.Context(str(d)).native is True
    # an explicit OpenAI meta still gives the OpenAI text (an openai/math port is unchanged)
    with pytest.raises(SystemExit) as e:
        T.Context(str(d), {'title': 'x'})
    assert 'oai_meta.json' in str(e.value)
    (d / 'native_meta.json').write_text(json.dumps({k: v for k, v in PMETA.items() if k != 'credit'}))
    with pytest.raises(SystemExit) as e:
        T.Context(str(d))
    assert 'credit' in str(e.value)


# ---------------------------------------------------------------- the goal piece against the existing theorem

def _proves_split(tmp_path):
    """A split whose target Loc.goal proves the statement published as Pub.target (no stub of ours)."""
    d = tmp_path
    for sub in ('out/lib', 'out/solutions', 'prose', 'explanations'):
        (d / sub).mkdir(parents=True, exist_ok=True)
    (d / 'out/lib/Def_NB000.lean').write_text('import Mathlib\n\ndef NB000.k : Nat := 1\n')
    (d / 'prose/NB000.md').write_text('---\ntitle: Bundle NB000\n---\n\nDefinitions.\n')
    (d / 'out/solutions/Sol_Pub_target.lean').write_text('import Mathlib\n\ntheorem solution : True := trivial\n')
    (d / 'explanations/Pub_target.md').write_text(
        'The statement is\n\n$$x = x$$\n\nand it holds by reflexivity of equality, which is all the proof uses; '
        'the carved file states it, imports the bundle that defines the objects, and closes the goal with '
        '`rfl` after unfolding the definitions involved in the claim.\n')
    plan = {'bundles': [{'name': 'NB000', 'imports': [], 'nodes': ['Loc.a']}], 'stubs': {},
            'pieces': {'Loc.goal': {'bundles': ['NB000'], 'imports': []}},
            'external': ['Loc.goal'], 'proves': {'Loc.goal': 'Pub.target'},
            'proves_ids': {'Pub.target': '8b3180bd'}}
    (d / 'plan.json').write_text(json.dumps(plan))
    return {'plan': str(d / 'plan.json'), 'out': str(d / 'out'), 'prose': str(d / 'prose'),
            'explanations': str(d / 'explanations'), 'state': str(d / 'run_state.json'),
            'log': str(d / 'PROGRESS.log'), 'source': 'x', 'tags': ['t'], 'jobs': 8}


def test_split_run_submits_the_goal_piece_against_the_existing_theorem(tmp_path):
    from test_splitrun import FakeApi
    from p2mlib import splitrun as R
    cfg = _proves_split(tmp_path)
    api = FakeApi(published={'Pub.target': '8b3180bd-123f'})
    R.Runner(cfg, api, sleep=lambda s: None).run()
    assert ('verify', 'Pub.target') in api.posted
    assert not [x for x in api.posted if x[0] == 'thm']          # no statement of ours for it


def test_split_run_refuses_a_live_target_whose_id_is_not_the_given_one(tmp_path):
    from test_splitrun import FakeApi
    from p2mlib import splitrun as R
    cfg = _proves_split(tmp_path)
    api = FakeApi(published={'Pub.target': 'ffff0000-other'})
    summary = R.Runner(cfg, api, sleep=lambda s: None).run()
    assert ('verify', 'Pub.target') not in api.posted
    assert summary['stopped'] == ['piece:Loc.goal']
    st = json.loads(open(cfg['state']).read())['piece:Loc.goal']
    assert st['state'] == 'stop' and '8b3180bd' in st['last'] and 'ffff0000-other' in st['last']


def test_carve_plan_records_the_proves_ids(tmp_path):
    import shutil
    import subprocess
    from test_carve import FIX, TARGETS
    work = tmp_path / 'work'
    work.mkdir()
    shutil.copy(os.path.join(FIX, 'decl_graph.jsonl'), work / 'decl_graph.jsonl')
    cfg = tmp_path / 'carve.json'
    cfg.write_text(json.dumps({'src': FIX, 'prefix': 'CarveDev', 'roots': ['CarveDev.Top'], 'targets': TARGETS,
                               'external': ['CD.main'], 'proves': {'CD.main': 'Pub.main_theorem'},
                               'proves_ids': {'Pub.main_theorem': '8b3180bd'}, 'work': str(work),
                               'out': str(tmp_path / 'out'), 'bundle_prefix': 'CDB', 'budget': 0.05,
                               'bundle_budget': 0.005, 'bytes_per_second': 10000}))
    r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'carve.py'), 'plan', str(cfg)],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
    P = json.loads((work / 'plan.json').read_text())
    assert P['proves'] == {'CD.main': 'Pub.main_theorem'} and P['proves_ids'] == {'Pub.main_theorem': '8b3180bd'}


# ---------------------------------------------------------------- a statement's definitions, for a read-back

def test_stage_auditor_carve_view_writes_the_signature_definitions(tmp_path, capsys):
    import stage_auditor as SA
    from test_carve import FIX
    cfg = tmp_path / 'config.json'
    cfg.write_text(json.dumps({'src': FIX, 'work': FIX}))
    out = tmp_path / 'view' / 'uses_sized.defs.lean'
    path = SA.carve_view(str(cfg), 'CD.uses_sized', str(out))
    assert path == str(out)
    text = out.read_text()
    assert 'structure Space where' in text and 'def sizedZero' in text and 'uses_sized' not in text
    said = capsys.readouterr().out
    assert '3 definitions' in said and 'CD.Space.size_eq' in said
    # by its published name, through the plan; the default output sits beside the config
    (tmp_path / 'plan.json').write_text(json.dumps({'stubs': {'CD.uses_sized': {}}, 'pieces': {},
                                                    'statement_suffix': '_s2'}))
    cfg.write_text(json.dumps({'src': FIX, 'work': FIX, 'plan': str(tmp_path / 'plan.json')}))
    p2 = SA.carve_view(str(cfg), 'CD.uses_sized_s2')
    assert p2 == str(tmp_path / 'readback_views' / 'CD_uses_sized_s2.defs.lean') and os.path.exists(p2)
    with pytest.raises(SystemExit) as e:
        SA.carve_view(str(cfg), 'CD.nothing_here')
    assert 'CD.nothing_here' in str(e.value)


# ---------------------------------------------------------------- a per-module measurement as the cost model

def test_native_prep_takes_times_from_a_measurement_file(tmp_path, monkeypatch, capsys):
    # PACKAGING.md 3.2: the trial's build log was the per-module CPU of times.jsonl less the 3 s import;
    # a module the file lacks falls back to LeanInfo's recorded time
    P, d = _prep(tmp_path, monkeypatch, {'Solutions.Nat.C0.B': 4.0})
    times = tmp_path / 'times.jsonl'
    times.write_text('{"module": "Solutions.Nat.KP.A", "build_s": 8.5, "wall_s": 30, "errors": []}\n'
                     '{"module": "Solutions.Nat.KP.Main", "build_s": 13.0, "wall_s": 40, "errors": []}\n'
                     '{"module": "Solutions.Nat.Elsewhere", "build_s": 99.0}\n')
    P.cmd_native_prep([str(d / 'config.json'), '--times', str(times)])
    log = (d / 'build_adj.log').read_text()
    assert log == ('✔ [1/1] Built Solutions.Nat.KP.A (5.5s)\n✔ [1/1] Built Solutions.Nat.C0.B (1.0s)\n'
                   '✔ [1/1] Built Solutions.Nat.KP.Main (10.0s)\n')
    assert '2 from %s' % times in capsys.readouterr().out
    assert N.read_times(str(times))['Solutions.Nat.Elsewhere'] == 99.0


def test_native_times_reach_native_prep_and_make_it_stale(nat):
    times = nat.tmp / 'times.jsonl'
    times.write_text('{"module": "Solutions.Nat.KP.A", "build_s": 8.5}\n')
    r = run(nat, *NARGS, '--times', str(times), '--stop-after', 'extdefs')
    assert r.returncode == 0, r.stdout + r.stderr
    argv = [c['argv'] for c in calls(nat) if c.get('tool') == 'carve_prep' and c['argv'][0] == 'native-prep'][0]
    assert argv[argv.index('--times') + 1] == str(times)
    assert json.load(open(nat.dir / 'pipeline.json'))['times'] == str(times)
    times.write_text('{"module": "Solutions.Nat.KP.A", "build_s": 9.5}\n')
    nat.log.write_text('')
    r = run(nat, '--stop-after', 'extdefs')
    assert r.returncode == 0 and '== stale: extdefs' in r.stdout, r.stdout
