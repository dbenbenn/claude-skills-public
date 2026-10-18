"""The carver (p2mlib.carve, scripts/carve.py) on the CarveDev fixture development.

lean_fixtures/carve/CarveDev/*.lean is a four-module development in core Lean (it compiles in
seconds) with one instance of every bug class the five split variants hit (2026-10-07/08):
multi-line `variable` and `omit … in`, namespace blocks left empty, ranges running into the next
declaration, children of imported declarations kept again, a missing trailing newline, `local
notation` naming a declaration, a dead `open` (Erdős 3 B007), a definition a bundle needs only
through the source (B006), the `<name>_oai` rename, macros, private-name collisions.

Offline tests replay the recorded DeclGraph and LeanInfo output (tests/record_fixtures.py carve
re-records it). With P2M_LEAN=1 the tools must reproduce the recordings, and every generated file
must compile in publish order, with each `solution` stating exactly its published statement."""
import json
import os
import re

import pytest

from p2mlib import carve as C

HERE = os.path.dirname(os.path.abspath(__file__))
FIX = os.path.join(HERE, 'lean_fixtures', 'carve')
TARGETS = ['CD.main', 'CD.top_aux', 'CD.top_pick']


@pytest.fixture(scope='module')
def g():
    return C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)


@pytest.fixture(scope='module')
def plan(g):
    # tiny budgets, so the fixture splits into several bundles and promotes intermediate nodes
    return C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.005,
                       bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                       bundle_prefix='CDB')


def node_text(g, key):
    n = g.nodes[key]
    info = g.infos[n.module]
    a, b = info.command_span(n.cmd)
    return info.slice(a, b)


# ---------------------------------------------------------------- the graph

def test_nodes_are_commands_and_own_their_children(g):
    sp = g.nodes['CD.Space']
    assert {'CD.Space.carrier', 'CD.Space.pt', 'CD.Space.mk', 'CD.Space.rec',
            'CD.Space.mk.injEq'} <= set(sp.names)
    assert g.owner['CD.Space.pt'] == 'CD.Space'
    # a notation's generated parser and macro constants are not declarations
    assert not any('termDE' in k or 'termAUX' in k for k in g.nodes)
    assert not any(k.startswith('CD.Mac.termTwice') for k in g.nodes)


def test_source_dependencies_catch_rfl_simp_lemmas(g):
    # `simp only [double_eq]` rewrites by dsimp and leaves no trace in the term
    ds = g.nodes['CD.double_succ']
    assert 'CD.double_eq' not in ds.term and 'CD.double_eq' in ds.deps


def test_dot_notation_on_a_local_is_a_dependency(g):
    # Erdős 3 B024 ("Unknown identifier `coord`"): `dsimp only [A.coord_eq]` with `A` a local names
    # Space.coord_eq through dot notation and leaves no trace in the term
    sv = g.nodes['CD.size_via_coord']
    assert 'CD.Space.coord_eq' not in sv.term and 'CD.Space.coord_eq' in sv.deps


def test_local_notation_names_are_dependencies_of_what_follows(g):
    # `local notation "DE" => double_eq` precedes `size_zero` in Mid's scope: a file keeping
    # size_zero keeps the notation, whose identifiers Lean prechecks
    assert 'CD.double_eq' in g.nodes['CD.size_zero'].deps


def test_private_names_are_per_module(g):
    a, b = '_private.CarveDev.Mid.0.CD.helper', '_private.CarveDev.Top.0.CD.helper'
    assert a in g.nodes and b in g.nodes
    assert a in g.nodes['CD.double_succ'].deps and b not in g.nodes['CD.double_succ'].deps
    assert b in g.nodes['CD.main'].deps
    assert C.collision_renames(g) == {a: 'helper_p0', b: 'helper_p1'}


def test_attributed_theorem_is_an_extra_root(g):
    # `size_zero` is `by simp` with the rfl simp lemma Space.size_eq: no trace in the term, so the
    # simp lemma comes in as an attributed root whenever its dependencies are present
    assert 'CD.Space.size_eq' not in g.nodes['CD.size_zero'].deps
    assert g.nodes['CD.Space.size_eq'].attributed
    assert 'CD.Space.size_eq' in g.extra_roots({'CD.Space', 'CD.Space.size', 'CD.size_zero'}, set())


def test_attribute_command_marks_its_target(g):
    assert g.nodes['CD.Aux.auxOnly'].attributed


# ---------------------------------------------------------------- the plan

def test_plan_is_valid(g, plan):
    assert C.check_plan(g, plan) == []
    allb = [n for b in plan['bundles'] for n in b['nodes']]
    assert len(allb) == len(set(allb))
    assert {'CD.Space', 'CD.Space.size', 'CD.double', 'CD.List.headOr', 'CD.Aux.auxOnly'} <= set(allb)
    assert 'CD.Space.size_eq' in allb             # attributed, its dependencies in the bundles
    assert 'CD.unusedDef' not in allb and 'CD.Mac.useMac' not in allb
    assert set(TARGETS) <= set(plan['nodes'])
    for n in plan['nodes']:
        assert n in plan['pieces'][n]['keep']


def test_bundles_form_a_dag_with_independent_bundles(g, plan):
    names = [b['name'] for b in plan['bundles']]
    assert len(names) >= 3
    pos = {n: i for i, n in enumerate(names)}
    for b in plan['bundles']:
        assert all(pos[i] < pos[b['name']] for i in b['imports'])
    # Alt's bundle and Mid's do not import each other: they publish concurrently
    order = C.publish_order(plan)
    first = [w for w in order['waves'] if any(x.startswith('bundle:') for x in w)]
    assert any(sum(x.startswith('bundle:') for x in w) >= 2 for w in first)


def test_budget_promotes_intermediate_nodes(g, plan):
    assert len(plan['nodes']) > len(TARGETS)
    main = plan['pieces']['CD.main']
    assert main['imports'] and set(main['imports']) <= set(plan['nodes'])


def test_check_plan_flags_a_definition_missing_from_the_bundles(g, plan):
    # Erdős 3 B006 ("Unknown identifier `A.space`"): a bundle lost a definition one of its own
    # members needs. The check must say which and why.
    bad = json.loads(json.dumps(plan))
    for b in bad['bundles']:
        if 'CD.Space' in b['nodes']:
            b['nodes'].remove('CD.Space')
    probs = C.check_plan(g, bad)
    assert probs and any('CD.Space' in p for p in probs)


def test_forced_theorem_a_definition_needs_is_a_clear_error(g):
    # StrictInverseFirstPower (2026-10-18): forcing Bieberbach's |a₂| ≤ 2, which the instance
    # `CompactSpace DiskFamily` needs, crashed make_plan with KeyError. `CD.double_eq` is a theorem
    # the definition `CD.sizedZero` uses, so it is bundle material once `CD.uses_sized` is a target
    with pytest.raises(C.CarveError, match=r'CD\.double_eq.*bundle.*CD\.sizedZero'):
        C.make_plan(g, ['CD.uses_sized'], forced=['CD.double_eq'], cost=C.size_costs(g))
    # a target pulled into a bundle the same way gets the same error
    with pytest.raises(C.CarveError, match=r'CD\.double_eq.*bundle'):
        C.make_plan(g, ['CD.uses_sized', 'CD.double_eq'], cost=C.size_costs(g))


def test_sorry_never_reaches_a_bundle_or_piece(g, plan):
    # Erdős 3 B022 ("declaration uses `sorry`"): a port's stubbed proof leaked into a bundle
    assert g.nodes['CD.sorried'].sorry and not g.nodes['CD.double'].sorry
    assert plan['sorry'] == [] and C.check_plan(g, plan) == []
    bad = C.make_plan(g, ['CD.uses_sorry'], cost=C.size_costs(g), bundle_prefix='X')
    assert 'CD.sorried' in bad['sorry']
    probs = C.check_plan(g, bad)
    assert any('CD.sorried uses sorry' in p for p in probs)
    b = next(b['name'] for b in bad['bundles'] if 'CD.sorried' in b['nodes'])
    with pytest.raises(C.CarveError, match='sorry'):
        C.gen_bundle(g, bad, b)


def test_check_plan_reports_bundle_import_cycles_as_cycles(g):
    # UniversalFInfinity (2026-10-18): a hand-pinned bundle missed one dependency, so it and a
    # later bundle needed each other; the imports were silently reduced away and the check only
    # said "needs … from bundle …, not imported". A cycle can never be published: say so.
    plan = {'bundles': [{'name': 'Y0', 'nodes': ['CD.Space.size'], 'imports': []},
                        {'name': 'Y1', 'nodes': ['CD.Space', 'CD.Space.size_eq'], 'imports': []}],
            'nodes': [], 'pieces': {}, 'stubs': {}}
    probs = C.check_plan(g, plan)
    cyc = [p for p in probs if 'cycle' in p]
    assert len(cyc) == 1
    assert 'Y0' in cyc[0] and 'Y1' in cyc[0]
    # the witnesses: which member needs which declaration across the cycle
    assert 'CD.Space.size' in cyc[0] and 'CD.Space.size_eq' in cyc[0]
    # an acyclic plan reports none
    plan['bundles'] = [{'name': 'Y0', 'nodes': ['CD.Space'], 'imports': []},
                       {'name': 'Y1', 'nodes': ['CD.Space.size', 'CD.Space.size_eq'], 'imports': ['Y0']}]
    assert not [p for p in C.check_plan(g, plan) if 'cycle' in p]


def test_publish_order_puts_statements_after_bundles_and_pieces_last(plan):
    order = C.publish_order(plan, external=['CD.main'])
    wave = {x: i for i, w in enumerate(order['waves']) for x in w}
    assert 'statement:CD.main' not in wave             # published by someone else
    for n, st in plan['stubs'].items():
        if n == 'CD.main':
            continue
        for b in st['bundles']:
            assert wave['bundle:' + b] < wave['statement:' + n]
    for n, p in plan['pieces'].items():
        for i in p['imports']:
            assert wave['statement:' + i] < wave['piece:' + n]


# ---------------------------------------------------------------- carving

def carve(g, keep, have=(), **kw):
    keep = set(keep)
    have = {C.pubname(c) for k in keep | set(have) for c in g.nodes[k].names}
    return C.Carver(g).carve(keep, have, **kw)


def test_multiline_variable_include_and_omit_lose_a_dropped_binder(g):
    # `variable (A …)\n  (n …)\n  (hx : Aux.auxOnly = 1)` with Aux.auxOnly gone: only the hx group
    # goes; `include hx` goes; the two-line `omit\n  hx in` head of a kept theorem goes whole
    txt = carve(g, {'CD.size_zero', 'CD.double_succ', '_private.CarveDev.Mid.0.CD.helper',
                    'CD.double_eq'}, {'CD.Space', 'CD.Space.size', 'CD.double', 'CD.Space.size_eq'})
    assert 'hx' not in txt and 'auxOnly' not in txt
    assert re.search(r'variable \(A : Space\)\s+\(n : Nat\)', txt)
    assert 'omit' not in txt and 'include' not in txt
    assert 'theorem size_zero : A.size = 0 := by simp' in txt


def test_empty_namespace_block_goes_with_its_notation_and_attributes(g):
    txt = carve(g, {'CD.double_eq'}, {'CD.double'})
    assert 'CD.Aux' not in txt and 'AUX' not in txt and 'attribute' not in txt
    assert 'theorem double_eq' in txt


def test_ranges_stop_at_the_next_declaration(g):
    # `def Space.size` (with its doc comment) sits on the line before `@[simp] theorem
    # Space.size_eq`: dropping one must leave the other whole, attribute and all
    txt = carve(g, {'CD.Space.size_eq'}, {'CD.Space', 'CD.Space.size'})
    assert '@[simp] theorem Space.size_eq (A : Space) : A.size = 0 := rfl' in txt
    assert 'def Space.size' not in txt and 'always zero' not in txt
    txt2 = carve(g, {'CD.Space.size'}, {'CD.Space'})
    assert 'def Space.size (_A : Space) : Nat := 0' in txt2 and 'size_eq' not in txt2


def test_children_of_an_available_declaration_are_not_redeclared(g):
    txt = carve(g, {'CD.Space.size'}, {'CD.Space'})
    assert 'structure Space' not in txt and 'carrier' not in txt


def test_missing_trailing_newline_does_not_merge_names(g):
    # Base.lean ends in `end CD.Aux` with no newline; Mid's section follows it
    txt = carve(g, {'CD.Aux.aux_eq', 'CD.uses_hx'}, {'CD.Aux.auxOnly'})
    assert 'end CD.Aux\n' in txt and 'Auxend' not in txt and 'Auxsection' not in txt


def test_local_notation_with_a_gone_identifier_is_dropped(g):
    # Mid's `local notation "DE" => double_eq`, double_eq not kept: the notation goes (Lean would
    # answer "Unknown identifier at quotation precheck")
    txt = carve(g, {'CD.uses_hx'}, {'CD.Aux.auxOnly'})
    assert '"DE"' not in txt
    txt2 = carve(g, {'CD.double_zero', 'CD.double_eq'}, {'CD.double'})
    assert 'local notation "DE" => double_eq' in txt2


def test_open_of_a_dead_namespace_is_dropped(g):
    # Erdős 3 B007 ("unknown namespace `_root_.OAI.Set`"): Top's `open Aux` and
    # `open _root_.CD.Aux in` name CD.Aux, which nothing kept or available populates
    keep = {'CD.main', '_private.CarveDev.Top.0.CD.helper'}
    have = {'CD.Space', 'CD.Space.size', 'CD.double', 'CD.List.headOr', 'CD.size_zero',
            'CD.double_succ', 'CD.List.headOr_nil'}
    txt = carve(g, keep, have)
    assert 'open Aux' not in txt and 'CD.Aux' not in txt
    txt2 = carve(g, {'CD.top_aux'}, {'CD.Aux.auxOnly', 'CD.Aux.aux_eq'})
    assert 'open Aux' in txt2 and 'open _root_.CD.Aux in' in txt2


def test_open_that_would_see_a_later_module_namespace_is_pinned_to_root(g):
    # Alt (namespace CD.List) comes before Mid in the carved file, but Mid never imported Alt:
    # its `open List` meant only `_root_.List`, and must keep meaning that
    txt = carve(g, {'CD.List.headOr', 'CD.double_zero', 'CD.double_eq'}, {'CD.double'})
    assert txt.index('-- module CarveDev.Alt') < txt.index('-- module CarveDev.Mid')
    assert 'open _root_.List' in txt
    # without Alt in the file it is rooted too: CD.List exists in the project, and a statement is
    # read after its solution, which may declare it (Erdős 3 v2, `open MvPolynomial`)
    txt2 = carve(g, {'CD.double_zero', 'CD.double_eq'}, {'CD.double'})
    assert 'open _root_.List' in txt2


def test_macro_commands_are_refused(g):
    with pytest.raises(C.CarveError, match='macro'):
        carve(g, {'CD.Mac.useMac'})


def test_examples_and_diagnostics_are_dropped(g):
    txt = carve(g, {'CD.double_succ', 'CD.double_eq', '_private.CarveDev.Mid.0.CD.helper'},
                {'CD.double'})
    assert 'example' not in txt and '#check' not in txt


def test_private_collisions_are_renamed_consistently(g):
    keep = {'CD.main', '_private.CarveDev.Top.0.CD.helper', 'CD.double_succ',
            '_private.CarveDev.Mid.0.CD.helper', 'CD.double_eq', 'CD.size_zero', 'CD.Space.size_eq'}
    have = {'CD.Space', 'CD.Space.size', 'CD.double', 'CD.List.headOr', 'CD.List.headOr_nil'}
    txt = carve(g, keep, have, rename=C.collision_renames(g))
    assert 'private theorem helper_p0 : True' in txt and 'private theorem helper_p1 : 1 = 1' in txt
    assert txt.count('have := helper_p0') == 1 and txt.count('have := helper_p1') == 1


def test_deprivatize_for_bundles(g):
    txt = carve(g, {'_private.CarveDev.Mid.0.CD.helper'}, deprivatize=True)
    assert 'private' not in txt and 'theorem helper : True' in txt


def test_universes_stay_in_their_module_section(g, plan):
    # Base, Mid and Top each declare `universe u`; each module is its own section, where a level
    # may be declared again, and `solution` names the target's levels explicitly
    txt = C.gen_piece(g, plan, 'CD.top_pick')
    assert txt.count('universe u\n') == len(re.findall('^-- module ', txt, re.M))
    assert txt.rstrip().endswith(
        'theorem solution.{u} : type_of% @CD.top_pick_oai.{u} := @CD.top_pick_oai.{u}')


# ---------------------------------------------------------------- generated files

def test_stub_is_the_statement_in_its_context(g, plan):
    n = next(x for x in plan['nodes'] if x == 'CD.size_zero') if 'CD.size_zero' in plan['nodes'] \
        else 'CD.main'
    txt = C.gen_stub(g, plan, n)
    assert re.search(r'^import Definitions\.Def_CDB\d+', txt, re.M)
    assert txt.rstrip().endswith('end CD\nend')
    assert ':= by\n  sorry' in txt and 'rw [' not in txt and 'simp' not in txt.split('theorem', 1)[1]
    assert '/--' not in txt


def test_piece_renames_the_target_and_ends_with_solution(g, plan):
    txt = C.gen_piece(g, plan, 'CD.main')
    assert re.search(r'^theorem main_oai \(A : Space\)', txt, re.M)
    assert txt.rstrip().endswith('theorem solution : type_of% @CD.main_oai := @CD.main_oai')
    for i in plan['pieces']['CD.main']['imports']:
        assert 'import Theorems.Thm_%s\n' % C.slug(i) in txt
    assert 'theorem main ' not in txt


def test_generated_sizes_are_reported(g, plan, tmp_path):
    report = C.generate(g, plan, str(tmp_path))
    assert report['over_cap'] == []
    for f in report['files']:
        if '/lib/Def_' in f or '/solutions/' in f:
            assert 'sorry' not in open(f).read(), f
    files = {os.path.relpath(p, tmp_path) for p in report['files']}
    assert {'lib/Def_%s.lean' % b['name'] for b in plan['bundles']} <= files
    assert 'solutions/Sol_CD_main.lean' in files and 'lib/Thm_CD_top_aux.lean' in files


def test_cost_from_build_log():
    log = ('✔ [3/9] Built CarveDev.Base (1.5s)\n⚠ [4/9] Built CarveDev.Mid (820ms)\n'
           'info: something else\n')
    assert C.parse_build_log(log) == {'CarveDev.Base': 1.5, 'CarveDev.Mid': 0.82}


# ---------------------------------------------------------------- with Lean

@pytest.mark.lean
def test_tools_reproduce_the_recordings(tmp_path):
    rec = C.record_fixture(FIX, 'CarveDev', ['CarveDev.Top'], str(tmp_path / 'olean'),
                           str(tmp_path / 'rec'))
    for rel in rec:
        new = open(os.path.join(tmp_path, 'rec', rel), encoding='utf-8').read()
        old = open(os.path.join(FIX, rel), encoding='utf-8').read()
        assert new == old, rel


@pytest.mark.lean
def test_generated_files_compile_in_publish_order(g, plan, tmp_path):
    _compile_in_publish_order(g, plan, tmp_path)


@pytest.mark.lean
def test_scoped_notations_and_silent_simp_lemmas_compile(g, tmp_path):
    # one-declaration bundles: a scoped notation and an rfl simp lemma land apart from their users
    p = C.make_plan(g, ['CD.uses_scoped', 'CD.uses_sized'], budget=0.05, piece_size=10**6,
                    bundle_budget=0.0001, bundle_size=10**6,
                    cost=C.size_costs(g, bytes_per_second=10000), bundle_prefix='N',
                    chunker='schedule')
    _compile_in_publish_order(g, p, tmp_path)


def _compile_in_publish_order(g, plan, tmp_path):
    out = str(tmp_path / 'out')
    C.generate(g, plan, out)
    olean = str(tmp_path / 'olean')
    # the platform's view: Definitions.Def_*, Theorems.Thm_*, and each solution on its own
    order = C.publish_order(plan)
    for wave in order['waves']:
        for item in wave:
            kind, name = item.split(':', 1)
            if kind == 'bundle':
                C.compile_file(os.path.join(out, 'lib', 'Def_%s.lean' % name),
                               'Definitions.Def_' + name, olean)
            elif kind == 'statement':
                C.compile_file(os.path.join(out, 'lib', 'Thm_%s.lean' % C.slug(name)),
                               'Theorems.Thm_' + C.slug(name), olean)
            else:
                mod = 'Solutions.Sol_' + C.slug(name)
                C.compile_file(os.path.join(out, 'solutions', 'Sol_%s.lean' % C.slug(name)), mod, olean)
                # the verifier's check: `solution` states exactly the published statement
                chk = tmp_path / ('Chk_%s.lean' % C.slug(name))
                chk.write_text('import Lean\nimport Theorems.Thm_%s\nimport %s\nopen Lean in\n'
                               'run_meta do\n'
                               '  let a := (← getConstInfo `%s).type\n'
                               '  let b := (← getConstInfo `solution).type\n'
                               '  unless a == b do throwError "solution states {b}, not {a}"\n'
                               % (C.slug(name), mod, name))
                C.compile_file(str(chk), None, olean)


def test_command_line_plan_gen_order(tmp_path):
    import shutil
    import subprocess
    import sys
    work = tmp_path / 'work'
    work.mkdir()
    shutil.copy(os.path.join(FIX, 'decl_graph.jsonl'), work / 'decl_graph.jsonl')
    cfg = tmp_path / 'carve.json'
    cfg.write_text(json.dumps({'src': FIX, 'prefix': 'CarveDev', 'roots': ['CarveDev.Top'],
                               'targets': TARGETS, 'external': ['CD.main'], 'work': str(work),
                               'out': str(tmp_path / 'out'), 'bundle_prefix': 'CDB',
                               'budget': 0.05, 'bundle_budget': 0.005, 'bytes_per_second': 10000}))
    script = os.path.join(os.path.dirname(HERE), 'scripts', 'carve.py')

    def run(*a):
        r = subprocess.run([sys.executable, script] + list(a), capture_output=True, text=True)
        assert r.returncode == 0, r.stdout + r.stderr
        return r.stdout
    out = run('plan', str(cfg))
    assert 'bundles' in out and 'PROBLEM' not in out
    assert 'plan OK' in run('check', str(cfg))
    run('gen', str(cfg))
    assert (tmp_path / 'out' / 'solutions' / 'Sol_CD_main.lean').exists()
    assert not (tmp_path / 'out' / 'lib' / 'Thm_CD_main.lean').exists()      # external
    waves = run('order', str(cfg))
    assert waves.startswith('wave 0') and 'statement:CD.main' not in waves
    # split: only the bundle measured over the limit is cut, the old plan is kept as a backup
    P = json.loads((work / 'plan.json').read_text())
    big = max(P['bundles'], key=lambda b: len(b['nodes']))
    times = {b['name']: {'secs': 99.0 if b is big else 1.0, 'ok': True} for b in P['bundles']}
    (tmp_path / 'times.json').write_text(json.dumps(times))
    assert len(big['nodes']) > 1
    out = run('split', str(cfg), str(tmp_path / 'times.json'), '--limit', '60')
    assert 'split %s' % big['name'] in out
    Q = json.loads((work / 'plan.json').read_text())
    assert len(Q['bundles']) > len(P['bundles'])
    assert json.loads((work / 'plan.pre_split.json').read_text()) == P
    assert 'plan OK' in run('check', str(cfg))


def test_notation_tokens_and_their_uses():
    # Hecke 7/8 stub ProbeEuler.pow_mul_sqrt: `variable (p : O)` outlived its `local notation "O"`
    assert C._notation_tokens('local notation "O" => ActualEisensteinCubic.O') == {'O'}
    assert C._notation_tokens('local infixl:65 " ∣_ " => f') == {'∣_'}
    assert C._uses_token('(p : O)', 'O') and C._uses_token('Ideal O', 'O')
    assert not C._uses_token('(p : Odd n)', 'O') and not C._uses_token('(x : A.O)', 'O')
    assert C._uses_token('a ∣_ b', '∣_')


def test_local_instance_names_go_after_the_keyword():
    # an anonymous `local instance` is named when carved, so an importer can re-activate it
    from types import SimpleNamespace as N

    def cmd(text):
        b = text.encode()
        return N(text_bytes=b), N(start=N(byte=0), end=N(byte=len(b)))
    i, c = cmd('noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _')
    assert C._local_instance(i, c) == (True, len('noncomputable local instance'))
    i, c = cmd('local instance (priority := 10) {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := x')
    assert C._local_instance(i, c) == (True, len('local instance (priority := 10)'))
    i, c = cmd('local instance foo : Bar := x')
    assert C._local_instance(i, c) == (True, None)
    i, c = cmd('instance : Bar := x')
    assert C._local_instance(i, c) == (False, None)


# ---------------------------------------------------------------- external definitions, statement suffix

@pytest.fixture(scope='module')
def ext_plan(g):
    # CD.double is provided by someone else's published bundle (Erdős 3: marwahaha's
    # Def_ErdosReciprocal defines the target's own definitions)
    return C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.005,
                       bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                       bundle_prefix='CDB', external_defs={'CD.double': 'Definitions.Def_Ext'},
                       statement_suffix='_s2', external=['CD.main'])


def test_external_definitions_stay_out_of_bundles_and_pieces(g, ext_plan):
    assert ext_plan['external_defs'] == {'CD.double': 'Definitions.Def_Ext'}
    assert all('CD.double' not in b['nodes'] for b in ext_plan['bundles'])
    assert all('CD.double' not in p['keep'] for p in ext_plan['pieces'].values())


def test_check_plan_counts_external_definitions_as_available(g, ext_plan):
    # StrongThinTree (2026-10-18): every bundle member and piece using one of the published
    # Def_StrongThinTree declarations was reported "needs …, which is in no bundle", so
    # `carve.py plan` refused a consistent plan. External definitions are available everywhere.
    assert C.check_plan(g, ext_plan) == []
    # without the external_defs entry the same plan is inconsistent, and the check says so
    bare = json.loads(json.dumps(ext_plan))
    bare['external_defs'] = {}
    probs = C.check_plan(g, bare)
    assert probs and all('CD.double' in p for p in probs)


def test_files_using_an_external_definition_import_its_bundle(g, ext_plan, tmp_path):
    C.generate(g, ext_plan, str(tmp_path))
    users = []
    for f in sorted((tmp_path / 'lib').iterdir()) + sorted((tmp_path / 'solutions').iterdir()):
        t = f.read_text()
        assert not re.search(r'^\s*(noncomputable\s+)?def\s+double\b', t, re.M), f.name
        if re.search(r'\bdouble\b', re.sub(r'^import .*$', '', t, flags=re.M)):
            users.append(f.name)
            assert 'import Definitions.Def_Ext\n' in t, f.name
    assert users


def test_stub_imports_only_external_definitions_its_statement_uses(ext_plan):
    # Petty projection (2026-10-18): the Mathlib-only statement brunnMinkowski_euclidean imported
    # the published Def_PettyProjectionVolume because its *proof* uses `Space`; a stub's proof is
    # `sorry`, so only what the statement needs (`sig`) decides its external imports, as it
    # already decides its bundle imports
    g2 = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)   # private copy: mutated
    assert 'CD.double' not in g2.nodes['CD.top_aux'].sig
    g2.nodes['CD.top_aux'].deps = g2.nodes['CD.top_aux'].deps | {'CD.double'}
    assert 'Def_Ext' not in C.gen_stub(g2, ext_plan, 'CD.top_aux')
    # a statement that does use the external definition still imports it
    assert 'CD.double' in g2.nodes['CD.double_succ'].sig
    assert 'import Definitions.Def_Ext\n' in C.gen_stub(g2, ext_plan, 'CD.double_succ')
    # a piece keeps its proof, so a proof-only use still imports it there
    assert 'import Definitions.Def_Ext\n' in C.gen_piece(g2, ext_plan, 'CD.top_aux')


def _cli():
    import importlib
    import sys
    sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'scripts'))
    return importlib.import_module('carve')


def test_external_theorems_are_imported_not_carved(g, tmp_path):
    # Petty projection (2026-10-18): the port's Brouwer step calls someone else's published
    # standalone AGT.brouwer_fixed_point (Theorems.Thm_AGT_brouwer_fixed_point). Config
    # `external_theorems` {name: Theorems module} works like external_defs: the theorem is never
    # carved or published again, counts as available, and the files using it import its module.
    # (CD.Aux.aux_eq stands in for the external theorem; DeclGraph reports such a theorem as a
    # node because carve.py passes its module with --also.)
    CLI = _cli()
    cfg = {'external_defs': {'CD.double': 'Definitions.Def_Ext'},
           'external_theorems': {'CD.Aux.aux_eq': 'Theorems.Thm_Ext'}}
    ext = CLI.external_map(cfg)
    assert ext == {'CD.double': 'Definitions.Def_Ext', 'CD.Aux.aux_eq': 'Theorems.Thm_Ext'}
    P = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.005,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    bundle_prefix='CDB', external_defs=ext, external=['CD.main'])
    assert 'CD.Aux.aux_eq' not in P['nodes']
    assert all('CD.Aux.aux_eq' not in b['nodes'] for b in P['bundles'])
    assert all('CD.Aux.aux_eq' not in p['keep'] for p in P['pieces'].values())
    assert 'CD.Aux.aux_eq' not in P['sorry']
    assert C.check_plan(g, P) == []
    piece = C.gen_piece(g, P, 'CD.top_aux')
    assert 'import Theorems.Thm_Ext\n' in piece
    assert not re.search(r'^\s*(theorem|lemma)\s+aux_eq\b', piece, re.M)
    # the graph step asks DeclGraph for the external theorems' modules too
    assert CLI.also_modules(cfg) == ['Theorems.Thm_Ext']


def test_decl_graph_command_passes_also_modules(monkeypatch, tmp_path):
    seen = {}

    class R:
        returncode = 0
        stdout = stderr = ''

    def run(cmd, **kw):
        seen['cmd'] = cmd
        return R()
    monkeypatch.setattr(C.subprocess, 'run', run)
    C.run_decl_graph(str(tmp_path / 'g.jsonl'), 'P', ['P.Main'], ws=str(tmp_path),
                     also=['Theorems.Thm_Ext'])
    cmd = seen['cmd']
    assert cmd[cmd.index('--run') + 1:] == [C.DECLGRAPH, '--also', 'Theorems.Thm_Ext',
                                             str(tmp_path / 'g.jsonl'), 'P', 'P.Main']


def test_statements_get_the_suffix_except_external_ones(g, ext_plan, tmp_path):
    assert C.statement_name(ext_plan, 'CD.top_aux') == 'CD.top_aux_s2'
    assert C.statement_name(ext_plan, 'CD.main') == 'CD.main'
    C.generate(g, ext_plan, str(tmp_path))
    stub = (tmp_path / 'lib' / 'Thm_CD_top_aux_s2.lean').read_text()
    assert re.search(r'^theorem top_aux_s2\b', stub, re.M)
    assert not (tmp_path / 'lib' / 'Thm_CD_main.lean').exists()      # external: not ours to publish
    piece = (tmp_path / 'solutions' / 'Sol_CD_top_aux_s2.lean').read_text()
    assert re.search(r'^theorem top_aux_s2_oai\b', piece, re.M)
    assert piece.rstrip().endswith('type_of% @CD.top_aux_s2_oai := @CD.top_aux_s2_oai')
    main = (tmp_path / 'solutions' / 'Sol_CD_main.lean').read_text()
    assert main.rstrip().endswith('type_of% @CD.main_oai := @CD.main_oai')
    for i in ext_plan['pieces']['CD.main']['imports']:
        s = C.statement_name(ext_plan, i)
        assert 'import Theorems.Thm_%s\n' % C.slug(s) in main
        short = i.rsplit('.', 1)[1]
        if re.search(r'\b%s\b' % short, main):
            assert re.search(r'\b%s_s2\b' % short, main)


def test_patches_apply_to_every_generated_file(g, plan, tmp_path):
    # proof fixes go in post-carve literal replacements, never in the port's source: the carver
    # cuts modules by the command ranges recorded when the port was compiled (Erdős 3, 2026-10-16)
    pat = [{'literal_old': 'theorem double_succ', 'literal_new': '-- patched\ntheorem double_succ'}]
    res = C.generate(g, plan, str(tmp_path), patches=pat)
    hit = [f for f in res['files'] if '-- patched\ntheorem double_succ' in open(f).read()]
    assert hit
    assert res['patches_unused'] == []
    res2 = C.generate(g, plan, str(tmp_path), patches=[{'literal_old': 'NO SUCH TEXT', 'literal_new': 'x'}])
    assert res2['patches_unused'] == ['NO SUCH TEXT']


# ---------------------------------------------------------------- the schedule chunker

def _bundle_depth(plan):
    pos = {b['name']: i for i, b in enumerate(plan['bundles'])}
    d = {}
    for b in plan['bundles']:
        assert all(pos[i] < pos[b['name']] for i in b['imports']), 'imports must come first'
        d[b['name']] = 1 + max([d[i] for i in b['imports']], default=0)
    return max(d.values())


@pytest.fixture(scope='module')
def sched_plan(g):
    return C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.01,
                       bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                       bundle_prefix='CDB', chunker='schedule')


def test_schedule_chunker_covers_bundle_material_once_and_fits(g, plan, sched_plan):
    allb = [k for b in sched_plan['bundles'] for k in b['nodes']]
    assert sorted(allb) == sorted(k for b in plan['bundles'] for k in b['nodes'])
    assert len(allb) == len(set(allb))
    cost = C.size_costs(g, bytes_per_second=10000)
    for b in sched_plan['bundles']:
        assert len(b['nodes']) == 1 or sum(cost[k] for k in b['nodes']) <= 0.01 + 1e-9
    C.check_plan(g, sched_plan)


def test_schedule_chunker_depth_is_the_longest_dependency_chain(g, sched_plan):
    # with every declaration about a full budget, the import depth can be no less than the longest
    # dependency chain of bundle material; list scheduling reaches it (here Space -> size -> size_eq).
    # (The band chunker keeps a module whole and so may exceed the budget instead.)
    B = {k for b in sched_plan['bundles'] for k in b['nodes']}
    ex = C.implicit_deps(g, B, B)          # silent simp lemmas order bundles too
    memo = {}

    def chain(k):
        if k not in memo:
            memo[k] = 1 + max([chain(d) for d in g.nodes[k].deps | ex.get(k, set()) if d in B and d != k], default=0)
        return memo[k]
    assert _bundle_depth(sched_plan) == max(chain(k) for k in B)


def test_repaired_declarations_need_their_patch(tmp_path):
    # the port stubbed a proof with sorry and a post-carve patch supplies it (Erdős 3 v2:
    # booleanSelectedDerivative_contDiff): mark it repaired, and generation refuses a file that
    # still contains sorry, so a patch that stops applying cannot slip a sorry through
    g2 = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
    C.mark_repaired(g2, ['CD.sorried'])
    p = C.make_plan(g2, ['CD.uses_sorry'], cost=C.size_costs(g2), bundle_prefix='X')
    assert p['sorry'] == [] and C.check_plan(g2, p) == []
    fix = [{'literal_old': 'theorem sorried : double 2 = 4 := sorry', 'literal_new': 'theorem sorried : double 2 = 4 := rfl'}]
    res = C.generate(g2, p, str(tmp_path), what=('bundles',), patches=fix)
    assert res['patches_unused'] == []
    with pytest.raises(C.CarveError, match='sorry'):
        C.generate(g2, p, str(tmp_path / 'nopatch'), what=('bundles',))


def test_schedule_chunker_keeps_silent_simp_lemmas_visible(g):
    # sizedZero's embedded `by simp` uses the rfl simp lemma Space.size_eq with no trace in the term:
    # list scheduling by recorded dependencies alone may put the lemma in a bundle the definition's
    # bundle does not import (Erdős 3 v2, 2026-10-16: six bundles failed "simp made no progress")
    p = C.make_plan(g, ['CD.uses_sized'], budget=0.05, piece_size=10**6, bundle_budget=0.0001,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    bundle_prefix='S', chunker='schedule')
    where = {k: b['name'] for b in p['bundles'] for k in b['nodes']}
    assert 'CD.sizedZero' in where and 'CD.Space.size_eq' in where
    imps = {b['name']: set(b['imports']) for b in p['bundles']}

    def closure(n, seen=None):
        seen = set() if seen is None else seen
        for i in imps[n]:
            if i not in seen:
                seen.add(i)
                closure(i, seen)
        return seen
    b = where['CD.sizedZero']
    assert where['CD.Space.size_eq'] == b or where['CD.Space.size_eq'] in closure(b)


def test_scoped_notation_scope_is_read_from_both_forms():
    # Mathlib `scoped[X] cmd` names X from the root; core `scoped notation` uses the current namespace
    assert C.scoped_scope('scoped[Indicator] notation3 "𝟭_[" s "]" => s', 'OAI', 'scopedNS') == 'Indicator'
    assert C.scoped_scope("scoped[Combinatorics.Additive'] notation3:max \"E[\" s \"]\" => s",
                          'OAI.Finset', 'scopedNS') == "Combinatorics.Additive'"
    assert C.scoped_scope('scoped notation "⟪" x "⟫" => f x', 'CDScope', 'notation') == 'CDScope'
    assert C.scoped_scope('/-- doc -/ scoped infixl:71 " ○ " => f', 'A.B', 'mixfix') == 'A.B'
    assert C.scoped_scope('local notation "AUX" => auxOnly', 'CD.Aux', 'notation') is None
    assert C.scoped_scope('notation "AUX" => auxOnly', 'CD.Aux', 'notation') is None


def _scoped_key(g):
    ks = [k for k, nd in g.nodes.items() if nd.kind == 'notation']
    assert len(ks) == 1, ks
    return ks[0]


def test_a_scoped_notation_is_a_node_its_openers_depend_on(g):
    # a scoped notation lives in exactly one bundle, and whatever opens its scope must see that
    # bundle: `open scoped X` fails with "unknown namespace" otherwise (Erdős 3 v2, 2026-10-16)
    k = _scoped_key(g)
    nd = g.nodes[k]
    assert nd.module == 'CarveDev.Base' and not nd.theorem and nd.names == []
    assert 'CD.double' in nd.deps
    assert k in g.nodes['CD.viaScoped'].deps
    assert k not in g.nodes['CD.sizedZero'].deps          # same module, not in the scope


def test_a_scoped_notation_is_emitted_in_exactly_one_bundle(g, tmp_path):
    p = C.make_plan(g, ['CD.uses_scoped'], budget=0.05, piece_size=10**6, bundle_budget=0.0001,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    bundle_prefix='N', chunker='schedule')
    k = _scoped_key(g)
    where = {n: b['name'] for b in p['bundles'] for n in b['nodes']}
    assert k in where and 'CD.viaScoped' in where
    C.generate(g, p, str(tmp_path), what=('bundles',))
    carriers = [f.name for f in (tmp_path / 'lib').iterdir() if '"⟪"' in f.read_text()]
    assert carriers == ['Def_%s.lean' % where[k]]
    imps = {b['name']: set(b['imports']) for b in p['bundles']}

    def closure(n, seen=None):
        seen = set() if seen is None else seen
        for i in imps[n]:
            if i not in seen:
                seen.add(i)
                closure(i, seen)
        return seen
    b = where['CD.viaScoped']
    assert where[k] == b or where[k] in closure(b)


def test_a_binder_using_a_field_of_another_variable_goes_with_its_declaration(g):
    # `variable (hS : S.big)`: field notation on the variable S names CD.Space.big; a file without
    # it must drop the group (Erdős 3 v2 B109/B170 "Invalid field `UnitIntervalValued`")
    out = C.Carver(g).carve({'CD.Space.field_free'}, g.have_names({'CD.Space.field_free', 'CD.Space'}),
                            sorry={'CD.Space.field_free'})
    assert 'S.big' not in out
    assert 'theorem field_free' in out


def test_an_unused_local_notation_keeps_no_variable_alive(g):
    out = C.Carver(g).carve({'CD.note_free'}, g.have_names({'CD.note_free'}), sorry={'CD.note_free'})
    assert '"WZ"' not in out
    assert 'Wide' not in out
    assert 'theorem note_free' in out


def test_a_used_local_notation_stays(g):
    # the existing fixture: `local notation "DE" => double_eq` used by double_succ's proof
    out = C.Carver(g).carve({'CD.double_succ'}, g.have_names(set(g.closure({'CD.double_succ'}))))
    if re.search(r'\bDE\b', out.split('local notation "DE"')[-1]):
        assert 'local notation "DE"' in out


def test_repaired_declarations_take_the_dependencies_of_their_patched_proofs():
    g2 = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
    assert g2.nodes['CD.sorried'].sorry
    C.mark_repaired(g2, {'CD.sorried': ['CD.double_eq']})
    nd = g2.nodes['CD.sorried']
    assert not nd.sorry and 'CD.double_eq' in nd.deps
    C.mark_repaired(g2, ['CD.sorried'])                      # the plain list form still works
    with pytest.raises(C.CarveError):
        C.mark_repaired(g2, {'CD.sorried': ['CD.nonexistent']})


def test_an_open_shadowed_by_a_project_namespace_elsewhere_is_rooted(g):
    # Base's `open Nat` meant Lean's Nat; CD.Nat exists in Mid. A statement is appended to its
    # solution by the verifier, after whatever namespaces the solution declares, so the open must
    # say which Nat it means wherever it lands
    out = C.Carver(g).carve({'CD.succ_pos_cd'}, g.have_names({'CD.succ_pos_cd'}), sorry={'CD.succ_pos_cd'})
    assert re.search(r'^open _root_\.Nat$', out, re.M), out


def test_measured_bundle_times_rescale_the_estimates_of_their_declarations():
    cost = {'a': 1.0, 'b': 3.0, 'c': 2.0, 'd': 5.0}
    bundles = [{'name': 'X0', 'nodes': ['a', 'b']}, {'name': 'X1', 'nodes': ['c']}, {'name': 'X2', 'nodes': ['d']}]
    times = {'X0': {'secs': 25.0, 'ok': True}, 'X1': {'secs': 4.0, 'ok': True},
             'X2': {'secs': 0, 'ok': False}}
    out = C.calibrate_costs(cost, bundles, times, scale=1.5, overhead=5.0)
    assert out['a'] + out['b'] == pytest.approx((25.0 - 5.0) * 1.5)
    assert out['a'] / out['b'] == pytest.approx(1 / 3)       # shares within a bundle kept
    assert out['c'] == pytest.approx(0.5 * 1.5)                # floor: never below 0.5 s local
    assert out['d'] == 5.0                                     # failed: estimate unchanged
    assert cost['a'] == 1.0                                    # input not mutated


def test_a_variable_with_nothing_kept_after_it_goes(g):
    out = C.Carver(g).carve({'CD.trail_kept'}, g.have_names({'CD.trail_kept'}))
    assert 'variable (q : Nat)' in out
    assert 'Inhabited Wide' not in out


def test_binders_are_not_dropped_by_guessing(g):
    # the carver no longer guesses from text whether a binder group is needed (a field read by its
    # short name, B065; project names in it that no kept declaration uses, B066): both guesses
    # dropped binders a declaration needed (B107, B167, B248). A group that does not elaborate is
    # cut by p2mlib.repair from Lean's error instead
    out = C.Carver(g).carve({'CD.Space.paren_free'}, g.have_names({'CD.Space.paren_free', 'CD.Space'}),
                            sorry={'CD.Space.paren_free'})
    assert '(F k).big' in out
    out = C.Carver(g).carve({'CD.unused_var_free'}, g.have_names({'CD.unused_var_free', 'CD.double'}))
    assert '(hq :' in out and '(hk :' in out


def test_a_variable_group_a_kept_declaration_uses_stays(g):
    have = g.have_names({'CD.uses_hk', 'CD.double'})
    out = C.Carver(g).carve({'CD.uses_hk'}, have, sorry={'CD.uses_hk'})
    assert 'variable (hk : double k0 = k0)' in out
    assert 'k0' in out


def test_a_field_of_a_local_does_not_count_as_a_project_constant_for_variable_use(g):
    have = g.have_names({'CD.uses_hk1'})
    out = C.Carver(g).carve({'CD.uses_hk1'}, have, sorry={'CD.uses_hk1'})
    assert '(hk1 : k1.succ = k1 + 1)' in out


def test_a_field_after_a_parenthesis_does_not_count_for_variable_use(g):
    # CD.pred is in the file (B167: VectorPolynomial.map was), so only the variable-use rule is
    # tested: with CD.pred absent the short-name field rule of B065 would drop the group, a
    # known false positive of reading fields by short name
    out = C.Carver(g).carve({'CD.uses_hk2'}, g.have_names({'CD.uses_hk2', 'CD.pred'}),
                            sorry={'CD.uses_hk2'})
    assert '(hk2 : (k1 + 1).pred = k1)' in out


def test_an_open_before_its_namespace_is_created_in_the_same_module_is_rooted(g):
    out = C.Carver(g).carve({'CD.natAbs_cd'}, g.have_names({'CD.natAbs_cd'}), sorry={'CD.natAbs_cd'})
    assert re.search(r'^open _root_\.Int$', out, re.M), out


def test_a_dotted_declaration_reads_its_body_in_its_own_namespace(g):
    assert 'CD.Space.size_eq' in g.nodes['CD.Space.cd_unused_simp'].deps


def test_a_named_local_instance_not_imported_is_emitted_again_under_a_unique_name(g):
    out = C.Carver(g).carve({'CD.uses_local_inst'}, g.have_names({'CD.uses_local_inst', 'CD.Wide'}),
                            sorry={'CD.uses_local_inst'})
    m = re.search(r'^local instance (cdLocalInst_r\w+) : Inhabited Wide', out, re.M)
    assert m, out
    assert not re.search(r'^local instance cdLocalInst :', out, re.M)


def test_split_bundles_cuts_only_the_slow_ones_and_keeps_the_rest(g):
    p = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=10.0,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    bundle_prefix='S', chunker='schedule')
    big = max(p['bundles'], key=lambda b: len(b['nodes']))
    assert len(big['nodes']) >= 2
    times = {b['name']: {'secs': 100.0 if b is big else 10.0, 'ok': True} for b in p['bundles']}
    cost = C.calibrate_costs(C.size_costs(g, bytes_per_second=10000), p['bundles'], times,
                             scale=1.5, overhead=5.0)
    q = C.split_bundles(g, p, [big['name']], cost, budget=90.0, bundle_prefix='S')
    old = {b['name']: b for b in p['bundles']}
    new = {b['name']: b for b in q['bundles']}
    for n, b in old.items():                       # the others: same declarations, same names
        if n != big['name']:
            assert new[n]['nodes'] == b['nodes']
    parts = [b for b in q['bundles'] if b['name'] not in old or b['name'] == big['name']]
    assert len(parts) >= 2 and big['name'] in new
    assert sorted(k for b in parts for k in b['nodes']) == sorted(big['nodes'])
    assert all(sum(cost[k] for k in b['nodes']) <= 90.0 * 1.15 for b in parts)
    assert C.check_plan(g, q) == []
    pos = {b['name']: i for i, b in enumerate(q['bundles'])}
    assert all(pos[i] < pos[b['name']] for b in q['bundles'] for i in b['imports'])


def test_a_local_instance_comes_back_before_a_variable_that_needs_it(g):
    out = C.Carver(g).carve({'CD.uses_hdef'}, g.have_names({'CD.uses_hdef', 'CD.Wide'}),
                            sorry={'CD.uses_hdef'})
    i = out.find('local instance cdLocalInst_r')
    j = out.find('variable (hdef')
    assert i >= 0 and j >= 0 and i < j, out


def test_dot_notation_uses_of_a_renamed_statement_are_renamed(g):
    have = g.have_names({'CD.uses_dot_thm', 'CD.Space.coord_eq', 'CD.Space.coord', 'CD.Space'})
    out = C.Carver(g).carve({'CD.uses_dot_thm'}, have, rename={'CD.Space.coord_eq': 'coord_eq_s2'})
    assert 'A.coord_eq_s2' in out and '(id A).coord_eq_s2' in out, out


def test_a_notation_used_by_a_re_emitted_local_instance_stays(g):
    out = C.Carver(g).carve({'CD.uses_hdef2'}, g.have_names({'CD.uses_hdef2', 'CD.Wide'}),
                            sorry={'CD.uses_hdef2'})
    i, j = out.find('local notation "WD"'), out.find('local instance cdLocalInst2_r')
    assert i >= 0 and j >= 0 and i < j, out


def test_an_open_reading_a_namespace_through_an_earlier_open_keeps_it(g):
    # Kaplansky 2026-10-18: `open _root_.SimpleGraph _root_.OAI.SimpleGraph Walk` in ReducedWalks
    # meant (also) SimpleGraph.Walk; carving away OAI.SimpleGraph.Walk dropped the token and the
    # bundle lost `length_eq_zero_iff`. Here `open _root_.List Perm` also opens List.Perm
    out = C.Carver(g).carve({'CD.perm_length_cd'}, g.have_names({'CD.perm_length_cd'}))
    m = re.search(r'^open _root_\.List (\S+)$', out, re.M)
    assert m and m.group(1) in ('Perm', '_root_.List.Perm'), out


def test_renaming_a_declaration_leaves_a_same_named_lean_declaration_alone(g):
    # Kaplansky 2026-10-18: renaming MultipleHNN.of_injective to of_injective_oai also renamed
    # Mathlib's HNNExtension.of_injective, read as dot notation on a local by its short name
    have = g.have_names({'CD.uses_core_succ', 'CD.Pkg.succ_le_succ'})
    out = C.Carver(g).carve({'CD.uses_core_succ'}, have, rename={'CD.Pkg.succ_le_succ': 'succ_le_succ_oai'})
    assert 'Nat.succ_le_succ h' in out and 'succ_le_succ_oai' not in out, out
