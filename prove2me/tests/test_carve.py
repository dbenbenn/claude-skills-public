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
    txt2 = carve(g, {'CD.double_zero', 'CD.double_eq'}, {'CD.double'})
    assert 'open List' in txt2 and '_root_.List' not in txt2


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
