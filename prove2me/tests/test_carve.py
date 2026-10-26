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


def test_dot_notation_reads_no_unrelated_project_declaration_by_short_name(g):
    # UniversalFInfinity (2026-10-18): `w.support` (Mathlib's Finsupp.support on a local) was read
    # as the project's Higman.RecognizingStack.support, and `Subtype.val` as a project structure's
    # field `val`. Dot notation `x.f` means `T.f` for the head T of x's type, so a short-name
    # reading in a project-only namespace T needs T among the declaration's constants.
    # `k1.succ` (k1 : Nat) is Nat.succ, not the project's Wide.succ:
    assert 'CD.Wide.succ' not in g.nodes['CD.uses_hk1'].deps
    # while `A.coord_eq` with A : Space still reads Space.coord_eq (Space is in the term)
    assert 'CD.Space.coord_eq' in g.nodes['CD.size_via_coord'].deps


def test_local_notation_names_are_dependencies_of_what_uses_the_notation(g):
    # `local notation "DE" => double_eq` in Mid: double_zero (`DE 0`) depends on double_eq; size_zero,
    # after it in its scope, never uses DE and does not (it did, by scope: a false import of the
    # double_eq statement into the CD.main piece; the import-edge check found it, 2026-10-24)
    assert 'CD.double_eq' in g.nodes['CD.double_zero'].deps
    assert 'CD.double_eq' not in g.nodes['CD.size_zero'].deps
    p = C.make_plan(g, ['CD.double_succ', 'CD.double_zero', 'CD.main'], forced=['CD.double_eq'],
                    cost=C.size_costs(g), bundle_prefix='DE')
    assert 'CD.double_eq' not in p['pieces']['CD.main']['imports']
    assert 'import Theorems.Thm_CD_double_eq' not in C.gen_piece(g, p, 'CD.main')
    # without Lean's record, a notation still counts for everything after it in its scope


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


def test_forced_theorem_a_definition_needs_is_a_clear_error_without_statement_imports(g):
    # StrictInverseFirstPower (2026-10-18): forcing Bieberbach's |a₂| ≤ 2, which the instance
    # `CompactSpace DiskFamily` needs, crashed make_plan with KeyError. `CD.double_eq` is a theorem
    # the definition `CD.doubleWitness` uses, so it is bundle material once `CD.uses_witness` is a target.
    # With bundles_import_statements off (the default is on) that stays a clear error.
    with pytest.raises(C.CarveError, match=r'CD\.double_eq.*bundle.*CD\.doubleWitness'):
        C.make_plan(g, ['CD.uses_witness'], forced=['CD.double_eq'], cost=C.size_costs(g),
                    bundles_import_statements=False)
    # a target pulled into a bundle the same way gets the same error
    with pytest.raises(C.CarveError, match=r'CD\.double_eq.*bundle'):
        C.make_plan(g, ['CD.uses_witness', 'CD.double_eq'], cost=C.size_costs(g),
                    bundles_import_statements=False)


def _stmt_plan(g, **kw):
    return C.make_plan(g, ['CD.uses_witness', 'CD.main', 'CD.uses_sized'], forced=['CD.double_eq'],
                       budget=0.05, piece_size=10**6, bundle_budget=1.0, bundle_size=10**6,
                       cost=C.size_costs(g, bytes_per_second=10000), bundle_prefix='S',
                       chunker='schedule', **kw)


def test_a_forced_theorem_definitions_need_is_published_and_their_bundles_import_it(g, tmp_path):
    # prove2.me's /submit-definition may import `Theorems.Thm_…` (a definition built by
    # Classical.choose from AGT.brouwer_fixed_point published, 2026-10-18), so a theorem that
    # definitions need need not be re-proved inside a bundle: forced, it is published as a
    # statement and the bundles that need it import that statement
    p = _stmt_plan(g)
    assert 'CD.double_eq' in p['nodes']
    assert all('CD.double_eq' not in b['nodes'] for b in p['bundles'])
    wit = next(b for b in p['bundles'] if 'CD.doubleWitness' in b['nodes'])
    assert wit['statements'] == ['CD.double_eq']
    assert C.check_plan(g, p) == []
    # the order: the statement's own bundles, the statement, its proof, then the bundles importing
    # it (a bundle may import a theorem only once it is Proved: "Imported platform theorems must be
    # Proved at submission time", 2026-10-18)
    order = C.publish_order(p)
    wave = {x: i for i, w in enumerate(order['waves']) for x in w}
    st, pc = 'statement:CD.double_eq', 'piece:CD.double_eq'
    assert wave[st] < wave[pc] < wave['bundle:' + wit['name']]
    for b in p['stubs']['CD.double_eq']['bundles'] + p['pieces']['CD.double_eq']['bundles']:
        assert wave['bundle:' + b] < wave[pc]
        assert 'CD.double_eq' not in next(x for x in p['bundles'] if x['name'] == b).get('statements', ())
    assert pc in order['deps']['bundle:' + wit['name']]
    out = tmp_path / 'out'
    C.generate(g, p, str(out))
    bundle = (out / 'lib' / ('Def_%s.lean' % wit['name'])).read_text()
    assert 'import Theorems.Thm_CD_double_eq\n' in bundle
    for f in (out / 'lib').glob('Def_*.lean'):
        assert not re.search(r'^theorem double_eq\b', f.read_text(), re.M), f.name
    assert re.search(r'^theorem double_eq_oai\b', (out / 'solutions' / 'Sol_CD_double_eq.lean').read_text(), re.M)


def test_a_piece_needing_a_bundle_that_imports_its_statement_is_made_self_contained(g, tmp_path):
    # ZeroTemperatureSK (2026-10-18): a forced statement's piece imported the bundle that imports
    # that statement; the bundle waits for the statement to be Proved, the proof waits for the
    # bundle, and publishing deadlocks. Here the piece of CD.double_eq is made to import the
    # bundle importing it (as an instance or attribute root can pull it in).
    p = json.loads(json.dumps(_stmt_plan(g)))
    wit = next(b for b in p['bundles'] if 'CD.doubleWitness' in b['nodes'])
    pc = p['pieces']['CD.double_eq']
    pc['bundles'] = [wit['name']]
    assert any('CD.double_eq' in x and 'cycle' in x for x in C.check_plan(g, p))
    with pytest.raises(C.CarveError, match='depends on itself'):
        C.publish_order(p)
    # the carver resolves it: the piece keeps what its proof needs and imports only bundles that
    # come before the statement (its stub's), never one importing it
    q = C.resolve_piece_cycles(g, p)
    assert q == ['CD.double_eq']
    pc = p['pieces']['CD.double_eq']
    assert pc['selfcontained'] and wit['name'] not in pc['bundles']
    assert C.check_plan(g, p) == []
    order = C.publish_order(p)
    wave = {x: i for i, w in enumerate(order['waves']) for x in w}
    assert wave['piece:CD.double_eq'] < wave['bundle:' + wit['name']]
    out = tmp_path / 'out'
    C.generate(g, p, str(out), what=('pieces',), names=['CD.double_eq'])
    sol = (out / 'solutions' / 'Sol_CD_double_eq.lean').read_text()
    assert 'Def_%s' % wit['name'] not in sol and re.search(r'^theorem double_eq_oai\b', sol, re.M)
    # make_plan never returns such a cycle
    assert C.resolve_piece_cycles(g, _stmt_plan(g)) == []


def test_an_external_attributed_declaration_is_never_kept_by_a_piece(g):
    # DiamondDistortion (2026-10-19): the published bundle's `@[reducible] def Edge` was an
    # external definition, yet the extra roots (instances and attributed declarations whose
    # dependencies are present) put the port's copy back into the piece: "already declared"
    p = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.005,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    bundle_prefix='CDB', external_defs={'CD.Space.size_eq': 'Definitions.Def_X'})
    assert not any('CD.Space.size_eq' in pc['keep'] for pc in p['pieces'].values())
    assert not any('CD.Space.size_eq' in b['nodes'] for b in p['bundles'])
    assert C.check_plan(g, p) == []


def test_split_keeps_the_statements_a_bundle_imports(g):
    p = _stmt_plan(g)
    wit = next(b for b in p['bundles'] if 'CD.doubleWitness' in b['nodes'])
    q = C.split_bundles(g, p, [wit['name']], C.size_costs(g, bytes_per_second=10000), 0.002)
    parts = [b for b in q['bundles'] if 'CD.doubleWitness' in b['nodes']]
    assert parts and parts[0].get('statements') == ['CD.double_eq']
    assert C.check_plan(g, q) == []


@pytest.mark.lean
def test_bundles_importing_a_statement_compile_and_show_its_sorry(g, tmp_path):
    # sorry-safe locally: a bundle member resting on the imported statement shows sorryAx, as a
    # piece importing a statement does
    p = _stmt_plan(g)
    _compile_in_publish_order(g, p, tmp_path)
    wit = next(b for b in p['bundles'] if 'CD.doubleWitness' in b['nodes'])
    chk = tmp_path / 'Axioms.lean'
    chk.write_text('import Definitions.Def_%s\n#print axioms CD.doubleWitness\n' % wit['name'])
    assert 'sorryAx' in C.compile_file(str(chk), None, str(tmp_path / 'olean'))


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


def _pinned_plan(g, pinned, targets=('CD.main', 'CD.size_zero')):
    return C.make_plan(g, list(targets), forced=['CD.size_zero'], budget=0.05, piece_size=10**6,
                       bundle_budget=1.0, bundle_size=10**6,
                       cost=C.size_costs(g, bytes_per_second=10000), bundle_prefix='P',
                       chunker='schedule', pinned=pinned)


def test_pinned_definitions_get_their_own_small_bundle_closed_under_dependencies(g):
    # UniversalFInfinity (2026-10-18): named statements (Higman, Whitehead, Milnor) should import a
    # few definitions, not the 850-declaration bundle the scheduler put them in; the split pinned
    # them by hand through `frozen`, and a missed dependency made an import cycle.
    p = _pinned_plan(g, {'space': ['CD.Space.size']})
    first = p['bundles'][0]
    # the pinned group is the first bundle, closed under dependencies (CD.Space came in itself)
    assert first['name'] == 'P000' and set(first['nodes']) == {'CD.Space', 'CD.Space.size'}
    assert first['imports'] == []
    assert C.check_plan(g, p) == []
    # a statement using only pinned definitions imports only the pinned bundle
    assert p['stubs']['CD.size_zero']['bundles'] == ['P000']
    # nothing pinned twice; later groups take what earlier ones left
    p2 = _pinned_plan(g, [['CD.Space'], ['CD.Space.size', 'CD.Space.coord']])
    assert p2['bundles'][0]['nodes'] == ['CD.Space']
    # Space.coord's module sees the rfl simp lemma Space.size_eq, which simp may use silently: the
    # closure takes implicit dependencies too
    assert set(p2['bundles'][1]['nodes']) == {'CD.Space.size', 'CD.Space.coord', 'CD.Space.size_eq'}
    assert p2['bundles'][1]['imports'] == ['P000']
    assert C.check_plan(g, p2) == []


def test_pinning_refuses_what_is_not_bundle_material(g):
    with pytest.raises(C.CarveError, match='CD.double_succ'):
        _pinned_plan(g, [['CD.double_succ']])
    with pytest.raises(C.CarveError, match='CD.nonexistent'):
        _pinned_plan(g, [['CD.nonexistent']])


def _local_inst_plan():
    # the named local instance cdLocalInst stays out of every bundle, so both the statement and its
    # solution emit it again; the solution keeps only the statement's own declaration
    t = 'CD.uses_local_inst'
    return t, {'bundles': [{'name': 'L0', 'nodes': ['CD.Wide', 'CD.Aux.auxOnly'], 'imports': []}],
               'nodes': [t], 'external_defs': {}, 'external': [],
               'stubs': {t: {'bundles': ['L0']}},
               'pieces': {t: {'keep': [t], 'imports': [], 'bundles': ['L0']}}}


def test_statement_and_solution_never_declare_the_same_local_instance(g):
    # UniversalFInfinity Milnor.contractible (2026-10-18): the statement and its solution kept the
    # same declarations, so both re-emitted `local instance …_r461751_1` under one name, and the
    # verifier's file (solution, then the statement) said "has already been declared"
    from p2mlib import localcheck as L
    t, plan = _local_inst_plan()
    stub, sol = C.gen_stub(g, plan, t), C.gen_piece(g, plan, t)
    pre = ''.join(l + '\n' for l in stub.split('\n') if l.startswith('import '))
    body = '\n'.join(l for l in stub.split('\n') if not l.startswith('import '))
    chk = L.server_check_text(sol, pre, body, t)
    names = re.findall(r'^\s*(?:@\[[^\]]*\]\s*)?local instance (?:\([^)]*\)\s*)?([^\s:({\[]+)', chk, re.M)
    assert names and len(names) == len(set(names)), names
    # and the statement still has its instance (its binders may need it)
    assert re.search(r'local instance cdLocalInst_r', stub)


@pytest.mark.lean
def test_statement_and_solution_compile_together_in_the_verifiers_form(g, tmp_path):
    from p2mlib import localcheck as L
    t, plan = _local_inst_plan()
    out = str(tmp_path / 'out')
    C.generate(g, plan, out)
    olean = str(tmp_path / 'olean')
    C.compile_file(os.path.join(out, 'lib', 'Def_L0.lean'), 'Definitions.Def_L0', olean)
    stub = open(os.path.join(out, 'lib', 'Thm_%s.lean' % C.slug(t))).read()
    C.compile_file(os.path.join(out, 'lib', 'Thm_%s.lean' % C.slug(t)), 'Theorems.Thm_' + C.slug(t), olean)
    sol = open(os.path.join(out, 'solutions', 'Sol_%s.lean' % C.slug(t))).read()
    pre = ''.join(l + '\n' for l in stub.split('\n') if l.startswith('import '))
    body = '\n'.join(l for l in stub.split('\n') if not l.startswith('import '))
    chk = tmp_path / 'Chk.lean'
    chk.write_text(L.server_check_text(sol, pre, body, t))
    C.compile_file(str(chk), None, olean)


def _kept_here_plan(g):
    return C.make_plan(g, ['CD.uses_keptHere'], budget=100, piece_size=10**6, bundle_budget=100,
                       bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                       bundle_prefix='N', chunker='schedule')


def test_a_local_notation_with_nothing_kept_after_it_goes_with_its_variable(g):
    # UniversalFInfinity B005 (2026-10-18): `local notation "hf" => (Fact.out : Function.Injective
    # f)` stayed for a local instance using it that was never emitted again, while `variable (f :
    # …)` went (nothing kept followed): "Unknown identifier `f` at quotation precheck". A local
    # notation with no kept declaration after it in its scope serves nothing, as a variable.
    p = _kept_here_plan(g)
    txt = C.gen_bundle(g, p, p['bundles'][0]['name'])
    assert 'def keptHere' in txt
    assert '"XW"' not in txt and 'variable (x : Wide)' not in txt


@pytest.mark.lean
def test_a_dropped_variables_notation_does_not_break_the_bundle(g, tmp_path):
    _compile_in_publish_order(g, _kept_here_plan(g), tmp_path)


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


@pytest.mark.lean
def test_pinned_bundles_compile(g, tmp_path):
    # a pinned bundle carries everything its members need: it compiles on its own, first
    _compile_in_publish_order(g, _pinned_plan(g, [['CD.Space'], ['CD.Space.size', 'CD.Space.coord']]), tmp_path)


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
                # the verifier's check (p2mlib.localcheck): the solution, then the published
                # statement in the same file, then `theorem _check : type_of% @T := @solution`
                from p2mlib import localcheck
                stub = open(os.path.join(out, 'lib', 'Thm_%s.lean' % C.slug(name)), encoding='utf-8').read()
                sol = open(os.path.join(out, 'solutions', 'Sol_%s.lean' % C.slug(name)), encoding='utf-8').read()
                pre = ''.join(l + '\n' for l in stub.split('\n') if l.startswith('import '))
                stmt = '\n'.join(l for l in stub.split('\n') if not l.startswith('import '))
                chk = tmp_path / ('Chk_%s.lean' % C.slug(name))
                chk.write_text(localcheck.server_check_text(sol, pre, stmt, name))
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


def test_command_line_pinned(tmp_path):
    import shutil
    import subprocess
    import sys
    work = tmp_path / 'work'
    work.mkdir()
    shutil.copy(os.path.join(FIX, 'decl_graph.jsonl'), work / 'decl_graph.jsonl')
    cfg = tmp_path / 'carve.json'
    cfg.write_text(json.dumps({'src': FIX, 'prefix': 'CarveDev', 'roots': ['CarveDev.Top'],
                               'targets': ['CD.main'], 'forced': ['CD.size_zero'],
                               'external': ['CD.main'], 'work': str(work), 'out': str(tmp_path / 'out'),
                               'bundle_prefix': 'CDP', 'budget': 0.05, 'bundle_budget': 1.0,
                               'bytes_per_second': 10000, 'chunker': 'schedule',
                               'pinned': {'space': ['CD.Space.size']}}))
    script = os.path.join(os.path.dirname(HERE), 'scripts', 'carve.py')
    r = subprocess.run([sys.executable, script, 'plan', str(cfg)], capture_output=True, text=True)
    assert r.returncode == 0 and 'PROBLEM' not in r.stdout, r.stdout + r.stderr
    P = json.loads((work / 'plan.json').read_text())
    assert set(P['bundles'][0]['nodes']) == {'CD.Space', 'CD.Space.size'}
    assert P['stubs']['CD.size_zero']['bundles'] == ['CDP000']


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


def test_external_theorem_modules_do_not_leak_their_imports():
    # CrouzeixHilbert (2026-10-19): with external_theorems, DeclGraph reports the Theorems module
    # as a project module (--also), so ext_imports walked into it and every carved file importing
    # a module that imports it got the theorem's own Definitions bundle
    # (Def_MilnorDynamics_NormalFamilies), even the Mathlib-only statements. An external theorem's
    # module is imported only where the theorem is used (the external map), with its own imports.
    g2 = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)   # private copy: mutated
    m = sorted(g2.infos)[0]
    g2.infos['Theorems.Thm_X'] = g2.infos[m]
    g2.imports['Theorems.Thm_X'] = ['Mathlib', 'Definitions.Def_Other']
    g2.imports[m] = list(g2.imports.get(m, [])) + ['Theorems.Thm_X']
    out = g2.ext_imports([m])
    assert 'Definitions.Def_Other' not in out
    assert 'Theorems.Thm_X' not in out


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


# ---------------------------------------------------------------- extending a published carve

def _carve_cli(tmp_path, name, **extra):
    """A carve config of the fixture under tmp_path/name, and a runner of carve.py on it."""
    import shutil
    import subprocess
    import sys
    work = tmp_path / name / 'work'
    work.mkdir(parents=True)
    shutil.copy(os.path.join(FIX, 'decl_graph.jsonl'), work / 'decl_graph.jsonl')
    cfg = tmp_path / name / 'carve.json'
    cfg.write_text(json.dumps(dict({
        'src': FIX, 'prefix': 'CarveDev', 'roots': ['CarveDev.Top'], 'targets': TARGETS,
        'external': ['CD.main'], 'work': str(work), 'out': str(tmp_path / name / 'out'),
        'bundle_prefix': 'CDB', 'budget': 0.05, 'bundle_budget': 0.005, 'bytes_per_second': 10000},
        **extra)))
    script = os.path.join(os.path.dirname(HERE), 'scripts', 'carve.py')

    def run(*a, ok=True):
        r = subprocess.run([sys.executable, script] + list(a), capture_output=True, text=True,
                           env=dict(os.environ, P2M_WORKSPACE=str(tmp_path / 'ws')))
        assert (r.returncode == 0) == ok, r.stdout + r.stderr
        return r.stdout + r.stderr
    (tmp_path / 'ws').mkdir(exist_ok=True)
    return cfg, work, tmp_path / name / 'out', run


def test_gen_applies_recorded_repairs(tmp_path):
    # carve_measure cuts a failing context command and records the cut in work/repairs.json;
    # Boone-Higman (2026-10-24): a later `carve.py gen` rewrote the bundle without the cut, so the
    # regenerated file differed from the one measured and published
    cfg, work, out, run = _carve_cli(tmp_path, 'a')
    run('plan', str(cfg))
    run('gen', str(cfg))
    assert 'open _root_.List\n' in (out / 'lib' / 'Def_CDB002.lean').read_text()
    (work / 'repairs.json').write_text(json.dumps({'Def_CDB002.lean': ['open _root_.List']}))
    run('gen', str(cfg))
    assert 'open _root_.List' not in (out / 'lib' / 'Def_CDB002.lean').read_text()
    # a recorded cut that no longer matches is reported, not silently dropped
    (work / 'repairs.json').write_text(json.dumps({'Def_CDB002.lean': ['open NoSuch']}))
    assert 'STALE REPAIR Def_CDB002.lean' in run('gen', str(cfg))


def test_gen_takes_frozen_bundles_verbatim_from_the_published_copy(tmp_path):
    # Extending a published carve (Boone-Higman option (c), 2026-10-24): a second carve with the
    # first carve's bundles `frozen` regenerated them from the graph, without the first carve's
    # measure-time repair, and the agent copied the published files over by hand. A published
    # bundle is frozen: gen writes exactly its published text.
    cfg, work, out, run = _carve_cli(tmp_path, 'first')
    run('plan', str(cfg))
    run('gen', str(cfg))
    pub = tmp_path / 'published'
    pub.mkdir()
    for b in ('CDB000', 'CDB002'):
        txt = (out / 'lib' / ('Def_%s.lean' % b)).read_text()
        if b == 'CDB002':                                   # the first carve's repair
            from p2mlib import repair as RP
            txt = RP.apply_cuts(txt, ['open _root_.List'])[0]
            assert 'open _root_.List' not in txt
        (pub / ('Def_%s.lean' % b)).write_text(txt)
    frozen = {'plan': str(work / 'plan.json'), 'bundles': ['CDB000', 'CDB002']}
    cfg2, work2, out2, run2 = _carve_cli(tmp_path, 'second', frozen=dict(frozen, lib=str(pub)))
    run2('plan', str(cfg2))
    run2('gen', str(cfg2))
    for b in ('CDB000', 'CDB002'):
        assert (out2 / 'lib' / ('Def_%s.lean' % b)).read_bytes() == (pub / ('Def_%s.lean' % b)).read_bytes()
    # the published copy may also come from the workspace (fetch_theorems.py writes it there);
    # the first carve's repairs, named by `frozen.repairs`, make the regenerated text agree
    (work / 'repairs.json').write_text(json.dumps({'Def_CDB002.lean': ['open _root_.List']}))
    cfg3, work3, out3, run3 = _carve_cli(tmp_path, 'third', frozen=dict(
        frozen, repairs=str(work / 'repairs.json')))
    (tmp_path / 'ws' / 'Definitions').mkdir()
    for b in ('CDB000', 'CDB002'):
        (tmp_path / 'ws' / 'Definitions' / ('Def_%s.lean' % b)).write_bytes((pub / ('Def_%s.lean' % b)).read_bytes())
    run3('plan', str(cfg3))
    assert 'differs' not in run3('gen', str(cfg3))
    assert (out3 / 'lib' / 'Def_CDB002.lean').read_bytes() == (pub / 'Def_CDB002.lean').read_bytes()
    # a frozen bundle the generator would now write differently is reported (the copy still wins)
    (tmp_path / 'ws' / 'Definitions' / 'Def_CDB002.lean').write_text(
        (pub / 'Def_CDB002.lean').read_text() + '-- published later\n')
    msg = run3('gen', str(cfg3))
    assert 'Def_CDB002' in msg and 'differs' in msg
    assert (out3 / 'lib' / 'Def_CDB002.lean').read_text().endswith('-- published later\n')


def test_gen_refuses_a_frozen_bundle_without_a_published_copy(tmp_path):
    cfg, work, out, run = _carve_cli(tmp_path, 'first')
    run('plan', str(cfg))
    cfg2, _, out2, run2 = _carve_cli(tmp_path, 'second', frozen={
        'plan': str(work / 'plan.json'), 'bundles': ['CDB000']})
    run2('plan', str(cfg2))
    msg = run2('gen', str(cfg2), ok=False)
    assert 'CDB000' in msg and 'fetch_theorems.py' in msg
    assert not (out2 / 'lib' / 'Def_CDB000.lean').exists()


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


def test_a_bundle_waits_for_every_piece_its_statements_rest_on():
    # Eilenberg–Ganea (2026-10-25): bundle OAIEGC001 imports the statement d1_basis_cert, whose
    # piece imports eleven block statements; the piece came back SKETCH_ACCEPTED, the statement
    # stayed Open until the blocks were proved, and the bundle was refused ("Imported platform
    # theorems must be Proved at submission time"). The bundle waits for the whole closure.
    plan = {'bundles': [{'name': 'B0', 'nodes': [], 'imports': []},
                        {'name': 'B1', 'nodes': [], 'imports': ['B0'], 'statements': ['S']}],
            'nodes': ['S', 'T', 'U', 'X'],
            'stubs': {'S': {'bundles': ['B0']}, 'T': {'bundles': ['B0']}, 'U': {'bundles': ['B0']},
                      'X': {'bundles': ['B0']}},
            'pieces': {'S': {'bundles': ['B0'], 'imports': ['T', 'E']},
                       'T': {'bundles': ['B0'], 'imports': ['U']},
                       'U': {'bundles': ['B0'], 'imports': []},
                       'X': {'bundles': ['B0'], 'imports': []}},
            'external': ['E']}
    deps = C.publish_order(plan, external=['E'])['deps']['bundle:B1']
    assert {'piece:S', 'piece:T', 'piece:U'} <= set(deps)
    assert 'piece:X' not in deps and 'piece:E' not in deps


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


def test_measured_times_keyed_as_carve_measure_writes_them():
    # carve_measure.py keys work/times.json by publish item (`bundle:OAIEG012`); calibrate_costs and
    # `carve.py split` looked bundles up by bare name, so Eilenberg–Ganea's 284 s bundle was never
    # split ("26 bundles -> 26", 2026-10-25)
    cost = {'a': 1.0, 'b': 3.0}
    bundles = [{'name': 'X0', 'nodes': ['a', 'b']}]
    out = C.calibrate_costs(cost, bundles, {'bundle:X0': {'secs': 25.0, 'ok': True}})
    assert out['a'] + out['b'] == pytest.approx((25.0 - 5.0) * 1.5)
    assert C.bundle_time({'bundle:X0': {'secs': 25.0, 'ok': True}}, 'X0')['secs'] == 25.0
    assert C.bundle_time({'X0': {'secs': 7.0, 'ok': True}}, 'X0')['secs'] == 7.0
    assert C.bundle_time({'piece:X0': {'secs': 7.0, 'ok': True}}, 'X0') is None
    assert C.slow_bundles(bundles + [{'name': 'X1', 'nodes': []}],
                          {'bundle:X0': {'secs': 61.0, 'ok': True},
                           'bundle:X1': {'secs': 99.0, 'ok': False}}, 60.0) == ['X0']


def test_a_variable_with_nothing_kept_after_it_goes(g):
    out = C.Carver(g).carve({'CD.trail_kept'}, g.have_names({'CD.trail_kept'}))
    assert 'variable (q : Nat)' in out
    assert 'Inhabited Wide' not in out


def test_binders_are_not_dropped_by_guessing(g):
    # the carver never guesses from text whether a binder group is needed (a field read by its
    # short name, B065; project names in it that no kept declaration uses, B066): both guesses
    # dropped binders a declaration needed (B107, B167, B248). It reads what Lean resolved: in
    # `(hF : ∀ k, (F k).big)` the field is CD.Space.big, which this file lacks, so the group goes
    # (the text alone could not tell, and the group was left for p2mlib.repair to cut)
    out = C.Carver(g).carve({'CD.Space.paren_free'}, g.have_names({'CD.Space.paren_free', 'CD.Space'}),
                            sorry={'CD.Space.paren_free'})
    assert '(F k).big' not in out and 'theorem paren_free' in out
    out = C.Carver(g).carve({'CD.Space.paren_free'},
                            g.have_names({'CD.Space.paren_free', 'CD.Space', 'CD.Space.big'}),
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


def test_a_local_instance_in_scope_that_nothing_kept_uses_stays_out(g):
    # every local instance in scope used to come back; Lean's record says no_inst_use never used
    # cdLocalInst, while uses_local_inst's statement did (`default : Wide`, instance search)
    out = C.Carver(g).carve({'CD.no_inst_use'}, g.have_names({'CD.no_inst_use', 'CD.Wide'}))
    assert 'theorem no_inst_use' in out and not re.search(r'^local instance', out, re.M), out
    out = C.Carver(g).carve({'CD.no_inst_use', 'CD.uses_local_inst'},
                            g.have_names({'CD.no_inst_use', 'CD.uses_local_inst', 'CD.Wide'}))
    assert out.count('local instance cdLocalInst_r') == 1
    assert out.index('local instance cdLocalInst_r') < out.index('theorem uses_local_inst')
    assert 'CD.cdLocalInst' in g.nodes['CD.uses_local_inst'].sig


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


# ---------------------------------------------------------------- fields and same-short-name names
# (CarveDev/Fields.lean; the three carver bugs of 2026-10-23's plain carves)

def test_a_field_token_is_not_read_as_a_namespace_constant(g):
    # PosteriorReplicas: `(E.rules ω).fixed_quadratic_memory` gave a false import of the theorem
    # OAI.PosteriorRegression.fixed_quadratic_memory. Here `(o.inner 0).fqm` is Inner.fqm, not CD.fqm
    deps = g.nodes['CD.Outer.fqm'].deps
    assert 'CD.Inner.fqm' in deps and 'CD.fqm' not in deps
    # `(k1 + 1).pred` is Nat.pred, not the project's CD.pred
    assert 'CD.pred' not in g.nodes['CD.uses_hk2'].deps


def test_dot_notation_needs_the_constant_or_its_type_in_the_term_even_in_a_shared_namespace(g):
    # PosteriorReplicas: a project namespace that is also a namespace of a published external
    # bundle (ext_ns) let a short-name reading through without the compiled-constant check
    g2 = C.Graph(g.consts, g.imports, set(g.ext_ns) | {'CD'}, g.infos)
    deps = g2.nodes['CD.outer_dot'].deps
    assert 'CD.Outer.fqm' in deps and 'CD.fqm' not in deps
    # genuine dot-notation dependencies stay
    assert 'CD.Outer.cp' in g2.nodes['CD.uses_outer_cp'].deps
    assert 'CD.Space.coord_eq' in g2.nodes['CD.size_via_coord'].deps


def test_renaming_leaves_a_namespaced_reference_to_another_declaration_alone(g):
    # Problem355: renaming AuxiliaryZeroCount.weighted_count_le_log also renamed the reference
    # `ZeroGlobalCount.weighted_count_le_log` inside it (the head is a namespace, not a local)
    have = g.have_names({'CD.AZ.wcl', 'CD.ZG.wcl'})
    out = C.Carver(g).carve({'CD.AZ.wcl'}, have, rename={'CD.AZ.wcl': 'wcl_oai'})
    assert 'theorem wcl_oai' in out and 'apply ZG.wcl\n' in out, out


def test_renaming_leaves_a_same_short_name_definition_in_the_statement_alone(g):
    # PermanentBorder: renaming HasBorderDeterminant.coefficientPolynomial also renamed the
    # definition `coefficientPolynomial` in its own statement, where Lean cannot read the
    # declaration being declared
    have = g.have_names({'CD.Outer.cp', 'CD.cp', 'CD.Outer', 'CD.Inner'})
    out = C.Carver(g).carve({'CD.Outer.cp'}, have, rename={'CD.Outer.cp': 'cp_oai'})
    assert 'theorem Outer.cp_oai' in out and ': cp (o.inner 0).val' in out, out
    # a genuine dot-notation use of the renamed declaration is still renamed
    have = g.have_names({'CD.uses_outer_cp', 'CD.Outer.cp', 'CD.cp', 'CD.Outer', 'CD.Inner'})
    out = C.Carver(g).carve({'CD.uses_outer_cp'}, have, rename={'CD.Outer.cp': 'cp_oai'})
    assert ':= o.cp_oai' in out and 'cp (o.inner 0).val = ' in out, out


def test_generate_refuses_a_file_the_soundness_guard_would_refuse(g, plan, tmp_path):
    # WLTime (2026-10-23): a bundle kept OpenAI's `def prelude`; the platform's soundness guard
    # refuses the token `prelude` even as an identifier, found only on publishing (compile_error)
    pt = [{'literal_old': 'def double (n : Nat)', 'literal_new': 'def prelude (n : Nat) : Nat := n\ndef double (n : Nat)'}]
    with pytest.raises(C.CarveError, match='prelude'):
        C.generate(g, plan, str(tmp_path / 'out'), patches=pt)


# ---------------------------------------------------------------- exports and instances across modules

def _section(txt, module):
    """The text of one module's section in a carved file."""
    i = txt.index('-- module %s\n' % module)
    j = txt.find('\nsection\n-- module ', i)
    return txt[i:j if j >= 0 else len(txt)]


def _propc_plan(g):
    return C.make_plan(g, ['CD.LI.uses_propc_a', 'CD.LI.uses_propc_b', 'CD.LI.uses_propc_sig',
                           'CD.LI.uses_propc_sig_b'], budget=100, bundle_budget=100,
                       cost=C.size_costs(g), bundle_prefix='Q', chunker='schedule')


def test_an_anonymous_local_instance_whose_name_another_module_took_comes_back(g):
    # Problem340 (2026-10-24): sibling modules each declared `local instance : Fact ((0 : ℝ) < 100)`;
    # an instance of a Prop class is a theorem, Lean lets two modules declare the same one, and
    # both got one generated name. The declaration graph keeps one constant per name, so the other
    # module's command was nobody's node and never came back for its declarations: the pieces
    # failed (a global instance was patched in by hand).
    assert 'CD.LI.instPropCOfNatNat' in g.nodes          # InstA's; InstB's command has no node
    p = _propc_plan(g)
    for n, mod in (('CD.LI.uses_propc_a', 'CarveDev.InstA'), ('CD.LI.uses_propc_b', 'CarveDev.InstB'),
                   ('CD.LI.uses_propc_sig', 'CarveDev.InstA'), ('CD.LI.uses_propc_sig_b', 'CarveDev.InstB')):
        piece, stub = C.gen_piece(g, p, n), C.gen_stub(g, p, n)
        # a statement stub carries the instance only when its statement needs it (`needsPropC 3`:
        # instance search, no name in the text); `PropC 3 := inferInstance` needs it in its proof only
        texts = [(piece, _section(piece, mod))] + ([(stub, stub)] if '_sig' in n else [])
        # in force again: its command re-emitted, or (InstA's, which a bundle carries for the
        # statements needing it) re-activated from the bundle
        for txt, sec in texts:
            m = re.search(r'^(local instance \S+ : PropC 3|attribute \[local instance\] \S*instPropC)', sec, re.M)
            assert m, txt
            assert m.start() < sec.index('theorem uses_propc')
        if '_sig' not in n:
            assert 'local instance' not in stub, stub


@pytest.mark.lean
def test_local_instances_sharing_a_name_compile(g, tmp_path):
    _compile_in_publish_order(g, _propc_plan(g), tmp_path)


def _export_plan():
    t = 'CD.Ex.word_len'
    return {'bundles': [{'name': 'E0', 'nodes': ['CD.Ex.Word', 'CD.Ex.Word.len'], 'imports': []},
                        {'name': 'E1', 'nodes': ['CD.Ex.Coding', 'CD.Ex.instCodingNat'], 'imports': []}],
            'nodes': [t], 'external_defs': {}, 'external': [],
            'stubs': {t: {'bundles': ['E0']}},
            'pieces': {t: {'keep': [t], 'imports': [], 'bundles': ['E0']}}}


def test_an_export_goes_where_its_namespace_exists(g):
    # RationalHitting (2026-10-24): `export Coding (code)` stayed in bundle OAIQWRHT000 with the rest
    # of its namespace block, but the class Coding was in OAIQWRHT001, which 000 does not import:
    # "unknown namespace `Coding`". An export, like an open, needs its namespace in the file.
    p = _export_plan()
    assert C.check_plan(g, p) == []
    e0, e1 = C.gen_bundle(g, p, 'E0'), C.gen_bundle(g, p, 'E1')
    assert not re.search(r'^export', e0, re.M) and 'structure Word' in e0
    assert re.search(r'^export Coding \(code\)$', e1, re.M)
    for txt in (C.gen_stub(g, p, 'CD.Ex.word_len'), C.gen_piece(g, p, 'CD.Ex.word_len')):
        assert not re.search(r'^export', txt, re.M)


@pytest.mark.lean
def test_exports_compile(g, tmp_path):
    _compile_in_publish_order(g, _export_plan(), tmp_path)


def test_an_instance_a_module_never_saw_is_hidden_again(g):
    # RationalHitting (2026-10-24): the instance witnessCharZero (Generator.lean) reached the carved
    # list_hits piece's Certificates.lean declarations through a bundle; `algebraMap ℚ` elaborated
    # through it there, and a `rwa [RingHom.ext_rat …]` no longer matched (a post-carve patch).
    # Here box_default (InstBase) is `rfl` only with boxInhabitedA: InstLate's later boxInhabited,
    # in the same bundle, would win. The module's section hides it: `attribute [-instance]`.
    p = _leak_plan()
    for txt in (C.gen_piece(g, p, 'CD.LI.box_default'), C.gen_stub(g, p, 'CD.LI.box_default')):
        sec = _section(txt, 'CarveDev.InstBase') if '-- module' in txt else txt
        m = re.search(r'^attribute \[-instance\] (.*)$', sec, re.M)
        assert m and '_root_.CD.LI.boxInhabited' in m.group(1).split(), txt
        assert '_root_.CD.LI.boxInhabitedA' not in m.group(1).split()
    # an instance of the declaration's own module, declared after it, cannot be hidden: reported
    leaks = C.instance_leaks(g, p)
    assert ('piece:CD.LI.late_default', 'CD.LI.late_default', 'CD.LI.boxInhabited') in leaks
    assert not [x for x in leaks if x[1] != 'CD.LI.late_default']
    assert not C._global_instance(g, 'CD.LI.instPropCOfNatNat')
    assert C.leak_summary(leaks) == ['CD.LI.boxInhabited: 1 declaration in 2 files '
                                     '(piece:CD.LI.late_default, statement:CD.LI.late_default)']
    # the filter: InstLate's box-free declarations, or one whose problems no Inhabited answers,
    # are not reported even when later instances show
    p['bundles'][0]['nodes'].remove('CD.LI.boxInhabited')
    assert C.instance_leaks(g, p) == []


def test_only_external_instances_the_file_imports_are_hidden(g):
    # Eilenberg–Ganea (2026-10-24): every bundle, statement and piece hid the StdSimplex shim's
    # instances (`attribute [-instance] _root_.Convexity.StdSimplex.instInhabited …`), external
    # definitions of Def_OAIStdSimplexCompat, which most files do not import: "Unknown constant".
    # A file's names are its imports' names, external definitions included only through the
    # external bundles it (or a bundle or statement it imports) actually imports.
    p = _leak_plan()
    for k in ('CD.LI.boxInhabited', 'CD.LI.defaultBox'):     # defaultBox uses boxInhabited
        p['bundles'][0]['nodes'].remove(k)
    p['external_defs'] = {'CD.LI.boxInhabited': 'Definitions.Def_Other'}
    for txt in (C.gen_piece(g, p, 'CD.LI.box_default'), C.gen_stub(g, p, 'CD.LI.box_default'),
                C.gen_bundle(g, p, 'L0')):
        assert 'Def_Other' not in txt, txt
        assert not re.search(r'^attribute \[-instance\].*boxInhabited(?!A)', txt, re.M), txt
    # imported (here: every bundle declaration is external, in the one external bundle), it is
    # visible and hidden again as before
    q = _leak_plan()
    q['external_defs'] = {k: 'Definitions.Def_Ext' for k in q['bundles'][0]['nodes']}
    q['bundles'] = []
    for k in q['stubs']:
        q['stubs'][k]['bundles'] = []
        q['pieces'][k]['bundles'] = []
    txt = C.gen_piece(g, q, 'CD.LI.box_default')
    assert 'import Definitions.Def_Ext' in txt
    m = re.search(r'^attribute \[-instance\] (.*)$', txt, re.M)
    assert m and '_root_.CD.LI.boxInhabited' in m.group(1).split(), txt


def _leak_plan():
    ts = ['CD.LI.box_default', 'CD.LI.box_get', 'CD.LI.box_default_local', 'CD.LI.late_default']
    return {'bundles': [{'name': 'L0', 'nodes': ['CD.LI.Box', 'CD.LI.Box.get', 'CD.LI.boxInhabited',
                                                 'CD.LI.boxInhabitedA', 'CD.LI.defaultBox'], 'imports': []}],
            'nodes': ts, 'external_defs': {}, 'external': [],
            'stubs': {x: {'bundles': ['L0']} for x in ts},
            'pieces': {x: {'keep': [x], 'imports': [], 'bundles': ['L0']} for x in ts}}


@pytest.mark.lean
def test_hidden_instances_compile(g, tmp_path):
    p = _leak_plan()
    for t in ('CD.LI.late_default',):            # the unhidable leak: its rfl fails
        p['nodes'].remove(t)
        del p['stubs'][t], p['pieces'][t]
    _compile_in_publish_order(g, p, tmp_path)


def test_names_declared_or_naming_a_case_are_never_written_in_full(g):
    # RationalHitting (2026-10-24): the constructor `| transfer (a b : K) …` of `Eval`, whose name
    # is also a definition in the file, was pinned to `| _root_.….Eval.transfer` (a constructor name
    # is a binder: Lean records it, but it is no reference). PermanentBorder: `| zero =>` of
    # `induction … with` was pinned to `| _root_.Nat.zero` ("Invalid alternative name")
    out = C.Carver(g).carve({'CD.Step'}, g.have_names({'CD.Step', 'CD.transfer'}))
    assert '  | transfer (n : Nat) : Step n (transfer n)' in out, out
    have = g.have_names({'CD.Tree.size_pos', 'CD.Tree', 'CD.Tree.size', 'CD.Other.leaf'})
    out = C.Carver(g).carve({'CD.Tree.size_pos'}, have)
    assert '  | leaf => exact Nat.one_pos' in out, out
    # `| @leaf =>` too (RationalHitting list_hits: `| @_root_.….Formula.Eval.inv h a … =>`)
    out = C.Carver(g).carve({"CD.Tree.size_pos'"}, have | {'CD.Tree.size_pos'})
    assert '  | @leaf => exact Nat.one_pos' in out, out
    # the case name is Lean's CD.Tree.leaf, the opened CD.Other.leaf would be the text's reading
    c = g.infos['CarveDev.Fields'].commands[g.nodes['CD.Tree.size_pos'].cmd]
    leaf = next(i for i in c.idents if i['name'] == 'leaf')
    assert C._alternative_name(g.infos['CarveDev.Fields'], leaf)


@pytest.fixture(scope='module')
def g_text():
    """The fixture graph with Lean's records removed: every identifier read from text, as for a
    module the elaborated port has no record of (the fallback)."""
    g2 = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
    for info in g2.infos.values():
        for c in info.commands:
            c.resolved = c.insts = c.sig_insts = c.inst_keys = c.declares = None
            c.declares_kinds = c.kinds_used = c.used_keys = c.sig_used_keys = None
    return C.Graph(g2.consts, g2.imports, g2.ext_ns, g2.infos)


def test_the_text_reading_remains_the_logged_fallback(g, g_text):
    # with records nothing is read from text in the fixture
    assert g.fallbacks == []
    # without them, the text rules of 2026-10-16..23 still decide, and each guess is logged
    assert 'CD.Space.coord_eq' in g_text.nodes['CD.size_via_coord'].deps          # B024
    assert 'CD.Wide.succ' not in g_text.nodes['CD.uses_hk1'].deps                   # UniversalFInfinity
    assert 'CD.double_eq' in g_text.nodes['CD.size_zero'].deps                     # notation by scope
    deps = g_text.nodes['CD.Outer.fqm'].deps                                        # PosteriorReplicas
    assert 'CD.Inner.fqm' in deps and 'CD.fqm' not in deps
    assert g_text.fallbacks and all(len(x) == 3 for x in g_text.fallbacks)
    have = g_text.have_names({'CD.AZ.wcl', 'CD.ZG.wcl'})                           # Problem355
    out = C.Carver(g_text).carve({'CD.AZ.wcl'}, have, rename={'CD.AZ.wcl': 'wcl_oai'})
    assert 'theorem wcl_oai' in out and 'apply ZG.wcl\n' in out, out
    # every local instance in scope comes back, used or not (the rule before the records)
    out = C.Carver(g_text).carve({'CD.no_inst_use'}, g_text.have_names({'CD.no_inst_use', 'CD.Wide'}))
    assert re.search(r'^local instance cdLocalInst_r', out, re.M), out


# ---------------------------------------------------------------- coercions and foreign attributes

def _coer_plan(g, targets, bundle_budget=100):
    return C.make_plan(g, targets, budget=100, bundle_budget=bundle_budget,
                       cost=C.size_costs(g), bundle_prefix='CO', chunker='schedule')


def test_a_coercion_instance_that_elaborates_away_is_a_dependency(g):
    # Kirchberg–Rørdam (batch 3): `↑p` elaborates to `p.carrier` and `f n` to `f.toFun n`, so the
    # CoeSort/CoeFun instances were in no constant and no record, and the bundles lost them
    # ("Function expected"); the agent pinned them by hand
    assert 'CD.Co.instCoeSortPackType' in g.nodes['CD.Co.Pack.first'].deps
    assert 'CD.Co.coeFnFn' in g.nodes['CD.Co.fn_double_apply'].deps
    # in the statement's binders and type too
    assert 'CD.Co.instCoeSortPackType' in g.nodes['CD.Co.Pack.first'].sig
    # a declaration that does not use the coerced function does not need the instance
    assert 'CD.Co.coeFnFn' not in g.nodes['CD.Co.rdef'].deps
    assert 'CD.Co.instCoeSortPackType' not in g.nodes['CD.Co.Fn.double'].deps


def test_a_coercion_instance_on_an_abbreviated_subtype_is_a_dependency(g):
    # Elasticity (oaiq-006): `instance : CoeFun Test _ := ⟨fun f => f.val⟩` on `abbrev Test := {f // …}`;
    # its value names `Test` only (Subtype.val is a projection), so the wrapped-function rule saw nothing
    inst = [k for k in g.nodes if 'instCoeFun' in k and 'Tst' in k]
    assert len(inst) == 1, inst
    assert inst[0] in g.nodes['CD.Co.Tst.ev'].deps
    assert inst[0] not in g.nodes['CD.Co.rdef'].deps
    assert inst[0] not in g.nodes['CD.Co.Tst'].deps


def test_the_bundle_of_a_coerced_declaration_carries_the_coercion_instance(g):
    p = _coer_plan(g, ['CD.Co.fn_double_apply'])
    holders = {n for b in p['bundles'] for n in b['nodes']}
    assert {'CD.Co.coeFnFn', 'CD.Co.Fn.double'} <= holders


@pytest.mark.lean
def test_coercion_instances_compile(g, tmp_path):
    _compile_in_publish_order(g, _coer_plan(g, ['CD.Co.fn_double_apply', 'CD.Co.pack_first_eq']), tmp_path)


def test_a_global_attribute_the_file_may_not_set_is_not_repeated_where_a_bundle_carries_it(g):
    # `attribute [instance_reducible] rdef` on a declaration a bundle defines: Lean refuses it in
    # another file ("failed to set reducibility status, `rdef` has not been defined in this file,
    # consider using the `local` modifier"). The carver knew only reducible/irreducible/semireducible.
    keep, have = {'CD.Co.rdef_pos'}, g.have_names({'CD.Co.rdef_pos', 'CD.Co.rdef'})
    out = C.Carver(g).carve(keep, have)
    assert 'theorem rdef_pos' in out
    # Lean lets only rdef's own file set it, so the command is in rdef's module and the bundle
    # holding rdef carries it (a persistent attribute)
    assert not re.search(r'^attribute', out, re.M), out
    # where the declaration is, the global attribute stays
    out = C.Carver(g).carve({'CD.Co.rdef', 'CD.Co.rdef_pos'}, g.have_names({'CD.Co.rdef', 'CD.Co.rdef_pos'}))
    assert re.search(r'^attribute \[instance_reducible\] rdef$', out, re.M), out
    assert 'local instance_reducible' not in out


@pytest.mark.lean
def test_foreign_attributes_compile(g, tmp_path):
    p = C.make_plan(g, ['CD.Co.rdef_pos'], budget=100, bundle_budget=100, cost=C.size_costs(g),
                    bundle_prefix='AT', chunker='schedule', pinned=[['CD.Co.rdef']])
    _compile_in_publish_order(g, p, tmp_path)


def test_every_attribute_lean_restricts_to_the_declaring_file_is_known():
    # measured with Lean 4.33.1 (an attribute command in a file importing `foo`)
    for a in ('reducible', 'irreducible', 'semireducible', 'instance_reducible', 'inline', 'noinline',
              'macro_inline', 'always_inline', 'specialize', 'nospecialize', 'never_extract',
              'match_pattern', 'elab_as_elim', 'export', 'unbox', 'implemented_by', 'extern'):
        assert C.restricted_attribute('attribute [%s] foo' % a), a
    for a in ('simp', 'instance', 'ext', 'coe', 'default_instance'):
        assert not C.restricted_attribute('attribute [%s] foo' % a), a
    assert not C.restricted_attribute('attribute [local instance_reducible] foo')


def test_a_local_instance_that_won_a_subproblem_comes_back_though_no_term_names_it():
    # Kirchberg–Rørdam (batch 3): `local instance : SMul ℂ Defect` answered a subproblem while
    # `Defect →ₗ[ℂ] A` was elaborated, and the final term kept a defeq instance instead: no constant,
    # no `insts` entry. Carved without it, instance search timed out (the agent raised
    # synthInstance.maxHeartbeats). The problems instance search solved (`inst_keys`) still show it.
    for asked, comes_back in ((['Inhabited CD.Wide'], True), (['Inhabited CD.Wide CD.Other'], True),
                              (['Inhabited CD.Other'], False), (['Nonempty CD.Wide'], False), ([], False)):
        g = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
        user = g.nodes['CD.uses_local_inst']
        c = g.infos[user.module].commands[user.cmd]
        c.insts, c.sig_insts, c.used_keys, c.sig_used_keys, c.inst_keys = [], [], [], [], list(asked)
        for n in user.names:           # its compiled constants do not name the instance either
            g.consts[n]['t'] = [x for x in g.consts[n]['t'] if x != 'CD.cdLocalInst']
            g.consts[n]['v'] = [x for x in g.consts[n]['v'] if x != 'CD.cdLocalInst']
        out = C.Carver(g).carve({'CD.uses_local_inst'}, g.have_names({'CD.uses_local_inst', 'CD.Wide'}))
        assert bool(re.search(r'^local instance cdLocalInst_r\w+ : Inhabited Wide', out, re.M)) == comes_back, \
            (asked, out)


def test_an_instance_only_a_variable_binder_needs_is_a_dependency_of_the_declarations_in_scope(g):
    # Kirchberg–Rørdam bundle: `variable (h0 : W.x 0 0 * v = v)` elaborates `OfNat (Fin rankNum) 0`
    # through the global `NeZero rankNum` instance; the declarations below do not use h0, so none
    # named the instance, the bundle lacked it and its `variable` line failed
    assert 'CD.Co.instPosFive' in g.nodes['CD.Co.var_user'].deps
    assert 'CD.Co.instPosFive' in g.nodes['CD.Co.var_user'].sig
    assert 'CD.Co.instPosFive' not in g.nodes['CD.Co.rdef'].deps


@pytest.mark.lean
def test_variable_binders_needing_an_instance_compile(g, tmp_path):
    _compile_in_publish_order(g, _coer_plan(g, ['CD.Co.var_user'], bundle_budget=0.0001), tmp_path)


def test_a_restricted_attribute_on_an_external_declaration_is_kept_local(g):
    # Coboundary (2026-10-26): `attribute [reducible] Face`, with Face in a published bundle
    # (external_defs), was dropped, so every proof that saw through Face failed in the carved file.
    # No bundle of the carve carries it and Lean lets only Face's file set it globally.
    keep, have = {'CD.Co.rdef_pos'}, g.have_names({'CD.Co.rdef_pos', 'CD.Co.rdef'})
    out = C.Carver(g).carve(keep, have, external={'CD.Co.rdef'})
    assert re.search(r'^attribute \[local instance_reducible\] _root_\.CD\.Co\.rdef$', out, re.M), out
    assert out.index('attribute [local') < out.index('-- module')          # at the top: the port's is global
    out = C.Carver(g).carve(keep, have)
    assert not re.search(r'^attribute', out, re.M), out


# `deriving instance Fintype for Skeleton` declares an instance (`instFintypeSkeleton`), but the
# command has no `decl_kind` and no `names`, so it was nobody's node: every bundle holding any of
# its module's commands got a copy, and a copy in a bundle that lacked the instance it uses
# (`instFintypeMarker`, another bundle's) failed (PeriodicGroups HeadTour, 2026-10-26).

def test_a_deriving_instance_command_is_a_declaration_command():
    class Cmd:
        decl_kind = None
        short_kind = 'deriving'
        names = []

    assert C._is_decl_command(Cmd())
    Cmd.short_kind = 'open'
    assert not C._is_decl_command(Cmd())


# `open Aux` in Top comes before the `namespace CD.Aux` block Top ends with. Mid made CD.Aux earlier,
# but a bundle holding only Top's `laterConst` does not import Mid: the `open` is dead there.
# The carver counted a namespace made by any command of the module as alive for every `open` of
# it (PeriodicGroups BooleanCircuits, 2026-10-26: "unknown namespace `Structured.Device.Formula`").

def test_open_before_the_namespace_block_that_makes_it_is_dropped(g):
    keep = {'CD.main', '_private.CarveDev.Top.0.CD.helper', 'CD.Aux.laterConst'}
    have = {'CD.Space', 'CD.Space.size', 'CD.double', 'CD.List.headOr', 'CD.size_zero',
            'CD.double_succ', 'CD.List.headOr_nil'}
    txt = carve(g, keep, have)
    assert 'open Aux' not in txt and 'laterConst' in txt


# `attribute [-simp] a b` with a and b gone: the command lost its targets but not its `simp` token,
# and was emitted as `attribute [-simp] ` ("expected identifier" at the next `end`;
# PeriodicGroups BooleanCircuits, 2026-10-26).

def test_attribute_command_whose_targets_are_all_gone_is_dropped(g):
    keep = {'CD.main', '_private.CarveDev.Top.0.CD.helper'}
    have = {'CD.Space', 'CD.Space.size', 'CD.double', 'CD.List.headOr', 'CD.size_zero',
            'CD.double_succ', 'CD.List.headOr_nil'}
    txt = carve(g, keep, have)
    assert 'attribute [-simp]' not in txt
