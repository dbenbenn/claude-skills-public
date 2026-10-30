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


def test_listed_private_lemmas_may_be_promoted_like_public_ones(g, monkeypatch):
    # oaiq-091: the automatic split of a slow piece could promote public lemmas only; pieces of 60 and 394
    # private lemmas needed a hand `forced` entry per graph node name. `promote_private` lists the private
    # theorems the plan may promote (carve_pipeline: the slow piece's own); unlisted ones never are
    h = '_private.CarveDev.Top.0.CD.helper'
    monkeypatch.setattr(C, 'collision_renames', lambda g: {})     # the fixture's two helpers collide
    cost = dict(C.size_costs(g, bytes_per_second=10000), **{h: 1.0})
    kw = dict(budget=0.05, piece_size=10**6, bundle_budget=0.005, bundle_size=10**6, cost=cost, bundle_prefix='PP')
    before = C.make_plan(g, ['CD.main'], **kw)
    assert h not in before['nodes'] and 'CD.main' in before['over']
    after = C.make_plan(g, ['CD.main'], promote_private=[h], **kw)
    assert h in after['nodes'] and 'CD.main' not in after['over'] and h not in after['pieces']['CD.main']['keep']


def test_private_names_are_per_module(g):
    a, b = '_private.CarveDev.Mid.0.CD.helper', '_private.CarveDev.Top.0.CD.helper'
    assert a in g.nodes and b in g.nodes
    assert a in g.nodes['CD.double_succ'].deps and b not in g.nodes['CD.double_succ'].deps
    assert b in g.nodes['CD.main'].deps
    assert {k: v for k, v in C.collision_renames(g).items() if '.IC.' not in k and '_dup' not in k} == \
        {a: 'helper_p0', b: 'helper_p1'}


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
    from record_fixtures import CARVE_ROOTS
    rec = C.record_fixture(FIX, 'CarveDev', CARVE_ROOTS, str(tmp_path / 'olean'), str(tmp_path / 'rec'))
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


def test_gen_takes_published_statements_verbatim_from_frozen_lib(tmp_path):
    # oaiq-081 (2026-10-30): a frozen re-plan of an overlap carve regenerated 13 live statements with an
    # extra `import` or a different `attribute [-instance]` line; publish_early's drift check refuses
    # that, so no slow piece could be re-split. A published statement is as frozen as a bundle: gen
    # writes the copy in frozen.lib byte for byte.
    cfg, work, out, run = _carve_cli(tmp_path, 'first')
    run('plan', str(cfg))
    run('gen', str(cfg))
    pub = tmp_path / 'published'
    pub.mkdir()
    thm = sorted(p.name for p in (out / 'lib').glob('Thm_*.lean'))[0]
    for b in ('CDB000', 'CDB002'):
        (pub / ('Def_%s.lean' % b)).write_bytes((out / 'lib' / ('Def_%s.lean' % b)).read_bytes())
    (pub / thm).write_text((out / 'lib' / thm).read_text() + '-- as published\n')
    frozen = {'plan': str(work / 'plan.json'), 'bundles': ['CDB000', 'CDB002'], 'lib': str(pub)}
    cfg2, work2, out2, run2 = _carve_cli(tmp_path, 'second', frozen=frozen)
    run2('plan', str(cfg2))
    run2('gen', str(cfg2))
    assert (out2 / 'lib' / thm).read_bytes() == (pub / thm).read_bytes()


def test_gen_fails_on_a_patch_matching_no_generated_file(tmp_path):
    # oaiq-123 (NuclearUltrapower): post-carve patches naming a collision-suffixed instance
    # (`normEntryOrder_r606002_1`) silently stopped matching after a snapshot change; gen only
    # listed "patches matching no generated file". A full gen now fails and names the patch.
    pat = tmp_path / 'patches.json'
    pat.write_text(json.dumps([
        {'literal_old': 'theorem double_succ', 'literal_new': 'theorem double_succ', 'why': 'matches'},
        {'literal_old': 'normEntryOrder_r606002_1', 'literal_new': 'x', 'why': 'stale instance name'}]))
    cfg, work, out, run = _carve_cli(tmp_path, 'a', patches=str(pat))
    run('plan', str(cfg))
    msg = run('gen', str(cfg), ok=False)
    assert 'normEntryOrder_r606002_1' in msg and 'stale instance name' in msg, msg
    assert 'theorem double_succ' not in msg.split('MATCHING NO GENERATED FILE')[-1]
    # the files are written all the same, so the stale patch can be checked against them
    assert (out / 'solutions' / 'Sol_CD_main.lean').exists()
    # a partial gen (named files, or one kind) cannot tell
    run('gen', str(cfg), 'pieces')
    run('gen', str(cfg), 'all', 'CD.top_pick')
    pat.write_text(json.dumps([{'literal_old': 'theorem double_succ',
                                'literal_new': 'theorem double_succ', 'why': 'matches'}]))
    run('gen', str(cfg))


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


def test_a_local_instance_that_won_a_subproblem_comes_back_though_no_term_names_it(monkeypatch):
    # Kirchberg–Rørdam (batch 3): `local instance : SMul ℂ Defect` answered a subproblem while
    # `Defect →ₗ[ℂ] A` was elaborated, and the final term kept a defeq instance instead: no constant,
    # no `insts` entry. Carved without it, instance search timed out (the agent raised
    # synthInstance.maxHeartbeats). The problems instance search solved (`inst_keys`) still show it.
    # (uses_local_inst uses Wide, so the carrier rule brings the instance back anyway; it is off
    # here, to pin the inst_keys test alone.)
    monkeypatch.setattr(C.Carver, '_carrier_used', lambda *a: False)
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


class _FakeInfo:
    def __init__(self, text):
        self.text_bytes = text.encode()


class _FakeCmd:
    def __init__(self, text, groups):
        self.binders = groups
        self.idents = []
        for grp in groups:
            for name, pos in grp['refs']:
                self.idents.append({'role': 'ref', 'name': name, 'start': pos, 'end': pos + len(name)})


def test_a_name_bound_again_earlier_in_one_variable_command_is_not_lost_for_its_later_groups():
    # OpenAI KL invariance (2026-10-26): `{B : Type ub} [CommRing B] [Algebra k B] (e : A ≃ₐ[k] B)`
    # after an earlier `{A B : Type ua}` whose B was dropped: the later groups mention the new B,
    # bound by the group just before them, and were cut as if they named the dropped one
    text = 'variable {B : Type ub} [CommRing B] (e : B)'
    pos = lambda s, k=0: [m for m in __import__('re').finditer(r'\b%s\b' % s, text)][k].start()
    groups = [dict(names=['B'], start=9, end=22, refs=[]),
              dict(names=[], start=23, end=34, refs=[('B', pos('B', 1))]),
              dict(names=['e'], start=35, end=43, refs=[('B', pos('B', 2))])]
    c = _FakeCmd(text, groups)
    carver = C.Carver.__new__(C.Carver)
    carver._gone = lambda *a, **k: False
    carver.g = type('G', (), {'reading': staticmethod(lambda *a: None)})()
    dropped = {'B'}
    assert carver._variable(_FakeInfo(text), c, 'M', set(), [], dropped, set()) is False
    assert dropped == set()


def test_a_local_borel_space_instance_answers_an_opens_measurable_space_problem():
    # FKMaps (oaiq-021, 2026-10-26): `local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩` supplies
    # `OpensMeasurableSpace C(unitInterval, ℝ)` through `BorelSpace.opensMeasurable`; the problem's class
    # is the parent, so the instance was carved away and the piece failed to synthesize it.
    import types
    inst = types.SimpleNamespace(declares=[('inst', 'BorelSpace', ['ContinuousMap', 'Real'])])
    asked = types.SimpleNamespace(inst_keys=['OpensMeasurableSpace ContinuousMap Real'])
    other = types.SimpleNamespace(inst_keys=['Nonempty ContinuousMap Real'])
    assert C._could_answer(inst, asked)
    assert not C._could_answer(inst, other)


def test_a_fully_generic_local_instance_answers_any_problem_of_its_class():
    # DilutedSpin (oaiq-041, 2026-10-27): `local instance (β : Type) : DecidableEq β := Classical.decEq β`
    # declares no head constants, so the heads-subset test never fired; a piece asking `DecidableEq Option`
    # lost the instance and failed to synthesize `DecidableEq (Option S.Vertex)`.
    import types
    inst = types.SimpleNamespace(declares=[('inst', 'DecidableEq', [])])
    asked = types.SimpleNamespace(inst_keys=['DecidableEq Option'])
    other = types.SimpleNamespace(inst_keys=['Fintype Option'])
    assert C._could_answer(inst, asked)
    assert C._could_answer(inst, other)       # a generic Decidable* instance counts for any recorded problem (next test)
    # a generic instance of another class answers problems of its own class only (the Decidable*
    # widening above is for decidability alone); aae14f3 asserted this against `other`, a Fintype
    # problem, which a generic Fintype instance does answer (102b62a)
    generic_fintype = types.SimpleNamespace(declares=[('inst', 'Fintype', [])])
    assert C._could_answer(generic_fintype, other)
    assert not C._could_answer(generic_fintype, asked)


def test_a_local_decidable_instance_is_kept_for_a_command_that_asks_about_its_type():
    # DilutedSpin (oaiq-041): `local instance (S) : DecidableEq (Edge S) := Classical.decEq _` is used by
    # `rw [requirements_selector]` through an instance argument unification assigns, so LeanInfo records
    # neither the instance nor a `DecidableEq` problem; the command only asks `Fintype Edge`. A decidability
    # instance is kept when its type's head constants occur among the command's problems.
    import types
    inst = types.SimpleNamespace(declares=[('inst', 'DecidableEq', ['Edge'])])
    asked = types.SimpleNamespace(inst_keys=['Fintype Edge', 'Fintype Sample'])
    other = types.SimpleNamespace(inst_keys=['Fintype Sample'])
    assert C._could_answer(inst, asked)
    # heads are not required to match (SharpRamsey, oaiq-045: `DecidableEq (Block w)` over an abbrev the
    # record shows unfolded, `Fintype Prod …`): a decidability instance was in force in its section
    assert C._could_answer(inst, other)
    assert not C._could_answer(inst, types.SimpleNamespace(inst_keys=[]))
    nonDecidable = types.SimpleNamespace(declares=[('inst', 'Fintype', ['Edge'])])
    assert not C._could_answer(nonDecidable, types.SimpleNamespace(inst_keys=['DecidableEq Sample', 'Foo Edge']))


def test_a_generic_decidability_instance_is_kept_for_any_proof_that_asked_something():
    # DilutedSpin (oaiq-041): `physicalOverlapLimsup_antitone` applies `DepthAverage.average_domain_bound`,
    # whose `[DecidableEq S.Vertex]` unification assigns; nothing records a `DecidableEq` problem (it asks
    # `Fintype`-family and arithmetic problems only). A fully generic `Decidable*` local instance was in
    # force for the whole section, so a proof (never a statement) keeps it whenever it asked anything.
    import types
    inst = types.SimpleNamespace(declares=[('inst', 'DecidableEq', [])])
    assert C._could_answer(inst, types.SimpleNamespace(inst_keys=['Add Nat', 'Fintype Vertex']))
    assert not C._could_answer(inst, types.SimpleNamespace(inst_keys=[]))
    generic_fintype = types.SimpleNamespace(declares=[('inst', 'Fintype', [])])
    assert not C._could_answer(generic_fintype, types.SimpleNamespace(inst_keys=['Add Nat']))


def test_reactivated_instance_uses_its_collision_rename():
    # Lech/Dutta (oaiq-032): ten modules declare `private local instance concreteRing`; the bundle
    # deprivatizes them as concreteRing_p0.., and a piece's `attribute [local instance]` named the
    # old public name, which no bundle has
    ik = '_private.M.0.OAI.Lech.ReesRoot.concreteRing'
    assert C.instance_ref(ik, {}, {ik: 'concreteRing_p3'}) == 'OAI.Lech.ReesRoot.concreteRing_p3'
    assert C.instance_ref(ik, {}, {}) == 'OAI.Lech.ReesRoot.concreteRing'
    assert C.instance_ref(ik, {ik: 'B.inst'}, {ik: 'concreteRing_p3'}) == 'B.inst'
    assert C.instance_ref('top', {}, {'top': 'top_p0'}) == 'top_p0'


def test_collided_instance_is_imported_only_under_its_renamed_name():
    # Lech/Dutta (oaiq-032): projectiveModule is private in ten modules, so one copy's bundle made
    # the public name `have` for all ten and a bundle imported a `projectiveModule_p7` nobody had
    ik = '_private.M.0.OAI.Lech.ReesRoot.projectiveModule'
    ren = {ik: 'projectiveModule_p7'}
    assert C.instance_imported(ik, {'OAI.Lech.ReesRoot.projectiveModule'}, {}) is True
    assert C.instance_imported(ik, {'OAI.Lech.ReesRoot.projectiveModule'}, ren) is False
    assert C.instance_imported(ik, {'OAI.Lech.ReesRoot.projectiveModule_p7'}, ren) is True
    assert C.instance_imported(ik, set(), {}) is False


# Collided private local instances (Lech multiplicity, oaiq-032, 2026-10-27): InstColA and InstColB
# each declare `private local instance zeroR` and `oneR`, renamed zeroR_p0/_p1 and oneR_p0/_p1;
# `oneR`'s statement needs `zeroR` in force.

IC_A, IC_B = '_private.CarveDev.InstColA.0.CD.IC.', '_private.CarveDev.InstColB.0.CD.IC.'
IC_DEFS = {'CD.IC.R', 'CD.IC.Zeroish', 'CD.IC.Oneish'}


def _section(txt, m):
    return txt[txt.index('-- module ' + m):].split('\nend\n\n', 1)[0]


def test_a_collided_local_instance_kept_from_another_module_still_comes_back(g):
    # the file keeps InstColA's zeroR (zeroR_p0) and InstColB's oneR, whose statement needs
    # InstColB's zeroR (zeroR_p1, imported): the public name `CD.IC.zeroR` of the kept copy made
    # InstColB's look declared by the file, so nothing put it back in force (Lech L026: the kept
    # scalarComm_p6 needed concreteRing of the same module, imported, and was cut by a repair)
    keep = IC_DEFS | {IC_A + 'zeroR', IC_B + 'oneR'}
    ren = C.collision_renames(g)
    have = g.have_names(keep | {IC_B + 'zeroR'})
    txt = C.Carver(g).carve(keep, have, deprivatize=True, rename=ren)
    sec = _section(txt, 'CarveDev.InstColB')
    assert 'attribute [local instance] CD.IC.zeroR_p1' in sec, sec
    assert sec.index('attribute [local instance] CD.IC.zeroR_p1') < sec.index('instance oneR_p1')


def test_a_library_name_a_project_declaration_shadows_is_pinned(g):
    # oaiq-096 (CubicMoment, 2026-10-29): the project lemma `norm_nonneg` (CubicGram_Coordinates) sat
    # in the same carved piece as modules that never imported it and meant Mathlib's: `norm_nonneg _`
    # inside `namespace CubicFirstMoment` read the project one ("Type mismatch", 20 pieces). A library
    # constant Lean resolved is written `_root_.` when the carved file would read the text as a
    # project declaration the module did not see.
    keep = {'CD.Sh.Nat.le_refl', 'CD.Sh.useRefl'}
    txt = C.Carver(g).carve(keep, g.have_names(keep))
    sec = _section(txt, 'CarveDev.ShadowB')
    assert 'Nat.le_refl n' in sec and '_root_.Nat.le_refl n' in sec, sec
    # alone, nothing shadows it: no pin
    keep = {'CD.Sh.useRefl'}
    sec = _section(C.Carver(g).carve(keep, g.have_names(keep)), 'CarveDev.ShadowB')
    assert '_root_.Nat.le_refl' not in sec, sec


def test_a_name_a_dotted_declarations_namespace_shadows_is_pinned(g):
    # q135 (VertexCover, 2026-10-31): `def Poly.finite` reads its body with namespace `Poly` open, and
    # its bundle also held `Poly.some` from a module it never imported: `| some s =>` read
    # `Poly.some` ("Invalid pattern"), and so did `Stream.poly (some …)`. The pin looks names up
    # from the declaration's own namespace, takes a library constant written by a suffix of its
    # name (`some` is `Option.some` by export), and covers a `match` pattern, never a tactic
    # alternative (`cases q with | some n`, where only the constructor's short name parses).
    keep = {'CD.Sh.Pk.some', 'CD.Sh.Pk.fin', 'CD.Sh.Pk.mk', 'CD.Sh.Pk.fin_le'}
    txt = C.Carver(g).carve(keep, g.have_names(keep))
    sec = _section(txt, 'CarveDev.ShadowD')
    assert '| _root_.Option.some n => n' in sec, sec
    assert 'Option Nat := _root_.Option.some 3' in sec, sec
    assert '  | none => 0' in sec, sec                     # nothing captures `none`
    assert '  | some n => exact' in sec and '  | none => exact' in sec, sec
    # alone, nothing shadows them: no pin
    keep = {'CD.Sh.Pk.fin', 'CD.Sh.Pk.mk'}
    sec = _section(C.Carver(g).carve(keep, g.have_names(keep)), 'CarveDev.ShadowD')
    assert '_root_.Option' not in sec, sec


def test_a_collided_instance_of_an_unimported_copy_is_not_hidden(g, monkeypatch):
    # oaiq-096 (CubicMoment, 2026-10-29): bundle A018 hid `instFinite…_p0` and `_p1`, copies of one
    # anonymous instance declared in the later bundles A019/A021: "Unknown constant". The check
    # `pubname(i) in have` took the base name, which another collided copy (the one the file keeps)
    # supplies; a collided copy counts as imported only under its own renamed name.
    keep = IC_DEFS | {IC_A + 'zeroR'}
    ren = C.collision_renames(g)
    cv = C.Carver(g)
    cv.keep = set(keep)
    monkeypatch.setattr(g, '_global_insts', [IC_B + 'zeroR'], raising=False)
    monkeypatch.setattr(C, '_could_match', lambda *a: True)
    have = g.have_names(keep)
    assert cv._unseen_instances('CarveDev.InstColA', have, set(), ren) == []
    have = have | {'CD.IC.zeroR_p1'}
    assert cv._unseen_instances('CarveDev.InstColA', have, set(), ren) == ['_root_.CD.IC.zeroR_p1']


def test_a_reemitted_local_instance_brings_back_the_earlier_ones_it_used_first(g):
    # one_b's record names only oneR (Lech: the declaration's term kept a defeq instance for
    # concreteRing); oneR, emitted again, needs zeroR before it, which one_b alone never asked for
    # (Def_OAIQ032L035: `baseAlgebra_r…` before `concreteRing_r…`, "typeclass instance problem is stuck")
    g = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
    user = g.nodes['CD.IC.one_b']
    c = g.infos[user.module].commands[user.cmd]
    c.insts = c.sig_insts = [IC_B + 'oneR']
    c.inst_keys = [k for k in c.inst_keys if not k.startswith('CD.IC.Zeroish')]
    c.used_keys = c.sig_used_keys = []
    for n in user.names:
        for f in ('t', 'v'):
            g.consts[n][f] = [x for x in g.consts[n][f] if x != IC_B + 'zeroR']
    keep = IC_DEFS | {'CD.IC.one_b'}
    txt = C.Carver(g).carve(keep, g.have_names(keep), rename=C.collision_renames(g))
    sec = _section(txt, 'CarveDev.InstColB')
    z = re.search(r'^private local instance zeroR_r\w+', sec, re.M)
    o = re.search(r'^private local instance oneR_r\w+', sec, re.M)
    assert z and o and z.start() < o.start() < sec.index('theorem one_b'), sec


def _ic_plan(nodes0, nodes1):
    return {'bundles': [{'name': 'IC0', 'nodes': sorted(nodes0), 'imports': []},
                        {'name': 'IC1', 'nodes': sorted(nodes1), 'imports': ['IC0']}],
            'stubs': {}, 'pieces': {}, 'nodes': []}


def test_a_local_instance_its_imported_bundle_text_lacks_is_emitted_again_not_activated(g, tmp_path):
    # a node can be in a bundle's plan `nodes` while that bundle's text lost the command (a repair
    # cut the local instance), and `attribute [local instance] scalarComm_p6` named a constant no
    # file declares (Def_OAIQ032L039:289): only what the imported text declares is activated
    P = _ic_plan(IC_DEFS | {IC_B + 'zeroR'}, {IC_B + 'oneR'})
    C.generate(g, P, str(tmp_path), what=('bundles',))
    b1 = open(tmp_path / 'lib' / 'Def_IC1.lean').read()
    assert 'attribute [local instance] CD.IC.zeroR_p1' in b1, b1
    cut = open(tmp_path / 'lib' / 'Def_IC0.lean').read()
    cut = re.search(r'^local instance zeroR_p1 .*$', cut, re.M).group(0)
    C.generate(g, P, str(tmp_path), what=('bundles',), repairs={'Def_IC0.lean': [cut]})
    assert 'zeroR_p1' not in open(tmp_path / 'lib' / 'Def_IC0.lean').read()
    b1 = open(tmp_path / 'lib' / 'Def_IC1.lean').read()
    assert 'attribute [local instance] CD.IC.zeroR_p1' not in b1, b1
    assert re.search(r'^(?:private )?local instance zeroR_r\w+', b1, re.M), b1
    # regenerating only IC1 reads IC0's text from the earlier run
    C.generate(g, P, str(tmp_path), what=('bundles',), names={'IC1'})
    assert 'attribute [local instance] CD.IC.zeroR_p1' not in open(tmp_path / 'lib' / 'Def_IC1.lean').read()


def test_a_kept_local_instance_brings_its_same_type_siblings():
    # Thomason (oaiq-043, 2026-10-27): `local instance : Fintype (OrdinalVertices n)` beside the
    # kept `LinearOrder` one on the same synonym; partialLastVertex needed it ("failed to synthesize
    # Fintype ↑(OrdinalVertices n)") though no record of the port shows a use. Here verts_zero uses
    # the Zeroish instance on Verts; the Inhabited sibling comes back with it.
    g = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
    keep = {'CD.IC.R', 'CD.IC.Zeroish', 'CD.IC.Verts', 'CD.IC.instZeroishVerts', 'CD.IC.verts_zero'}
    txt = C.Carver(g).carve(keep, g.have_names(keep))
    sec = _section(txt, 'CarveDev.InstColA')
    s = re.search(r'^local instance instInhabitedVerts_r\w+ \(n : Nat\) : Inhabited \(Verts n\)', sec, re.M)
    assert s and s.start() < sec.index('theorem verts_zero'), sec
    # a declaration that uses no instance on Verts does not bring it
    keep = {'CD.IC.R', 'CD.IC.Zeroish', 'CD.IC.Verts', 'CD.IC.instZeroishVerts'}
    assert 'Inhabited' not in C.Carver(g).carve(keep, g.have_names(keep))



def test_local_instances_are_recognised_and_never_owned_across_modules(g):
    # DeclGraph's `i` comes from Meta.isInstance on the compiled environment, where a `local instance`
    # is no longer one, so is_local_instance (which also required it) was False for every local
    # instance and the cross-module guard in inst_owners never fired (found in the oaiq-032 fix).
    for k in (IC_A + 'zeroR', IC_A + 'oneR', IC_B + 'zeroR', 'CD.IC.instInhabitedVerts'):
        assert g.is_local_instance(k), k
    for k in ('CD.Co.instCoeFunTstForallNat', 'CD.IC.R', 'CD.IC.one_a'):
        assert not g.is_local_instance(k), k
    # InstColB imports InstColA, but InstColA's local zeroR is out of force there: a command of
    # InstColB that used `zeroR` used its own (the carver re-emits that command instead)
    idx = len(g.infos['CarveDev.InstColB'].commands)
    assert IC_A + 'zeroR' not in g.inst_owners([IC_A + 'zeroR'], 'CD.IC.one_b', 'CarveDev.InstColB', idx)
    # a global instance of an imported module still counts
    co = g.nodes['CD.Co.instCoeFunTstForallNat'].module
    users = [m for m in g.infos if m != co and g.sees(m, co)]
    if users:
        assert 'CD.Co.instCoeFunTstForallNat' in g.inst_owners(
            ['CD.Co.instCoeFunTstForallNat'], 'x', users[0], len(g.infos[users[0]].commands))


# Local context a carved file must put back (Auslander–Reiten, oaiq-031, 2026-10-27): the
# LocalCtx module.

LC_DEFS = {'CD.LC.Wc', 'CD.LC.Act', 'CD.LC.Tower', 'CD.LC.needsTower'}


def test_a_local_notation_written_against_a_modifier_letter_is_kept_for_a_first_declaration(g):
    # `Cᵐᵒᵖ` (here `Cᵒᵖ`): Lean reads the token `C` then the postfix; the textual use test took the
    # modifier letters for identifier characters, so a bundle whose first kept declaration was
    # simpleRightAction lost `local notation "C"` ("Unknown identifier `C`"), while a neighbouring
    # bundle keeping rightSimpleDualEquiv (written `C`) had it. The postfix itself was lost the same way.
    keep = {'CD.LC.Opp', 'CD.LC.Wc', 'CD.LC.oppSelf'}
    sec = _section(carve(g, keep), 'CarveDev.LocalCtx')
    assert 'local notation "C" => Wc 3' in sec, sec
    assert 'local postfix:max "ᵒᵖ" => Opp' in sec, sec
    # a declaration written without them still drops them
    sec = _section(carve(g, {'CD.LC.Opp', 'CD.LC.Wc', 'CD.LC.needsTower', 'CD.LC.Act', 'CD.LC.Tower'}),
                   'CarveDev.LocalCtx')
    assert 'local notation "C" => Wc' not in sec and 'local postfix:max' not in sec, sec


def test_uses_token_reads_identifiers_as_lean_does():
    assert C._uses_token('(a : Cᵐᵒᵖ)', 'C')
    assert C._uses_token('(a : C⁻¹)', 'C')
    assert not C._uses_token('(a : Cat)', 'C')
    assert not C._uses_token('(a : C₁)', 'C')          # subscripts are identifier characters
    assert not C._uses_token("(a : C')", 'C')
    assert not C._uses_token('(a : C?)', 'C')
    assert not C._uses_token('(a : x.C)', 'C')
    assert not C._uses_token('(a : Cα)', 'C')          # Greek letters too



def test_a_reactivated_local_instance_keeps_its_priority(g):
    # oaiq-031: `local instance (priority := 3000) nativeSimpleScalar` came back as `attribute [local
    # instance] …` (priority 1000), and the module's `attribute [local instance 2000]
    # moduleCatBaseModule` won ("synthesized type class instance is not definitionally equal").
    keep = LC_DEFS | {'CD.LC.tower_use'}
    have = g.have_names(keep | {'CD.LC.actHi', 'CD.LC.towerHi', 'CD.LC.actLo'})
    sec = _section(C.Carver(g).carve(keep, have), 'CarveDev.LocalCtx')
    assert 'attribute [local instance 3000] CD.LC.actHi\n' in sec, sec
    assert 'attribute [local instance] CD.LC.towerHi\n' in sec, sec
    assert C._instance_priority(b'local instance (priority := high) x : A := a') == 'high'
    assert C._instance_priority(b'local instance x : A := a') is None


def _lc_graph_tower_unseen():
    """The fixture graph with tower_use's record naming only actHi (Auslander–Reiten: the
    IsScalarTower partner of a Module local instance is a Prop instance no elaborated term names)."""
    g = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
    user = g.nodes['CD.LC.tower_use']
    c = g.infos[user.module].commands[user.cmd]
    c.insts = c.sig_insts = ['CD.LC.actHi']
    c.inst_keys = [k for k in c.inst_keys or () if not k.startswith('CD.LC.Tower')]
    c.used_keys = c.sig_used_keys = [k for k in c.used_keys or () if not k.startswith('CD.LC.Tower')]
    for n in user.names:
        for f in ('t', 'v'):
            g.consts[n][f] = [x for x in g.consts[n][f] if x != 'CD.LC.towerHi']
    return g


def test_a_used_local_instance_brings_its_prop_partner_on_the_same_carrier():
    # oaiq-031: `local instance … : Module k (…).carrier` and `local instance … : IsScalarTower k A
    # (…).carrier`; only the Module one shows as used, and the carved file lacked the tower
    # ("failed to synthesize SMulCommClass k R …"). Here actHi (Act (Wc n)) and towerHi
    # (Tower Nat (Wc n)): different classes, argument heads sharing the carrier Wc.
    g = _lc_graph_tower_unseen()
    keep = LC_DEFS | {'CD.LC.tower_use'}
    sec = _section(C.Carver(g).carve(keep, g.have_names(keep)), 'CarveDev.LocalCtx')
    a = re.search(r'^local instance \(priority := 3000\) actHi_r\w+', sec, re.M)
    t = re.search(r'^local instance towerHi_r\w+', sec, re.M)
    assert a and t and a.start() < t.start() < sec.index('theorem tower_use'), sec
    # imported from a bundle: both activated, the partner too (a kept constant there)
    have = g.have_names(keep | {'CD.LC.actHi', 'CD.LC.towerHi', 'CD.LC.actLo'})
    sec = _section(C.Carver(g).carve(keep, have), 'CarveDev.LocalCtx')
    assert re.search(r'^attribute \[local instance(?: \d+)?\] CD\.LC\.towerHi$', sec, re.M), sec
    # the partner not in a bundle: emitted again, never activated as a constant no file declares
    have = g.have_names(keep | {'CD.LC.actHi', 'CD.LC.actLo'})
    sec = _section(C.Carver(g).carve(keep, have), 'CarveDev.LocalCtx')
    assert 'attribute [local instance 3000] CD.LC.actHi\n' in sec, sec
    assert 'CD.LC.towerHi' not in sec and re.search(r'^local instance towerHi_r\w+', sec, re.M), sec


def test_a_used_local_instance_brings_a_partner_stated_over_it_on_a_variable_carrier():
    # oaiq-123 (NuclearUltrapower): `local instance normEntryOrder (i : ι) : PartialOrder (A i)` and
    # `local instance normEntryStarOrder (i : ι) : StarOrderedRing (A i)`; the carrier `A i` is a bound
    # variable, so neither has a type head and the shared-carrier rule never matched; the carved bundle
    # lacked the StarOrderedRing one ("failed to synthesize" at CStarMatrix). The partner's heads name
    # the used instance itself (its class takes it as an argument): that alone brings it back.
    # Here actHi (heads gone) is found only through its bare class key, as normEntryOrder was through
    # `key:PartialOrder`, and towerHi's heads are just actHi.
    g = _lc_graph_tower_unseen()
    user = g.nodes['CD.LC.tower_use']
    for c in g.infos[user.module].commands:
        for i, x in enumerate(c.declares or ()):
            if x[0] == 'CD.LC.actHi':
                c.declares[i] = [x[0], x[1], []]
            elif x[0] == 'CD.LC.towerHi':
                c.declares[i] = [x[0], x[1], ['CD.LC.actHi']]
    c = g.infos[user.module].commands[user.cmd]
    c.insts = c.sig_insts = []
    c.inst_keys = c.used_keys = c.sig_used_keys = ['CD.LC.Act']
    for n in user.names:
        for f in ('t', 'v'):
            g.consts[n][f] = [x for x in g.consts[n][f] if x != 'CD.LC.actHi']
    keep = LC_DEFS | {'CD.LC.tower_use'}
    car = C.Carver(g)
    car._carrier_used = lambda *a: False      # `A i` is a bound variable: no carrier to mention
    sec = _section(car.carve(keep, g.have_names(keep)), 'CarveDev.LocalCtx')
    a = re.search(r'^local instance \(priority := 3000\) actHi_r\w+', sec, re.M)
    t = re.search(r'^local instance towerHi_r\w+', sec, re.M)
    assert a and t and a.start() < t.start() < sec.index('theorem tower_use'), sec


def test_extending_a_frozen_carve_keeps_its_external_definitions_external(g, ext_plan):
    # oaiq-057 (DimensionTen Channel extending oaiq-033's published carve): the first carve took
    # Mat, krausMap's types, … from Def_DimensionTenPair (its external_defs); the second carve's
    # targets import only Def_DimensionTenChannel, so those declarations became its own bundle
    # material, a frozen bundle "needed" them from a new bundle, and `plan` failed ("needs krausMap
    # from bundle OAIQ033D009, not imported", plus an import cycle). The frozen bundles import the
    # first carve's external bundle, so the second carve does too.
    names = [b['name'] for b in ext_plan['bundles']]
    p = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.005,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    frozen=(ext_plan, names), bundle_prefix='NEW')
    assert p['external_defs'] == {'CD.double': 'Definitions.Def_Ext'}
    assert all('CD.double' not in b['nodes'] for b in p['bundles'])
    assert [b['name'] for b in p['bundles'][:len(names)]] == names
    assert C.check_plan(g, p) == []
    # this carve's own external_defs win over the frozen carve's
    p = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.005,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    frozen=(ext_plan, names), bundle_prefix='NEW',
                    external_defs={'CD.double': 'Definitions.Def_Mine'})
    assert p['external_defs'] == {'CD.double': 'Definitions.Def_Mine'}


def test_frozen_carve_against_another_definitions_bundle_says_so(g, ext_plan):
    # w2/oaiq-113 (TorsionFreeBass extending the first BassTrace carve): the frozen bundles were
    # carved against Def_BassTrace, this carve's goal imports Def_BassTorsionFree, which declares
    # the same names. This carve's external_defs win (right when one bundle imports the other), but
    # here the frozen bundles then needed Def_BassTrace-only declarations from a new bundle and
    # check_plan said only "imports a later or unknown bundle". The plan records the disagreement
    # and check_plan names it, with the way out.
    names = [b['name'] for b in ext_plan['bundles']]
    p = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.005,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    frozen=(ext_plan, names), bundle_prefix='NEW',
                    external_defs={'CD.double': 'Definitions.Def_Mine'})
    assert p['frozen_external_conflicts'] == {'Definitions.Def_Ext': ['Definitions.Def_Mine']}
    # a frozen bundle that now needs a new bundle
    q = json.loads(json.dumps(p))
    q['bundles'][0]['imports'] = [q['bundles'][-1]['name']]
    probs = C.check_plan(g, q)
    msg = [x for x in probs if 'later or unknown' in x]
    assert msg and q['bundles'][-1]['name'] in msg[0], probs
    assert 'Definitions.Def_Ext' in msg[0] and 'Definitions.Def_Mine' in msg[0], msg
    assert 'statement_suffix' in msg[0], msg
    # no disagreement: nothing recorded
    p = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.005,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    frozen=(ext_plan, names), bundle_prefix='NEW')
    assert 'frozen_external_conflicts' not in p


def _dq_graph():
    """The fixture graph with dq_use's and dq_use_late's records naming only dqW (SharpRamsey
    oaiq-060: the statement's term kept a defeq instance in place of the BDE it used)."""
    g = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
    for t in ('CD.LC.dq_use', 'CD.LC.dq_use_late'):
        user = g.nodes[t]
        c = g.infos[user.module].commands[user.cmd]
        c.insts = [x for x in c.insts if x != 'CD.LC.dqPair']
        c.sig_insts = [x for x in c.sig_insts if x != 'CD.LC.dqPair']
        for f in ('inst_keys', 'used_keys', 'sig_used_keys'):
            setattr(c, f, [x for x in getattr(c, f) or () if x != 'CD.LC.Dq Prod'])
        for n in user.names:
            for f in ('t', 'v'):
                g.consts[n][f] = [x for x in g.consts[n][f] if x != 'CD.LC.dqPair']
    return g


def test_a_used_local_instance_brings_its_same_class_siblings_in_source_order():
    # oaiq-060: `local instance BDE : DecidableEq (Fin w × Bool)`, `TDE`, `IDE : DecidableEq (Slots
    # w n)`, all `Classical.decEq _`; the statements' records named IDE (and TDE), their stubs got
    # those and not BDE, and failed "synthesized type class instance is not definitionally equal".
    # Here dqPair (Dq (Nat × Bool)) and dqW (Dq (Wc n)); dq_use's record names only dqW. Both come
    # back, in source order, so the one that won in the port still wins.
    g = _dq_graph()
    keep = {'CD.LC.Wc', 'CD.LC.Dq', 'CD.LC.dq_use'}
    for sorry in ({'CD.LC.dq_use'}, set()):
        sec = _section(C.Carver(g).carve(keep, g.have_names(keep), sorry=sorry), 'CarveDev.LocalCtx')
        a = re.search(r'^local instance dqPair_r\w+ : Dq \(Nat × Bool\)', sec, re.M)
        w = re.search(r'^local instance dqW_r\w+ \(n : Nat\) : Dq \(Wc n\)', sec, re.M)
        assert a and w and a.start() < w.start() < sec.index('theorem dq_use'), sec
    # a kept instance of the class that the port declared after the sibling (dqNat): put back
    # before dq_use_late, the sibling would take priority over it, so it stays out
    keep = {'CD.LC.Wc', 'CD.LC.Dq', 'CD.LC.dqNat', 'CD.LC.dq_use_late'}
    sec = _section(C.Carver(g).carve(keep, g.have_names(keep), sorry={'CD.LC.dq_use_late'}),
                   'CarveDev.LocalCtx')
    assert 'dqPair' not in sec and re.search(r'^local instance dqW_r', sec, re.M), sec


def test_a_local_instance_comes_back_when_the_record_names_a_foreign_one_of_its_class():
    # Finitistic (q128-finitistic-retry): `resolvedModelIso`'s module declared `local instance :
    # HasDerivedCategory (ModuleCat D)`, which answered its instance problem, but the record named
    # only another module's defeq local instance (reached by unification through an imported
    # abbrev), and the bundle dropped the module's own one ("failed to synthesize"). Here dq_for's
    # record is edited to name LocalCtx's dqPair instead of LocalFor's anonymous instance; the
    # carrier is a library type, so no project declaration of its type ties it to dq_for.
    g = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
    user = g.nodes['CD.LF.dq_for']
    c = g.infos[user.module].commands[user.cmd]
    c.insts = c.sig_insts = []
    for f in ('inst_keys', 'used_keys', 'sig_used_keys'):
        setattr(c, f, [x for x in getattr(c, f) or () if not x.startswith('CD.LC.Dq')])
    for n in user.names:
        for f in ('t', 'v'):
            g.consts[n][f] = ['CD.LC.dqPair' if x == 'CD.LF.instDqProdNatBool' else x
                              for x in g.consts[n][f]]
    keep = {'CD.LC.Dq', 'CD.LF.dq_for'}
    for sorry in ({'CD.LF.dq_for'}, set()):
        sec = _section(C.Carver(g).carve(keep, g.have_names(keep), sorry=sorry), 'CarveDev.LocalFor')
        s = re.search(r'^local instance instDqProdNatBool_r\w+ : Dq \(Nat × Bool\)', sec, re.M)
        assert s and s.start() < sec.index('theorem dq_for'), sec


def test_a_local_instance_on_a_type_a_declaration_uses_comes_back_though_nothing_records_its_use(g):
    # oaiq-066 (and oaiq-043): a `local instance : CoeFun (FunctionalTree.diagonalRep A) …` is
    # unfolded by coercion elaboration, so no constant, `insts` or `inst_keys` entry of its users
    # names it; the bundles lost it ("Function expected at ↑(diagonalRep A)"). Same for
    # `Primcodable (Symbols k i)` on an abbrev. A local instance whose type mentions a project
    # declaration the kept one uses comes back. Here the CoeFun on WcFn and wcfn_apply (`w 3`).
    nd = g.nodes['CD.LC.wcfn_apply']
    c = g.infos[nd.module].commands[nd.cmd]
    assert not c.insts and not [x for x in c.inst_keys or () if x.startswith('CoeFun')]
    keep = {'CD.LC.Wc', 'CD.LC.WcFn', 'CD.LC.wcfn_apply'}
    for sorry in ({'CD.LC.wcfn_apply'}, set()):
        sec = _section(C.Carver(g).carve(keep, g.have_names(keep), sorry=sorry), 'CarveDev.LocalCtx')
        s = re.search(r'^local instance instCoeFunWcFnForallNat_r\w+ \(n : Nat\) : CoeFun', sec, re.M)
        assert s and s.start() < sec.index('theorem wcfn_apply'), sec
    # carried by a bundle: activated
    have = g.have_names(keep | {'CD.LC.instCoeFunWcFnForallNat'})
    sec = _section(C.Carver(g).carve(keep, have), 'CarveDev.LocalCtx')
    assert re.search(r'^attribute \[local instance\] CD\.LC\.instCoeFunWcFnForallNat$', sec, re.M), sec


def _opt_plan():
    p = _leak_plan()
    p['bundles'][0]['nodes'] += ['CD.LI.NatOpt', 'CD.LI.natOptInhabited']
    for t in ('CD.LI.late_default',):            # the unhidable leak (test_hidden_instances_compile)
        p['nodes'].remove(t)
        del p['stubs'][t], p['pieces'][t]
    t = 'CD.LI.opt_default'
    p['nodes'].append(t)
    p['stubs'][t] = {'bundles': ['L0']}
    p['pieces'][t] = {'keep': [t], 'imports': [], 'bundles': ['L0']}
    return p


def test_an_unseen_instance_on_an_abbrev_is_hidden_where_its_class_was_asked(g):
    # CoulombAtom (oaiq-071): `spatialRotationMeasurable : MeasurableSpace SpatialRotation` reached
    # radialAverage_integrable's module through a bundle; the lemma mentions no project declaration
    # of the instance's type (SpatialRotation sits inside radialAverage's definition), so it was not
    # hidden, and the proof took it over `Subtype.instMeasurableSpace`. It solved `MeasurableSpace
    # (Subtype …)` problems (inst_keys), and an abbrev head matches anything. Here InstLate's
    # natOptInhabited on `abbrev NatOpt := Option Nat` and InstBase's opt_default.
    assert C._could_match(g, 'CD.LI.opt_default', 'CD.LI.natOptInhabited')
    assert not C._could_match(g, 'CD.LI.box_get', 'CD.LI.natOptInhabited')     # no Inhabited problem
    p = _opt_plan()
    for txt in (C.gen_piece(g, p, 'CD.LI.opt_default'), C.gen_stub(g, p, 'CD.LI.opt_default')):
        m = re.search(r'^attribute \[-instance\] (.*)$', txt, re.M)
        assert m and '_root_.CD.LI.natOptInhabited' in m.group(1).split(), txt
    assert 'natOptInhabited' not in C.gen_piece(g, p, 'CD.LI.box_get')


@pytest.mark.lean
def test_hidden_abbrev_instances_compile(g, tmp_path):
    _compile_in_publish_order(g, _opt_plan(), tmp_path)


def _lcm_plan(g):
    return C.make_plan(g, ['CD.uses_lcm23', 'CD.uses_lcm23_only'], budget=0.05, piece_size=10**6,
                       bundle_budget=0.005, bundle_size=10**6,
                       cost=C.size_costs(g, bytes_per_second=10000), bundle_prefix='SL')


def test_a_default_simp_call_depends_on_its_modules_earlier_rfl_simp_lemmas(g):
    # PeriodicLattice (oaiq-067): `@[simp] theorem encode_int_ofNat … := rfl` (library constants
    # only) and later `simp [Nat.bodd]` proofs; simp used it by definitional rewriting, so nothing
    # recorded the use, and the carved proofs' bundle did not import the lemmas ("unsolved goals").
    # Here lcm23 and uses_lcm23 (`by simp`); `simp only [...]` uses no default lemma.
    assert 'CD.lcm23' not in g.nodes['CD.uses_lcm23'].term
    assert 'CD.lcm23' in g.nodes['CD.uses_lcm23'].deps
    assert 'CD.lcm23' not in g.nodes['CD.uses_lcm23_only'].deps
    assert 'CD.uses_lcm23' not in g.nodes['CD.lcm23'].deps
    p = _lcm_plan(g)
    assert C.check_plan(g, p) == []
    pc = p['pieces']['CD.uses_lcm23']
    # an attributed declaration of the bundle material: the piece imports its bundle
    b = next(b['name'] for b in p['bundles'] if 'CD.lcm23' in b['nodes'])
    assert b in pc['bundles'], pc


@pytest.mark.lean
def test_default_simp_lemmas_compile(g, tmp_path):
    _compile_in_publish_order(g, _lcm_plan(g), tmp_path)


def test_an_attribute_that_declares_constants_is_applied_once_where_its_target_is(g):
    # SimpleAmenable (oaiq-065): `attribute [reassoc] Data.s₀_comp_δ₁` was kept in a bundle importing
    # the bundle that declares Data (and so already has `…_assoc`): "`…s₀_comp_δ₁_assoc` has already
    # been declared". Such an attribute (reassoc, simps, to_additive, ext, …) on a target of its own
    # module stays only in the file declaring the target; the generated constants are the target
    # node's. Here `attribute [ext] Pt` (Pt.ext, Pt.ext_iff).
    assert g.owner['CD.Co.Pt.ext'] == 'CD.Co.Pt'
    out = C.Carver(g).carve({'CD.Co.pt_eq'}, g.have_names({'CD.Co.pt_eq', 'CD.Co.Pt'}))
    assert 'theorem pt_eq' in out and not re.search(r'^attribute \[ext\]', out, re.M), out
    out = C.Carver(g).carve({'CD.Co.Pt'}, g.have_names({'CD.Co.Pt'}))
    assert re.search(r'^attribute \[ext\] Pt$', out, re.M), out
    assert C.generating_attribute('attribute [reassoc (attr := simp)] foo')
    assert not C.generating_attribute('attribute [simp] foo')
    assert C._attribute_list_end(b'attribute [reassoc (attr:=simp)] a b', 0, 36) == 32


@pytest.mark.lean
def test_declaring_attributes_compile(g, tmp_path):
    p = C.make_plan(g, ['CD.Co.pt_eq'], budget=100, bundle_budget=100, cost=C.size_costs(g),
                    bundle_prefix='GA', chunker='schedule', pinned=[['CD.Co.Pt']])
    assert any('CD.Co.Pt' in b['nodes'] for b in p['bundles'])
    _compile_in_publish_order(g, p, tmp_path)


# ---------------------------------------------------------------- folding statements into their importers

def test_fold_statements_merges_a_statement_into_every_importer(g, plan):
    # oaiq-039 (2026-10-28): 13 universe-polymorphic statements could never be proved on prove2.me (the
    # verifier's CoeT fallback timed out on their types). Folding each into the pieces that import it
    # leaves the importers' live statements as they are and makes their new pieces self-contained.
    f = C.fold_statements(plan, ['CD.double_succ'])
    assert 'CD.double_succ' not in f['nodes'] and 'CD.double_succ' not in f['pieces']
    assert 'CD.double_succ' not in f['stubs'] and f['folded'] == ['CD.double_succ']
    main = f['pieces']['CD.main']
    assert set(plan['pieces']['CD.double_succ']['keep']) <= set(main['keep'])
    assert main['imports'] == ['CD.size_via_coord']
    assert main['bundles'] == ['CDB001', 'CDB002']          # CDB000 comes in through CDB002
    assert plan['pieces']['CD.main']['imports'] == ['CD.double_succ', 'CD.size_via_coord']   # input untouched
    assert C.check_plan(g, f) == []
    txt = C.gen_piece(g, f, 'CD.main')
    assert 'Thm_CD_double_succ' not in txt and re.search(r'^theorem double_succ\b', txt, re.M)
    # the other pieces are generated exactly as before
    assert C.gen_piece(g, f, 'CD.top_aux') == C.gen_piece(g, plan, 'CD.top_aux')
    assert 'statement:CD.double_succ' not in [x for w in C.publish_order(f)['waves'] for x in w]


def test_fold_statements_refuses_a_target_or_an_unknown_node(plan):
    with pytest.raises(C.CarveError):
        C.fold_statements(plan, ['CD.main'])
    with pytest.raises(C.CarveError):
        C.fold_statements(plan, ['CD.no_such_statement'])


def test_folded_config_key_is_applied_by_plan_and_the_fold_command(tmp_path):
    # a re-plan keeps a fold: `carve.py plan` applies config `folded` after planning, and
    # `carve.py fold CONFIG NODE...` folds the current plan in place and records the nodes in the config
    import shutil
    import subprocess
    import sys
    work = tmp_path / 'work'
    work.mkdir()
    shutil.copy(os.path.join(FIX, 'decl_graph.jsonl'), work / 'decl_graph.jsonl')
    cfg = tmp_path / 'carve.json'
    base = {'src': FIX, 'prefix': 'CarveDev', 'roots': ['CarveDev.Top'], 'targets': TARGETS,
            'work': str(work), 'out': str(tmp_path / 'out'), 'bundle_prefix': 'CDB',
            'budget': 0.05, 'bundle_budget': 0.005, 'bytes_per_second': 10000}
    script = os.path.join(os.path.dirname(HERE), 'scripts', 'carve.py')

    def run(*a):
        r = subprocess.run([sys.executable, script] + list(a), capture_output=True, text=True)
        assert r.returncode == 0, r.stdout + r.stderr
        return r.stdout
    cfg.write_text(json.dumps(dict(base, folded=['CD.double_succ'])))
    run('plan', str(cfg))
    P = json.loads((work / 'plan.json').read_text())
    assert 'CD.double_succ' not in P['nodes'] and P['folded'] == ['CD.double_succ']
    cfg.write_text(json.dumps(base))
    run('plan', str(cfg))
    assert 'CD.double_succ' in json.loads((work / 'plan.json').read_text())['nodes']
    out = run('fold', str(cfg), 'CD.double_succ')
    assert 'CD.main' in out                                   # the importers whose pieces change
    assert 'CD.double_succ' not in json.loads((work / 'plan.json').read_text())['nodes']
    assert json.loads(cfg.read_text())['folded'] == ['CD.double_succ']
    assert 'plan OK' in run('check', str(cfg))


def test_fold_problems_are_only_the_ones_the_fold_adds(g, plan):
    # oaiq-039's published plan already carried 37 check_plan reports (source-text dependencies the
    # bundles never needed); `carve.py fold` must refuse a fold for what it breaks, not for those
    bad = json.loads(json.dumps(plan))
    for b in bad['bundles']:
        if 'CD.Space' in b['nodes']:
            b['nodes'].remove('CD.Space')
    assert C.check_plan(g, bad)
    assert C.fold_problems(g, bad, C.fold_statements(bad, ['CD.double_succ'])) == []
    broken = C.fold_statements(plan, ['CD.double_succ'])
    broken['pieces']['CD.main']['bundles'] = []
    assert C.fold_problems(g, plan, broken)


def test_frozen_bundle_members_get_no_implicit_dependencies(g):
    # oaiq-088 (Falconer all dimensions extending oaiq-038's published carve): a frozen member
    # (`PolicyBranch.exponentSum`) "implicitly used" an attributed lemma that this carve put in a
    # NEW bundle, which in turn needs the frozen bundle: an import cycle, so `_reduce` emptied
    # every import and the check said "needs X from the frozen bundle, not imported". A published
    # bundle's imports are fixed; implicit dependencies apply to new material only.
    old = {'bundles': [{'name': 'F0', 'nodes': ['CD.Space', 'CD.Space.size', 'CD.Space.coord']}],
           'external_defs': {}}
    p = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.01,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    bundle_prefix='N', chunker='schedule', frozen=(old, ['F0']))
    new = {k: b for b in p['bundles'] for k in b['nodes']}
    assert new['CD.Space.size_eq']['imports'] == ['F0']
    assert C.check_plan(g, p) == []


def test_a_frozen_bundles_inferred_needs_are_not_problems():
    # oaiq-120 (BallPacking, a carve published on an old skill, re-planned frozen after --upgrade):
    # the new graph rules (simp-set and implicit edges) made the published B000 "need" 37
    # declarations the new plan put in new bundles, and two import cycles. B000 compiled and was
    # published without them: a frozen bundle keeps its published imports, and its members' needs
    # are not reported.
    g = C.Graph.load(os.path.join(FIX, 'decl_graph.jsonl'), FIX)
    first = C.make_plan(g, ['CD.top_pick'], budget=0.05, piece_size=10**6, bundle_budget=0.005,
                        bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                        bundle_prefix='F')
    names = [b['name'] for b in first['bundles']]
    fz = {k for b in first['bundles'] for k in b['nodes']}
    k = first['bundles'][0]['nodes'][0]
    # a declaration the first carve never bundled, which needs the frozen bundle in turn
    d = next(x for x in ('CD.Space.size', 'CD.Space', 'CD.double') if x not in fz)
    g.nodes[k].deps.add(d)
    g.nodes[d].deps.add(k)
    p = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.005,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000),
                    frozen=(first, names), bundle_prefix='NEW')
    assert p['frozen'] == names
    assert p['bundles'][0]['imports'] == first['bundles'][0]['imports']
    assert C.check_plan(g, p) == [], C.check_plan(g, p)
    # without `frozen` in the plan (an old plan file), the same need is a problem
    q = dict(p)
    q.pop('frozen')
    assert any(d in x for x in C.check_plan(g, q))


def test_graph_load_warns_and_counts_the_modules_leaninfo_must_elaborate(tmp_path, monkeypatch, capsys):
    # oaiq-047: after an upgrade across a LeanInfo.lean change, `plan` loaded the graph and re-ran
    # LeanInfo on 1259 modules one at a time for ~3 h with no output
    import shutil
    src = tmp_path / 'carve'
    shutil.copytree(FIX, src)
    recs = sorted(str(p) for p in src.rglob('*.info.json'))
    gone = recs[:2]
    saved = {p: json.load(open(p)) for p in gone}
    for p in gone:
        os.remove(p)
    by_module = {}
    for p in gone:
        rel = os.path.relpath(p, src)[:-len('.info.json')]
        by_module[rel.replace(os.sep, '.')] = saved[p]

    def fake_info(src_root, m, ws=None, use_cache=True):
        from p2mlib import leaninfo
        return leaninfo.parse(by_module[m], open(C.module_path(src_root, m), 'rb').read())
    monkeypatch.setattr(C, 'module_info', fake_info)
    monkeypatch.setattr(C, 'module_info_cached', lambda src_root, m, ws=None: False)
    g = C.Graph.load(str(src / 'decl_graph.jsonl'), str(src))
    err = capsys.readouterr().err
    assert g.nodes and '2 of' in err and 'not in the LeanInfo cache' in err
    assert 'LeanInfo 1/2' in err and 'LeanInfo 2/2' in err
    # all cached: silent
    monkeypatch.setattr(C, 'module_info_cached', lambda src_root, m, ws=None: True)
    C.Graph.load(str(src / 'decl_graph.jsonl'), str(src))
    assert 'LeanInfo' not in capsys.readouterr().err


def _carve_script():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        'carve_cli_t', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts', 'carve.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def test_cost_factors_scale_the_declarations_a_slow_piece_kept(g):
    # carve_pipeline overlap mode: a piece measured far over its plan after its statements were
    # published is split by a frozen re-plan in which only that piece's declarations cost more
    # (its measured / planned ratio), so the planner promotes lemmas inside it and nowhere else
    cli = _carve_script()
    base = cli.costs({}, g)
    k = sorted(base)[0]
    scaled = cli.costs({'cost_factors': {k: 4.0, 'not.a.node': 9.0}}, g)
    assert scaled[k] == pytest.approx(base[k] * 4.0)
    assert all(scaled[x] == base[x] for x in base if x != k)


def test_split_only_names_the_bundles_to_cut():
    # a late slow bundle is split alone (carve_pipeline): the target is the budget, but only the
    # bundles calibrate named are cut, not every bundle measured over the budget
    cli = _carve_script()
    bundles = [{'name': 'X0', 'nodes': []}, {'name': 'X1', 'nodes': []}, {'name': 'X2', 'nodes': []}]
    times = {'bundle:X0': {'secs': 70.0, 'ok': True}, 'bundle:X1': {'secs': 150.0, 'ok': True},
             'bundle:X2': {'secs': 20.0, 'ok': True}}
    assert cli.bundles_to_split(bundles, times, 55.0, None) == ['X0', 'X1']
    assert cli.bundles_to_split(bundles, times, 55.0, ['X1']) == ['X1']


def test_splitting_one_bundle_leaves_every_file_that_does_not_import_it_unchanged(g):
    # carve_pipeline (dbenbenn 2026-10-29): a late slow bundle is split alone; every other bundle keeps
    # its declarations, name and imports, so gen writes it byte for byte and its measured time stays
    # valid; only the bundles, statements and pieces importing it change
    cost = C.size_costs(g, bytes_per_second=10000)
    p = C.make_plan(g, TARGETS, budget=0.05, piece_size=10**6, bundle_budget=0.05, bundle_size=10**6,
                    cost=cost, bundle_prefix='S', chunker='schedule')
    big = max(p['bundles'], key=lambda b: len(b['nodes']))
    times = {'bundle:' + b['name']: {'secs': 100.0 if b is big else 10.0, 'ok': True} for b in p['bundles']}
    q = C.split_bundles(g, p, [big['name']], C.calibrate_costs(cost, p['bundles'], times, 1.5, 5.0), 60.0, 'S')
    old = {b['name']: b for b in p['bundles']}
    new = {b['name']: b for b in q['bundles']}
    assert len(q['bundles']) > len(p['bundles'])

    def reaches(names, seen=()):
        return any(i == big['name'] or (i not in seen and reaches(old[i]['imports'], seen + (i,))) for i in names)
    kept = [n for n in old if n != big['name'] and not reaches(old[n]['imports'])]
    importers = [n for n in old if n != big['name'] and reaches(old[n]['imports'])]
    assert kept and importers
    assert all(new[n]['imports'] == old[n]['imports'] and new[n]['nodes'] == old[n]['nodes'] for n in kept)
    for kind in ('pieces', 'stubs'):
        for n, x in p[kind].items():
            if big['name'] not in x['bundles'] and not reaches(x['bundles']):
                assert q[kind][n]['bundles'] == x['bundles']
    assert C.check_plan(g, q) == []


def test_stub_and_piece_imports_restore_a_bundle_edge_the_real_text_lacks():
    # oaiq-010/oaiq-120: the plan had B008 -> B004, so the statements needing `holderShift` (in B004) imported
    # B008 alone; the published B008 had that import cut (an unused definitions import), and the three
    # statements failed to publish with "Unknown identifier `holderShift`". Imports follow the real texts.
    plan = {'bundles': [{'name': 'B004', 'imports': []}, {'name': 'B005', 'imports': []},
                        {'name': 'B008', 'imports': ['B004', 'B005']}],
            'stubs': {'s': {'bundles': ['B008']}, 't': {'bundles': ['B004']}},
            'pieces': {'s': {'bundles': ['B008'], 'keep': []}}}
    real = {'B004': [], 'B005': [], 'B008': ['B005']}
    new = C.restore_cut_bundle_imports(plan, real)
    assert new['stubs']['s']['bundles'] == ['B004', 'B008']
    assert new['pieces']['s']['bundles'] == ['B004', 'B008']
    assert new['stubs']['t']['bundles'] == ['B004']
    assert [b['imports'] for b in new['bundles']] == [[], [], ['B005']]
    assert plan['stubs']['s']['bundles'] == ['B008']          # the input is not changed
    assert C.restore_cut_bundle_imports(plan, {'B004': [], 'B005': [], 'B008': ['B004', 'B005']}) is plan
    # only what the file needs: a published piece that never used B004 keeps its text (frozen)
    need = lambda kind, n: {'B008'} if kind == 'pieces' else {'B004', 'B008'}
    new = C.restore_cut_bundle_imports(plan, real, need)
    assert new['stubs']['s']['bundles'] == ['B004', 'B008'] and new['pieces']['s']['bundles'] == ['B008']


def test_make_plan_builds_the_available_name_set_once():
    # oaiq-098 (PlanarPacking, 564k declarations): `ok_node` rebuilt `B | set(ext)` on every call, an O(|B|)
    # union inside the promotion loop, and `plan` ran for over 5 hours. The set is built once, outside it.
    import inspect
    src = inspect.getsource(C.make_plan)
    inner = src[src.index('def ok_node'):src.index('def fresh')]
    assert 'B | set(ext)' not in inner and '| set(' not in inner


# ---------------------------------------------------------------- oaiq-081..124 (2026-10-30)

def _tiny_plan(g, targets, prefix, **kw):
    """A plan of small bundles; `budget` large keeps each target's chain in one piece."""
    args = dict(budget=0.05, piece_size=10**6, bundle_budget=0.005, bundle_size=10**6,
                cost=C.size_costs(g, bytes_per_second=10000), bundle_prefix=prefix)
    args.update(kw)
    return C.make_plan(g, targets, **args)


DUP, DUP1 = 'CD.Dup.bound', 'CD.Dup.bound_dup1'


def test_a_theorem_two_modules_declare_is_one_node_per_copy(g):
    # oaiq-088/090/095/096: Lean imports DupA's and DupZ's `CD.Dup.bound` together (same type) and
    # keeps one constant (DupZ's: imported first); the name-keyed graph had one node, and a piece
    # holding DupUseZ and DupA used DupA's copy before it was declared ("Unknown identifier").
    # DeclGraph records the other module's copy (`dup`); DupA has more importers, so it keeps the
    # name and DupZ's copy is renamed, with the references that mean it.
    dups = []
    consts, _, _ = C.load_decl_graph(os.path.join(FIX, 'decl_graph.jsonl'), dups)
    assert consts[DUP]['m'] == 'CarveDev.DupZ'
    # (InstB's anonymous `Prop` instance, identical to InstA's, is a `dup` record too; it stays one
    # node, as before: Carver._reactivate emits another module's copy again where it is used)
    assert sorted((x['n'], x['m']) for x in dups) == [(DUP, 'CarveDev.DupA'),
                                                      ('CD.LI.instPropCOfNatNat', 'CarveDev.InstB')]
    assert g.duplicates == [(DUP, 'CarveDev.DupA', [('CarveDev.DupZ', DUP1)], [])]
    assert g.nodes[DUP].module == 'CarveDev.DupA' and g.nodes[DUP1].module == 'CarveDev.DupZ'
    for user in ('CD.Dup.useZ', "CD.Dup.useZ'"):
        assert DUP1 in g.nodes[user].deps and DUP not in g.nodes[user].deps
    for user in ('CD.Dup.useA', 'CD.Dup.useA2'):
        assert DUP in g.nodes[user].deps and DUP1 not in g.nodes[user].deps
    assert C.collision_renames(g)[DUP1] == 'bound_dup1'
    assert g.dup_alias == {'CarveDev.DupZ': {DUP: DUP1}, 'CarveDev.DupUseZ': {DUP: DUP1}}


def test_a_piece_holding_both_copies_declares_each_under_its_own_name(g):
    p = _tiny_plan(g, ['CD.Dup.dupMain'], 'DUP', budget=1000)
    assert C.check_plan(g, p) == []
    assert p['nodes'] == ['CD.Dup.dupMain']
    txt = C.gen_piece(g, p, 'CD.Dup.dupMain')
    z = _section(txt, 'CarveDev.DupZ')
    assert 'theorem bound_dup1 (n : Nat)' in z, txt
    assert 'CD.Dup.bound_dup1 (n + 1)' in _section(txt, 'CarveDev.DupUseZ'), txt
    keep = {'CD.Dup.useZ', DUP1}
    uz = _section(C.Carver(g).carve(keep, g.have_names(keep), rename=C.collision_renames(g)),
                  'CarveDev.DupUseZ')
    assert 'theorem useZ (n : Nat) : n ≤ n + 1 := bound_dup1 n' in uz, uz
    # DupA's copy and its users keep the name, wherever they are carved
    assert 'theorem bound (n : Nat) : n ≤ n + 1 := Nat.le_succ n' in _section(txt, 'CarveDev.DupA')
    assert 'useA (n : Nat) : n ≤ n + 1 := bound n' in _section(txt, 'CarveDev.DupUseA')
    # the topological order alone put DupUseA before DupZ, the environment's copy: the old failure
    assert txt.index('-- module CarveDev.DupA') < txt.index('-- module CarveDev.DupUseA')


def test_duplicates_without_dup_records_are_read_from_the_commands(tmp_path):
    # a decl graph recorded before DeclGraph wrote `dup` records: the copy is found by its command
    # (DupA's declares a name the environment puts in DupZ), its value's dependencies unknown
    lines = [l for l in open(os.path.join(FIX, 'decl_graph.jsonl'), encoding='utf-8') if '"dup":true' not in l]
    old = tmp_path / 'decl_graph.jsonl'
    old.write_text(''.join(lines), encoding='utf-8')
    g2 = C.Graph.load(str(old), FIX)
    assert g2.duplicates == [(DUP, 'CarveDev.DupA', [('CarveDev.DupZ', DUP1)], ['CarveDev.DupA'])]
    assert DUP1 in g2.nodes["CD.Dup.useZ'"].deps and DUP in g2.nodes['CD.Dup.useA2'].deps


def test_a_simp_lemma_a_module_never_saw_is_hidden_in_its_section(g):
    # oaiq-081 (SubexponentialSAT, ~40 hand patches): SimpLate's `@[simp] h_eq`, bundle material
    # (attributed), closed SimpUse's `simp` early in a piece holding both; SimpUse never imported it
    p = _tiny_plan(g, ['CD.Sp.simpTop'], 'SP', budget=1000)
    files = [C.gen_piece(g, p, n) for n in p['nodes']] + [C.gen_bundle(g, p, b['name']) for b in p['bundles']]
    use = [f for f in files if '-- module CarveDev.SimpUse' in f]
    assert use
    for f in use:
        sec = _section(f, 'CarveDev.SimpUse')
        assert 'attribute [-simp] _root_.CD.Sp.h_eq' in sec, f
    for f in files:
        if '-- module CarveDev.SimpLate' in f:
            assert '[-simp]' not in _section(f, 'CarveDev.SimpLate')
    # never a library lemma, and only where a kept declaration calls the default simp set
    assert all(re.findall(r'\[-simp\] (.*)', f) in ([], ['_root_.CD.Sp.h_eq']) for f in files)
    # imported (from a bundle) rather than kept earlier: hidden all the same
    txt = C.Carver(g).carve({'CD.Sp.use'}, g.have_names({'CD.Sp.use', 'CD.Sp.h', 'CD.Sp.h_eq'}))
    assert 'attribute [-simp] _root_.CD.Sp.h_eq' in _section(txt, 'CarveDev.SimpUse')
    # not imported: nothing to hide (and naming it would be an unknown constant)
    txt = C.Carver(g).carve({'CD.Sp.use'}, g.have_names({'CD.Sp.use', 'CD.Sp.h'}))
    assert '[-simp]' not in txt


def test_a_notation_written_with_a_section_variable_reads_it_as_the_variable(g):
    # oaiq-081: `local notation "seeded" => … run.output`, `run` a section variable, recorded by
    # LeanInfo as the theorem `run` of the namespace: the stub dropped `seeded` (and `both`, written
    # with it), and the target `run` renamed `run_oai` turned the field into `run.run_oai`
    assert 'CD.NV.run' not in g.nodes['CD.NV.uses'].deps
    p = _tiny_plan(g, ['CD.NV.uses', 'CD.NV.both_run'], 'NV')
    stub = C.gen_stub(g, p, 'CD.NV.uses')
    assert 'local notation "seeded"' in stub and 'local notation "both"' in stub, stub
    keep = set(p['pieces']['CD.NV.uses']['keep']) | {'CD.NV.run'}
    txt = C.Carver(g).carve(keep, g.have_names(keep | {k for b in p['bundles'] for k in b['nodes']}),
                            rename={'CD.NV.run': 'run_oai'})
    from p2mlib.leantext import strip
    body = strip(txt)
    assert 'theorem run_oai' in body and 'run.run_oai' not in body and 'run.output' in body, txt


def test_an_export_in_a_block_without_declarations_stays(g):
    # oaiq-081: `namespace PA / export PolynomialAlgorithm (denote) / end PA` went with its block,
    # which holds no declaration, and the piece's `PA.denote` was unknown
    p = _tiny_plan(g, ['CD.NV.denote_zero'], 'EX')
    for txt in (C.gen_piece(g, p, 'CD.NV.denote_zero'), C.gen_stub(g, p, 'CD.NV.denote_zero')):
        assert 'export PolyAlg (denote)' in txt, txt


def test_a_library_coercion_local_instance_comes_back(g):
    # oaiq-096 (`Wiener`): `local instance : Coe (E → ℝ) (E → ℂ)` leaves no constant and no instance
    # problem, so nothing brought it back; it was in force for every declaration of its section
    p = _tiny_plan(g, ['CD.CL.coerced'], 'CO')
    for txt in (C.gen_piece(g, p, 'CD.CL.coerced'), C.gen_stub(g, p, 'CD.CL.coerced')):
        sec = _section(txt, 'CarveDev.CoeLocal') if '-- module' in txt else txt
        m = re.search(r'local instance \S+ : Coe \(Nat → Nat\) \(Nat → Int\)', sec)
        assert m and m.start() < sec.index('theorem coerced'), sec


def test_a_local_attribute_of_an_imported_declaration_is_applied_again(g):
    # oaiq-096: `@[local gcongr] theorem norm_lt_norm_of_nonneg` kept in a bundle; the attribute ends
    # with the bundle's section, so `gcongr` in the piece "did not make progress". Here `@[local
    # simp] k_eq` (attributed, so bundle material) and `uses_k := by simp`.
    p = _tiny_plan(g, ['CD.CL.uses_k'], 'LA')
    assert any('CD.CL.k_eq' in b['nodes'] for b in p['bundles'])
    sec = _section(C.gen_piece(g, p, 'CD.CL.uses_k'), 'CarveDev.CoeLocal')
    assert 'attribute [local simp] _root_.CD.CL.k_eq\ntheorem uses_k' in sec, sec
    # the statement does not call simp: nothing to apply there
    assert 'attribute [local simp]' not in C.gen_stub(g, p, 'CD.CL.uses_k')


def test_a_theorem_with_universes_only_under_max_is_not_made_a_statement(g):
    # oaiq-124: `{σ : Type (max us v)}` (`us` nowhere bare): WA "stuck at solving universe
    # constraint"; the carver keeps such a theorem inside its importers' pieces
    assert g.consts['CD.UM.maxOnly']['mu'] == ['u', 'v']
    assert 'mu' not in g.consts['CD.UM.bare']
    assert C.max_only_universes(g, 'CD.UM.umTop') == ['v']
    p = C.make_plan(g, ['CD.UM.umTop'], budget=0.0001, piece_size=10**6, bundle_budget=0.005,
                    bundle_size=10**6, cost=C.size_costs(g, bytes_per_second=10000), bundle_prefix='UM')
    assert 'CD.UM.bare' in p['nodes'] and 'CD.UM.maxOnly' not in p['nodes']
    assert p['max_only_universes'] == {'CD.UM.umTop': ['v']}


@pytest.mark.lean
def test_duplicates_simp_leaks_notations_coercions_and_local_attributes_compile(g, tmp_path):
    for i, (targets, prefix) in enumerate([
            (['CD.Dup.dupMain'], 'DUP'), (['CD.Sp.simpTop'], 'SP'),
            (['CD.NV.uses', 'CD.NV.both_run'], 'NV'), (['CD.CL.coerced', 'CD.CL.uses_k'], 'CO')]):
        d = tmp_path / str(i)
        d.mkdir()
        _compile_in_publish_order(g, _tiny_plan(g, targets, prefix), d)
    # the max-only universes: every file compiles, and only the target umTop (its `v` only under
    # `max`, which make_plan warns about) fails the verifier's check, as oaiq-124's statement did;
    # maxOnly, never made a statement, does not
    d = tmp_path / 'um'
    d.mkdir()
    p = _tiny_plan(g, ['CD.UM.umTop'], 'UM', budget=0.0001)
    assert 'CD.UM.maxOnly' not in p['nodes']
    with pytest.raises(C.CarveError, match=r'(?s)Chk_CD_UM_umTop.*oaiq-124'):
        _compile_in_publish_order(g, p, d)


def test_make_plan_computes_each_pieces_bundle_closure_once():
    # oaiq-098: `{k for k in B if bidx[k] in _bundle_closure(bimp, bks)}` ran the closure once per element of B
    # (564k) for every statement; `plan` then ran for hours. The closure is computed once per piece.
    import inspect
    src = inspect.getsource(C.make_plan)
    assert 'in _bundle_closure(' not in src
