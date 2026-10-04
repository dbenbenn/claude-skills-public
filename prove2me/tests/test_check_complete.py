"""check_complete.py: a milestone is complete when its proof is good and all it rests on is."""
import check_complete as C

MS = ['N.a', 'N.b', 'N.c', 'N.d', 'N.e', 'N.f']


def test_outright_reduction_and_missing():
    good = {'N.a': [], 'N.b': ['N.a'], 'N.c': ['N.b', 'N.d']}       # N.d has no proof
    done = C.complete(MS, good)
    assert done['N.a'] and done['N.b'] and not done['N.c'] and not done['N.d']


def test_a_cycle_is_never_complete():
    good = {'N.e': ['N.f'], 'N.f': ['N.e'], 'N.a': ['N.e']}
    done = C.complete(MS, good)
    assert not done['N.e'] and not done['N.f'] and not done['N.a']


def test_statements_outside_the_mission_do_not_block():
    # Monod's published theorem: its platform status decides, the local check lists it
    done = C.complete(MS, {'N.a': ['Monod.x']})
    assert done['N.a']


def test_check_block_outside_the_mission_namespace():
    # CFW 2026-10-03: the Blueprint's checks live in CFWPlan.Main (and CFWPlan.Main.P5), not in
    # ConnesFeldmanWeiss; the namespace-only match reported "no proof" for all 16 milestones
    ms = ['N.foo', 'N.bar']
    assert C.target_of('N.chk_foo', ms) == 'N.foo'
    assert C.target_of('Plan.Main.chk_foo', ms) == 'N.foo'
    assert C.target_of('Plan.Main.P5.chk_bar', ms) == 'N.bar'
    assert C.target_of('Plan.Main.helper', ms) is None
    assert C.target_of('Plan.chk_baz', ms) is None


def test_ambiguous_short_name_needs_the_namespace():
    ms = ['A.foo', 'B.foo']
    assert C.target_of('A.chk_foo', ms) == 'A.foo'
    assert C.target_of('Plan.chk_foo', ms) is None


def test_summary_with_and_without_a_goal():
    # markov-heat-kernels 2026-10-04: a standalone package has no GOAL, and main printed the
    # verdicts and then crashed with AttributeError: GOAL
    import types
    M = types.SimpleNamespace(NAMESPACE='N')
    line, ok = C.summary(M, {'N.a': True, 'N.b': False}, ['N.a', 'N.b'], {'N.a': []})
    assert not ok and 'no goal' in line and '1 of 2' in line
    line, ok = C.summary(M, {'N.a': True}, ['N.a'], {'N.a': []})
    assert ok
    M.GOAL = 'a'
    line, ok = C.summary(M, {'N.a': True}, ['N.a'], {'N.a': []})
    assert ok and 'goal COMPLETE' in line
    M.GOAL = 'ref:Other.b'
    line, ok = C.summary(M, {'N.a': True}, ['N.a'], {'N.a': []})
    assert not ok and 'goal not complete' in line
