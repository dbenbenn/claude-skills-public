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
