"""stubs.py: a mission's draft statements installed as the modules the platform will publish."""
import json
import os

import pytest

import stubs
from mini import make_mission
from p2mlib import workspace as W


@pytest.fixture
def env(tmp_path):
    ws = tmp_path / 'ws'
    (ws / 'Theorems').mkdir(parents=True)
    return str(make_mission(tmp_path / 'mission')), str(ws)


def test_install_writes_published_shape_and_records_drafts(env):
    mdir, ws = env
    problems, written = stubs.sync(mdir, ws)
    assert problems == [] and sorted(written) == ['Theorems.Thm_Mini_goal', 'Theorems.Thm_Mini_t1']
    text = open(os.path.join(ws, 'Theorems', 'Thm_Mini_t1.lean')).read()
    # exactly the text fetch_theorems writes for a published statement: preamble, blank line, statement
    assert text.startswith('import Mathlib\nimport Definitions.Def_Mini\n\nnamespace Mini\n\ntheorem t1')
    assert W.drafts(ws) == {'Theorems.Thm_Mini_goal': mdir, 'Theorems.Thm_Mini_t1': mdir}
    assert W.published_by_full(ws) == {}                      # drafts are not published
    # ... except to a pre-submission audit, for which they are the siblings about to be published
    assert sorted(W.published_by_full(ws, with_drafts=True)) == ['Mini.goal', 'Mini.t1']
    assert stubs.sync(mdir, ws, check=True) == ([], [])       # current


def test_check_reports_a_stale_stub_and_install_fixes_it(env):
    mdir, ws = env
    stubs.sync(mdir, ws)
    lib = os.path.join(mdir, 'lib', 'Thm_Mini.lean')
    text = open(lib).read()
    open(lib, 'w').write(text.replace('Mini.k = 1', 'Mini.k = 1 ∧ True'))
    assert stubs.sync(mdir, ws, check=True)[0] == ['STALE Theorems.Thm_Mini_t1']
    assert stubs.sync(mdir, ws)[1] == ['Theorems.Thm_Mini_t1']
    assert '∧ True' in open(os.path.join(ws, 'Theorems', 'Thm_Mini_t1.lean')).read()


def test_a_dropped_milestone_loses_its_stub(env):
    mdir, ws = env
    stubs.sync(mdir, ws)
    lib = os.path.join(mdir, 'lib', 'Thm_Mini.lean')
    text = open(lib).read()
    open(lib, 'w').write(text.replace('theorem t1 : Mini.k = 1 := by\n  sorry\n\n', ''))
    mp = os.path.join(mdir, 'mission.py')
    s = open(mp).read()
    i = s.index("    dict(name='t1'"); j = s.index("    dict(name='goal'")
    open(mp, 'w').write(s[:i] + s[j:])
    assert stubs.sync(mdir, ws, check=True)[0] == ['LEFTOVER Theorems.Thm_Mini_t1: no longer a statement of the mission']
    stubs.sync(mdir, ws)
    assert not os.path.exists(os.path.join(ws, 'Theorems', 'Thm_Mini_t1.lean'))
    assert list(W.drafts(ws)) == ['Theorems.Thm_Mini_goal']


def test_a_published_statement_is_never_overwritten(env):
    mdir, ws = env
    pub = os.path.join(ws, 'Theorems', 'Thm_Mini_t1.lean')
    open(pub, 'w').write('import Mathlib\n\ntheorem Mini.t1 : 2 = 2 := by sorry\n')
    problems, written = stubs.sync(mdir, ws)
    assert problems == ['PUBLISHED-DIFFERS Theorems.Thm_Mini_t1: the platform has another statement under this name']
    assert written == ['Theorems.Thm_Mini_goal'] and '2 = 2' in open(pub).read()


def test_submit_refuses_a_draft_import(env, monkeypatch, tmp_path):
    import submit_solution
    mdir, ws = env
    stubs.sync(mdir, ws)
    monkeypatch.setenv('P2M_WORKSPACE', ws)
    f = tmp_path / 'Sol.lean'
    f.write_text('import Theorems.Thm_Mini_t1\n\ntheorem solution : True := trivial\n')
    with pytest.raises(SystemExit, match='draft statements not yet published'):
        submit_solution.check_no_draft_imports(str(f))
    f.write_text('import Mathlib\n\ntheorem solution : True := trivial\n')
    submit_solution.check_no_draft_imports(str(f))           # fine


def statements_layout(mdir):
    """Convert the mini mission to one statements/ file per statement (the new layout)."""
    from p2mlib.mission import load
    from p2mlib.workspace import statement_text
    M = load(mdir)
    pay = M.payloads()
    os.makedirs(os.path.join(mdir, 'statements'))
    for T in M.THEOREMS:
        open(os.path.join(mdir, 'statements', 'Thm_Mini_%s.lean' % T['name']), 'w').write(statement_text(*pay[T['name']]))
    os.remove(os.path.join(mdir, 'lib', 'Thm_Mini.lean'))
    mp = os.path.join(mdir, 'mission.py')
    s = open(mp).read()
    open(mp, 'w').write(s[:s.index('def payloads():')])
    return pay


def test_statements_layout_gives_the_same_payloads_and_stubs(env):
    mdir, ws = env
    pay = statements_layout(mdir)
    from p2mlib.mission import load
    assert load(mdir).payloads() == pay                      # the restructure changes nothing on p2m
    assert stubs.sync(mdir, ws)[0] == []


def test_verify_resolves_statement_names_in_the_statements_layout(env):
    # draft.dead_lean_refs read only lib/*.lean: after Lodha-Moore moved to statements/, every
    # statement name in the prose looked dead (BAD 12, 2026-10-02)
    import draft
    mdir, ws = env
    statements_layout(mdir)
    M = draft.load(mdir)
    its, mls, _, _ = draft.desired(M, mdir)
    its['goal']['natural_language_statement'] += ' Compare `Mini.t1`.'
    bad = draft.dead_lean_refs(M, mdir, its, mls, 'This mission formalizes a paper.', lambda *a, **k: {})
    assert not [b for b in bad if 'Mini.t1' in b[1]], bad



def test_a_stub_copied_by_hand_is_listed_and_adopted_on_request(env):
    # Erschler-Zheng (2026-10-04): implementers copied each statement into Theorems/ by hand, so the
    # files matched but were never listed as drafts; scripts then took 38 draft stubs for published
    # statements. Such a file looks exactly like a published one, so it is not a problem: `unlisted`
    # names it, and --adopt lists it as this mission's draft.
    mdir, ws = env
    stubs.sync(mdir, ws)
    W.update_drafts(remove=['Theorems.Thm_Mini_t1'], ws=ws)            # the hand-copied state
    assert stubs.sync(mdir, ws) == ([], [])
    assert stubs.unlisted(mdir, ws) == ['Theorems.Thm_Mini_t1']
    assert stubs.sync(mdir, ws, adopt=True) == ([], [])
    assert W.drafts(ws)['Theorems.Thm_Mini_t1'] == mdir and stubs.unlisted(mdir, ws) == []
