"""p2mlib.splitrun: publishing a carved split in waves, against a fake platform (no live writes)."""
import json
import os

import pytest

from p2mlib import splitrun as R

# a two-bundle chain, two statements, two pieces; `top` is external (someone else's statement)
PLAN = {
    'bundles': [{'name': 'XB000', 'imports': [], 'nodes': ['A.d']},
                {'name': 'XB001', 'imports': ['XB000'], 'nodes': ['A.e']}],
    'stubs': {'A.low': {'bundles': ['XB000']}, 'A.mid': {'bundles': ['XB001']}},
    'pieces': {'A.low': {'bundles': ['XB000'], 'imports': []},
               'A.mid': {'bundles': ['XB001'], 'imports': ['A.low']},
               'A.top': {'bundles': ['XB001'], 'imports': ['A.mid']}},
    'external': ['A.top'], 'statement_suffix': '_s2',
}
EXPL = ('The statement is\n\n$$x = x$$\n\nand it holds by reflexivity of equality, which is all the '
        'proof uses; the carved file states it, imports the bundle that defines the objects, and '
        'closes the goal with `rfl` after unfolding the definitions involved in the claim.\n')


@pytest.fixture
def split(tmp_path):
    d = tmp_path
    (d / 'out' / 'lib').mkdir(parents=True)
    (d / 'out' / 'solutions').mkdir()
    (d / 'prose').mkdir()
    (d / 'explanations').mkdir()
    for b in ('XB000', 'XB001'):
        (d / 'out' / 'lib' / ('Def_%s.lean' % b)).write_text('import Mathlib\n\ndef %s.k : Nat := 1\n' % b)
        (d / 'prose' / ('%s.md' % b)).write_text('---\ntitle: Bundle %s\n---\n\nDefinitions.\n' % b)
    for n in ('A_low_s2', 'A_mid_s2'):
        (d / 'out' / 'lib' / ('Thm_%s.lean' % n)).write_text(
            'import Mathlib\nimport Definitions.Def_XB000\n\ntheorem %s : True := by\n  sorry\n' % n)
        (d / 'prose' / ('%s.md' % n)).write_text('---\ntitle: Lemma %s\n---\n\nIt holds.\n' % n)
    for n in ('A_low_s2', 'A_mid_s2', 'A_top'):
        (d / 'out' / 'solutions' / ('Sol_%s.lean' % n)).write_text('import Mathlib\n\ntheorem solution : True := trivial\n')
        (d / 'explanations' / ('%s.md' % n)).write_text(EXPL)
    (d / 'plan.json').write_text(json.dumps(PLAN))
    cfg = {'plan': str(d / 'plan.json'), 'out': str(d / 'out'), 'prose': str(d / 'prose'),
           'explanations': str(d / 'explanations'), 'state': str(d / 'run_state.json'),
           'log': str(d / 'PROGRESS.log'), 'source': 'OpenAI, openai/math family 159', 'tags': ['t'],
           'jobs': 8}
    return d, cfg


class FakeApi:
    """The platform: publish jobs finish on the next poll, verdicts on the next poll. `script` maps
    an item name to the (status, error) results it gets, in order, then success."""

    def __init__(self, script=None, published=None):
        self.script = {k: list(v) for k, v in (script or {}).items()}
        self.published = dict(published or {'A.top': 'TOP'})    # name -> id
        self.posted, self.jobs, self.subs, self.n = [], {}, {}, 0
        self.proved = set()
        self.foreign, self.texts, self.proofs = {}, {}, {}

    def live_proofs(self, name):
        """The live proofs of the theorem `name`: [{id, author, status, content}]."""
        return [dict(x) for x in self.proofs.get(name, [])]

    def _next(self, name, ok):
        s = self.script.get(name)
        return s.pop(0) if s else ok

    def theorem_id(self, name):
        return self.published.get(name)

    def existing(self, kind, name):
        """The live record under `name` (kind 'statement' or 'bundle'), or None. An item published
        by name without recorded text (`published`) reads as exactly ours; `foreign` holds someone
        else's records."""
        if name in self.foreign:
            return dict(self.foreign[name])
        if name not in self.published:
            return None
        return dict(self.texts.get(name, {'same': True}), id=self.published[name], author='dbenbenn')

    def submit_definition(self, body):
        assert body['definition'].startswith('import') and body['definition_title']
        # prove.md: a definition may import a platform theorem only once it is Proved
        for imp in body['definition'].split('\n'):
            if imp.startswith('import Theorems.Thm_'):
                assert imp[len('import Theorems.Thm_'):] in self.proved, \
                    'Imported platform theorems must be Proved at submission time'
        self.posted.append(('def', body['definition_name']))
        self.n += 1
        self.jobs['j%d' % self.n] = ('def', body['definition_name'])
        return 'j%d' % self.n

    def submit_problems(self, problems):
        out = []
        for p in problems:
            assert p['formal_statement'].lstrip().startswith('theorem') and p['preamble'].startswith('import')
            for imp in p['preamble'].split('\n'):
                if imp.startswith('import Definitions.Def_'):
                    assert imp[len('import Definitions.Def_'):] in self.published, 'statement before its bundle'
            self.posted.append(('thm', p['theorem_name']))
            self.n += 1
            self.jobs['j%d' % self.n] = ('thm', p['theorem_name'])
            out.append('j%d' % self.n)
        return out

    def job(self, jid):
        kind, name = self.jobs[jid]
        st, err = self._next(name, ('PUBLISHED', None))
        if st == 'PUBLISHED':
            self.published[name] = 'id-' + name
            return {'status': st, 'theorem_id': 'id-' + name}
        return {'status': st, 'error_message': err}

    def verify(self, tid, path, explanation):
        assert tid in self.published.values(), 'piece before its statement'
        assert len(explanation) >= 200
        name = next(n for n, i in self.published.items() if i == tid)
        self.posted.append(('verify', name))
        self.n += 1
        self.subs['s%d' % self.n] = name
        return 's%d' % self.n

    def verdict(self, sid):
        st, err = self._next('verify:' + self.subs[sid], ('ACCEPTED', None))
        if st == 'ACCEPTED':
            self.proved.add(self.subs[sid].replace('.', '_'))
        return {'status': st, 'error_message': err}


def run(cfg, api):
    r = R.Runner(cfg, api, sleep=lambda s: None)
    return r, r.run()


def test_publishes_in_dependency_order_and_records_ids(split):
    d, cfg = split
    api = FakeApi()
    r, summary = run(cfg, api)
    order = [x for x in api.posted]
    assert order.index(('def', 'XB000')) < order.index(('def', 'XB001'))
    assert order.index(('def', 'XB000')) < order.index(('thm', 'A.low_s2'))
    assert order.index(('thm', 'A.low_s2')) < order.index(('verify', 'A.low_s2'))
    assert ('thm', 'A.top') not in order                      # external: not ours to publish
    assert ('verify', 'A.top') in order                       # but its proof is
    st = json.loads((d / 'run_state.json').read_text())
    assert st['bundle:XB001']['state'] == 'live' and st['bundle:XB001']['id'] == 'id-XB001'
    assert st['piece:A.top']['state'] == 'live'
    assert summary['live'] == 7 and not summary['stopped']
    log = (d / 'PROGRESS.log').read_text()
    assert '  XB000  publish  PUBLISHED id-XB000' in log


def test_a_rerun_posts_nothing(split):
    d, cfg = split
    run(cfg, FakeApi())
    api = FakeApi()
    run(cfg, api)
    assert api.posted == []


def test_already_published_items_are_adopted_not_reposted(split):
    d, cfg = split
    api = FakeApi(published={'A.top': 'TOP', 'XB000': 'old0'})
    run(cfg, api)
    assert ('def', 'XB000') not in api.posted
    st = json.loads((d / 'run_state.json').read_text())
    assert st['bundle:XB000']['id'] == 'old0'


def test_transient_failures_retry_unchanged(split):
    d, cfg = split
    cold = ('ERROR', 'Internal error while publishing: Module compilation timed out after 300s.')
    api = FakeApi(script={'XB001': [cold, cold]})
    r, summary = run(cfg, api)
    assert api.posted.count(('def', 'XB001')) == 3
    assert summary['live'] == 7


def test_own_timeouts_end_in_split_and_block_dependents(split):
    d, cfg = split
    own = ('FAILED', 'Compilation timed out after 300s')
    api = FakeApi(script={'XB001': [own, own, own]})
    r, summary = run(cfg, api)
    assert api.posted.count(('def', 'XB001')) == 3            # two retries, then the verdict
    st = json.loads((d / 'run_state.json').read_text())
    assert st['bundle:XB001']['state'] == 'split'
    assert ('thm', 'A.mid_s2') not in api.posted
    assert st['piece:A.low']['state'] == 'live'                # independent work went ahead
    assert 'bundle:XB001' in summary['stopped']
    assert 'NEEDS A PERSON: own compile timeout' in (d / 'PROGRESS.log').read_text()


def test_a_wrong_answer_stops_for_a_person(split):
    d, cfg = split
    api = FakeApi(script={'verify:A.low_s2': [('WA', 'solution does not match')]})
    r, summary = run(cfg, api)
    assert api.posted.count(('verify', 'A.low_s2')) == 1
    st = json.loads((d / 'run_state.json').read_text())
    assert st['piece:A.low']['state'] == 'stop'
    assert summary['stopped'] == ['piece:A.low']


def test_missing_or_bad_prose_blocks_the_item_before_any_post(split):
    d, cfg = split
    os.remove(d / 'prose' / 'A_mid_s2.md')
    (d / 'explanations' / 'A_low_s2.md').write_text('Too short.\n')
    api = FakeApi()
    r, summary = run(cfg, api)
    assert ('thm', 'A.mid_s2') not in api.posted
    assert ('verify', 'A.low_s2') not in api.posted
    assert set(summary['blocked']) == {'statement:A.mid', 'piece:A.low'}
    assert ('def', 'XB001') in api.posted


def test_dry_run_reads_nothing_writes_nothing(split):
    d, cfg = split

    class NoApi:
        def __getattr__(self, k):
            raise AssertionError('API used in a dry run: ' + k)
    plan = R.Runner(cfg, NoApi(), sleep=lambda s: None).dry_run(read=False)
    assert plan['ready'] == ['bundle:XB000']
    assert plan['blocked'] == {}
    assert not (d / 'run_state.json').exists()


def test_in_flight_items_are_polled_after_a_restart_not_resubmitted(split):
    d, cfg = split
    api = FakeApi()
    r = R.Runner(cfg, api, sleep=lambda s: None)
    r.step()                                                  # submits XB000, does not poll yet
    assert api.posted == [('def', 'XB000')]
    r2 = R.Runner(cfg, api, sleep=lambda s: None)             # a new process, same state file
    r2.run()
    assert api.posted.count(('def', 'XB000')) == 1


def test_a_refused_post_stops_that_item_only(split):
    d, cfg = split

    class Refusing(FakeApi):
        def submit_definition(self, body):
            if body['definition_name'] == 'XB001':
                raise RuntimeError('submit-definition: {"__error": "422 comments in a frozen field"}')
            return FakeApi.submit_definition(self, body)
    api = Refusing()
    r, summary = run(cfg, api)
    st = json.loads((d / 'run_state.json').read_text())
    assert st['bundle:XB001']['state'] == 'stop' and '422' in st['bundle:XB001']['last']
    assert st['piece:A.low']['state'] == 'live'
    assert summary['stopped'] == ['bundle:XB001']


def test_command_line_is_a_dry_run_without_go(split, capsys):
    import sys
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts'))
    import split_run
    d, cfg = split
    (d / 'run.json').write_text(json.dumps(cfg))
    split_run.main([str(d / 'run.json'), '--offline'])
    out = capsys.readouterr().out
    assert 'DRY RUN' in out and 'bundle:XB000' in out
    assert not (d / 'run_state.json').exists()


def test_kinds_and_max_items_limit_a_run(split):
    d, cfg = split
    api = FakeApi()
    r, summary = run(dict(cfg, kinds=['bundle'], max_items=1), api)
    assert api.posted == [('def', 'XB000')]                   # one bundle, then stop sending
    api2 = FakeApi(published=dict(api.published))
    run(dict(cfg, kinds=['bundle']), api2)
    assert [p for p in api2.posted if p[0] != 'def'] == []    # only bundles
    assert ('def', 'XB001') in api2.posted


def test_bundles_go_before_statements_and_pieces(split):
    # the bundle chain is the critical path: a ready bundle never waits behind statements or pieces
    d, cfg = split
    api = FakeApi()
    r = R.Runner(dict(cfg, jobs=1), api, sleep=lambda s: None)
    r.step()                                                  # XB000
    r.step()                                                  # XB000 live; XB001 and A.low_s2 ready
    assert api.posted[-1] == ('def', 'XB001')


def test_a_bundle_importing_a_statement_waits_for_its_accepted_proof(split):
    # carve's bundles_import_statements: XB001 imports the statement A.low, which the platform
    # allows only once A.low is Proved (2026-10-18). publish_order makes the bundle wait for the
    # piece, and the runner follows it.
    d, cfg = split
    plan = json.loads(json.dumps(PLAN))
    plan['bundles'][1]['statements'] = ['A.low']
    (d / 'plan.json').write_text(json.dumps(plan))
    (d / 'out' / 'lib' / 'Def_XB001.lean').write_text(
        'import Mathlib\nimport Definitions.Def_XB000\nimport Theorems.Thm_A_low_s2\n\ndef XB001.k : Nat := 1\n')
    api = FakeApi()
    r, s = run(cfg, api)
    assert s['live'] == len(r.items)
    assert api.posted.index(('verify', 'A.low_s2')) < api.posted.index(('def', 'XB001'))


def test_a_statement_name_taken_by_a_different_statement_is_a_hard_stop(split):
    # KervaireMixing 2026-10-18: `phase_upper_of_fixed` was Shuze Chen's, with their own bundles;
    # split_run adopted it by name and our pieces imported it, colliding with our bundle. A live
    # name with other text now stops the whole run before anything is posted (Boone-Higman
    # 2026-10-24: a regenerated frozen bundle that differs from its published text is the same case)
    d, cfg = split
    api = FakeApi()
    api.foreign['A.low_s2'] = {'id': 'theirs', 'author': 'Shuze Chen',
                               'preamble': 'import Mathlib\nimport Definitions.Def_Theirs',
                               'formal_statement': 'theorem A_low_s2 : True := by\n  sorry\n'}
    with pytest.raises(R.LiveMismatch) as e:
        run(cfg, api)
    msg = str(e.value)
    assert 'statement A.low_s2' in msg and 'Shuze Chen' in msg and 'theirs' in msg
    assert 'statement_suffix' in msg and 'carve.py gen' in msg
    assert api.posted == []
    assert 'LIVE TEXT DIFFERS' in (d / 'PROGRESS.log').read_text()


def test_an_exact_match_is_adopted_whitespace_aside(split):
    d, cfg = split
    api = FakeApi()
    api.foreign['A.low_s2'] = {'id': 'ours-before', 'author': 'dbenbenn',
                               'preamble': 'import Definitions.Def_XB000\nimport Mathlib\n',
                               'formal_statement': 'theorem A_low_s2 :   True := by\n    sorry'}
    run(cfg, api)
    st = json.loads((d / 'run_state.json').read_text())
    assert st['statement:A.low']['state'] == 'live' and st['statement:A.low']['id'] == 'ours-before'


def test_a_bundle_name_taken_by_a_different_definition_is_a_hard_stop(split):
    d, cfg = split
    api = FakeApi()
    api.foreign['XB001'] = {'id': 'd1', 'author': 'Someone', 'definition': 'import Mathlib\n\ndef other : Nat := 2\n'}
    with pytest.raises(R.LiveMismatch) as e:
        run(cfg, api)
    assert 'definitions bundle XB001' in str(e.value) and 'd1' in str(e.value)
    assert api.posted == []                                   # not even the independent XB000
    api2 = FakeApi()
    api2.foreign['XB000'] = {'id': 'd0', 'author': 'dbenbenn', 'definition': 'import Mathlib\n\ndef  XB000.k : Nat := 1'}
    run(cfg, api2)
    st = json.loads((d / 'run_state.json').read_text())
    assert st['bundle:XB000']['state'] == 'live' and st['bundle:XB000']['id'] == 'd0'


def test_live_items_of_an_extended_carve_are_adopted_without_their_prose(split):
    # Extending a published carve (Boone-Higman option (c), 2026-10-24): the new carve's fresh run
    # state would have re-posted the five live bundles; the agent seeded the state by hand. Every
    # bundle and statement already live under its name with our text is adopted before anything
    # is posted, and needs no prose (that belongs to the run that published it).
    d, cfg = split
    for n in ('XB000', 'XB001', 'A_low_s2'):
        os.remove(d / 'prose' / ('%s.md' % n))
    api = FakeApi(published={'A.top': 'TOP', 'XB000': 'b0', 'XB001': 'b1', 'A.low_s2': 's0'})
    api.texts['XB001'] = {'definition': (d / 'out' / 'lib' / 'Def_XB001.lean').read_text()}
    r, summary = run(cfg, api)
    assert [p for p in api.posted if p[0] != 'verify'] == [('thm', 'A.mid_s2')]
    st = json.loads((d / 'run_state.json').read_text())
    assert [st[x]['id'] for x in ('bundle:XB000', 'bundle:XB001', 'statement:A.low')] == ['b0', 'b1', 's0']
    assert summary['live'] == 7 and not summary['blocked']
    assert '  XB001  adopt  b1' in (d / 'PROGRESS.log').read_text()


def test_dry_run_reads_the_platform_and_reports_adoptions_without_writing(split):
    d, cfg = split

    class ReadOnly(FakeApi):
        def submit_definition(self, body):
            raise AssertionError('dry run posted')
        submit_problems = verify = submit_definition
    api = ReadOnly(published={'A.top': 'TOP', 'XB000': 'b0'})
    plan = R.Runner(cfg, api, sleep=lambda s: None).dry_run()
    assert plan['adopt'] == {'bundle:XB000': 'b0'} and plan['mismatch'] == []
    assert plan['ready'] == ['bundle:XB001', 'statement:A.low']
    assert not (d / 'run_state.json').exists() and not (d / 'PROGRESS.log').exists()
    api.foreign['XB001'] = {'id': 'd1', 'author': 'Someone', 'definition': 'def other : Nat := 2\n'}
    plan = R.Runner(cfg, api, sleep=lambda s: None).dry_run()
    assert [m['name'] for m in plan['mismatch']] == ['XB001']


def test_a_piece_whose_proof_is_live_with_our_text_is_adopted(split):
    # Boone-Higman option (c): the first carve's pieces were accepted; a fresh run state would
    # have sent them again (post_verify then refuses, as a stop). Our exact source live: adopted.
    d, cfg = split
    sol = (d / 'out' / 'solutions' / 'Sol_A_low_s2.lean').read_text()
    api = FakeApi(published={'A.top': 'TOP', 'XB000': 'b0', 'A.low_s2': 's0'})
    api.proofs['A.low_s2'] = [{'id': 'sub0', 'author': 'dbenbenn', 'status': 'ACCEPTED', 'content': sol + '\n'}]
    api.proofs['A.top'] = [{'id': 'other', 'author': 'wurtle', 'status': 'SKETCH_ACCEPTED',
                            'content': 'theorem solution : True := by\n  exact trivial\n'}]
    plan = R.Runner(cfg, api, sleep=lambda s: None).dry_run()
    assert plan['adopt']['piece:A.low'] == 'sub0'
    assert plan['proved_elsewhere'] == {'piece:A.top': ['other (SKETCH_ACCEPTED, wurtle)']}
    r, summary = run(cfg, api)
    assert ('verify', 'A.low_s2') not in api.posted
    st = json.loads((d / 'run_state.json').read_text())
    assert st['piece:A.low'] == {'state': 'live', 'id': 'sub0', 'history': {}}


def test_command_line_dry_run_reads_but_never_writes(split, capsys, monkeypatch):
    import sys
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts'))
    import split_run
    d, cfg = split
    (d / 'run.json').write_text(json.dumps(cfg))
    fake = FakeApi(published={'A.top': 'TOP', 'XB000': 'b0'})
    monkeypatch.setattr(R, 'LiveApi', lambda: fake)
    split_run.main([str(d / 'run.json')])
    out = capsys.readouterr().out
    assert 'would adopt (1): bundle:XB000 b0' in out and 'would send now (2)' in out
    assert not (d / 'run_state.json').exists()
    # the read-only wrapper refuses every write, whatever the API object offers
    with pytest.raises(RuntimeError):
        R.ReadOnly(fake).submit_definition({})


def test_a_file_the_soundness_guard_refuses_blocks_the_item_before_any_post(split):
    # WLTime (2026-10-23): bundle OAIQWWLT000 kept OpenAI's `def prelude`, and the platform's
    # soundness guard refused the token `prelude` even as an identifier ("`prelude` — disables the
    # automatic Init prelude import"): compile_error after the post. Checked locally first now.
    d, cfg = split
    (d / 'out' / 'lib' / 'Def_XB001.lean').write_text(
        'import Mathlib\n\ndef prelude (n : Nat) : Nat := n\ndef XB001.k : Nat := prelude 1\n')
    api = FakeApi()
    r, summary = run(cfg, api)
    assert ('def', 'XB001') not in api.posted
    assert 'bundle:XB001' in summary['blocked'] and 'prelude' in summary['blocked']['bundle:XB001']


def test_a_stopped_item_whose_text_changed_is_sent_again(split):
    # oaiq-065/071: after a re-split, the bundle/piece stayed in its terminal state (`split`) and was
    # never resubmitted; workers edited run_state.json by hand. The text sent is recorded, and a
    # terminal item whose file changed since starts over.
    d, cfg = split
    own = ('FAILED', 'Compilation timed out after 300s')
    first = FakeApi(script={'XB001': [own, own, own]})
    run(cfg, first)
    assert json.loads((d / 'run_state.json').read_text())['bundle:XB001']['state'] == 'split'
    api = FakeApi(published=dict(first.published))           # the platform remembers what went live
    run(cfg, api)
    assert ('def', 'XB001') not in api.posted                # unchanged: still waits for a person
    f = d / 'out' / 'lib' / 'Def_XB001.lean'
    f.write_text(f.read_text() + '\n-- re-split\n')
    api = FakeApi(published=dict(first.published))
    r, summary = run(cfg, api)
    assert ('def', 'XB001') in api.posted and not summary['stopped']
    assert 'changed since it stopped' in (d / 'PROGRESS.log').read_text()


def test_a_heartbeat_timeout_raises_the_limit_once_and_resends(split):
    # oaiq-055 (Lech): four bundles compiled in measure but the server answered "(deterministic)
    # timeout at whnf, maximum number of heartbeats (200000)"; each was parked for a person, whose fix
    # was always `set_option maxHeartbeats 1000000` after the imports and a resend
    d, cfg = split
    hb = ('FAILED', 'definition does not compile: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)')
    api = FakeApi(script={'XB001': [hb]})
    r, summary = run(cfg, api)
    assert api.posted.count(('def', 'XB001')) == 2 and not summary['stopped']
    text = (d / 'out' / 'lib' / 'Def_XB001.lean').read_text()
    assert 'set_option maxHeartbeats 1000000' in text
    assert text.index('set_option maxHeartbeats') > text.rindex('import ')
    assert 'raised maxHeartbeats' in (d / 'PROGRESS.log').read_text()


def test_a_second_heartbeat_timeout_waits_for_a_person(split):
    d, cfg = split
    hb = ('FAILED', '(deterministic) timeout at `whnf`, maximum number of heartbeats (200000)')
    api = FakeApi(script={'XB001': [hb, hb]})
    r, summary = run(cfg, api)
    st = json.loads((d / 'run_state.json').read_text())
    assert st['bundle:XB001']['state'] == 'raise_heartbeats' and api.posted.count(('def', 'XB001')) == 2
