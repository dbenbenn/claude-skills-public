"""draft.py: diff-based upload and verify against a fake proposal, plus its prose checks."""
import copy
import json

import pytest

import draft as D

from mini import make_mission


@pytest.fixture
def mdir(tmp_path):
    return make_mission(tmp_path)


class FakeProposal:
    """A Draft that stores what is posted; editing an item clears its confirmation, as live."""
    def __init__(self, items, miles, desc, order, goal):
        self.items, self.miles = items, miles
        self.prop = {'id': 'P', 'status': 'Draft', 'description': desc, 'item_order': order, 'main_item_id': goal}
        self.writes = []

    def call(self, m, p, b=None):
        if m == 'GET' and p == '/mission-proposals/P':
            return dict(self.prop, items=list(copy.deepcopy(self.items).values()))
        if m == 'GET' and p == '/mission-proposals/P/milestones':
            return {'milestones': [dict(item_id=k, milestone_title=t, milestone_description=d)
                                   for k, (t, d) in self.miles.items()]}
        self.writes.append((m, p))
        if m == 'POST' and p == '/mission-proposals/P/items':
            key = b.get('theorem_name') or b.get('definition_name')
            iid = next((i for i, it in self.items.items() if (it.get('theorem_name') or it.get('definition_name')) == key), 'new')
            self.items[iid] = dict(b, id=iid, confirmed_at=None)
            return {'id': iid}
        if m == 'POST' and p == '/mission-proposals/P/milestones':
            self.miles[b['item_id']] = (b['milestone_title'], b['milestone_description'])
            return {}
        if m == 'PATCH' and p == '/mission-proposals/P':
            self.prop.update(b)
            return {}
        if m == 'DELETE' and p.startswith('/mission-proposals/P/items/'):
            iid = p.rsplit('/', 1)[1]                       # live: 204, and gone from item_order
            del self.items[iid]
            self.miles.pop(iid, None)
            self.prop['item_order'] = [i for i in self.prop['item_order'] if i != iid]
            return {}
        raise AssertionError((m, p))


def live_from_repo(mdir):
    """A fake Draft identical to the repo, every item confirmed."""
    M = D.load(str(mdir))
    items, miles, order, desc = D.desired(M, str(mdir))
    ids = {k: 'i_' + k.replace(':', '_') for k in items}
    live = {ids[k]: dict(v, id=ids[k], confirmed_at='2026-10-02') for k, v in items.items()}
    lm = {ids[k]: v for k, v in miles.items()}
    (mdir / 'proposal.json').write_text(json.dumps({'id': 'P', 'items': ids}))
    return FakeProposal(live, lm, desc, [ids[k] for k in order], ids[M.GOAL]), ids


def test_identical_draft_has_no_diff(mdir):
    fake, _ = live_from_repo(mdir)
    bad, _, _ = D.diff(D.load(str(mdir)), str(mdir), fake.call, json.loads((mdir / 'proposal.json').read_text()))
    assert bad == []


def test_one_changed_field_is_exactly_one_diff(mdir):
    fake, ids = live_from_repo(mdir)
    fake.items[ids['t1']]['natural_language_statement'] = 'Something else.'
    fake.prop['description'] = 'old text'
    bad, _, _ = D.diff(D.load(str(mdir)), str(mdir), fake.call, json.loads((mdir / 'proposal.json').read_text()))
    assert sorted(bad) == [('description', 'text'), ('t1', 'natural_language_statement')]


def run_upload(mdir, fake, monkeypatch, *flags):
    import p2m
    # upload --go installs the statement stubs (stubs.sync) in $P2M_WORKSPACE: never the real one
    # (Thm_Mini_*.lean and their draft records were found in the live workspace, 2026-10-03)
    ws = mdir.parent / 'ws'
    (ws / 'Theorems').mkdir(parents=True, exist_ok=True)
    monkeypatch.setenv('P2M_WORKSPACE', str(ws))
    monkeypatch.setattr(p2m, 'call', fake.call)
    monkeypatch.setattr(D.sys, 'argv', ['draft.py', str(mdir), 'upload'] + list(flags))
    D.main()


def test_dry_run_writes_nothing(mdir, monkeypatch, capsys):
    fake, ids = live_from_repo(mdir)
    fake.items[ids['t1']]['natural_language_statement'] = 'Something else.'
    run_upload(mdir, fake, monkeypatch)
    out = capsys.readouterr().out
    assert fake.writes == [] and 'would POST /mission-proposals/P/items  (t1)' in out


def test_upload_touches_only_the_changed_item_and_keeps_other_confirmations(mdir, monkeypatch):
    fake, ids = live_from_repo(mdir)
    fake.items[ids['t1']]['natural_language_statement'] = 'Something else.'
    run_upload(mdir, fake, monkeypatch, '--go')
    assert fake.writes == [('POST', '/mission-proposals/P/items')]
    assert fake.items[ids['goal']]['confirmed_at'] == '2026-10-02'      # untouched item keeps its confirmation
    bad, _, _ = D.diff(D.load(str(mdir)), str(mdir), fake.call, json.loads((mdir / 'proposal.json').read_text()))
    assert bad == []


def test_double_backslash_and_escaped_quote_flagged():
    # Monod 2026-09-29 `$G(\\mathbf{Z})$`; Moore 2026-10-01 `$\Gamma\'$` and `\"` in prose
    items = {'a': {'natural_language_statement': r'The group $G(\\mathbf{Z})$.'},
             'b': {'natural_language_statement': r"Its $\Gamma\'$ and \"quoted\"."},
             'c': {'natural_language_statement': r'Fine: $\mathbf{Z}$ and a $\\$ line break.'}}
    where = [w for w, _ in D.double_backslash(items, {}, '')]
    assert where.count('a') == 1 and where.count('b') == 2 and 'c' not in where


def test_pdftotext_math_in_quotes_flagged():
    # IET 2026-10-06: quotes copied from pdftotext kept "F (X)", "F (Y )", "x0", "gn−1" (g_n^{-1}
    # read as g_{n-1}); dbenbenn caught it in review
    items = {'a': {'natural_language_statement': 'JMMS, p. 2: “setting F (X) to be the direct limit of F (Y ) as Y runs”'},
             'b': {'natural_language_statement': 'p. 14: “On = {x0 , g1−1 x0 · · · , gn−1 x0 }.”'},
             'c': {'natural_language_statement': 'p. 2: “setting $F(X)$ to be the direct limit of $F(Y)$” and F (X) outside quotes'},
             'd': {'natural_language_statement': 'p. 4: “Is the group IET amenable?”'}}
    where = [w for w, _ in D.extraction_math(items, {}, '')]
    assert 'a' in where and 'b' in where and 'c' not in where and 'd' not in where


def test_title_mismatch_and_goal_quote(mdir):
    M = D.load(str(mdir))
    items, miles, _, _ = D.desired(M, str(mdir))
    assert D.title_mismatch(items, miles) == [] and D.goal_unquoted(M, items) == []
    miles['t1'] = ('Lemma 1 — drifted', miles['t1'][1])
    assert D.title_mismatch(items, miles)
    items['goal']['natural_language_statement'] = 'A paraphrase.'
    assert D.goal_unquoted(M, items)


def test_short_bundle_name_bound_as_variable_flagged_but_not_K_ascription(mdir):
    (mdir / 'lib' / 'Def_Mini.lean').write_text('def s : Nat := 1\ndef K : Set Nat := ∅\ndef Kfull : Nat := 2\n')
    M = D.load(str(mdir))
    M.DEFINITIONS = [dict(name='Mini')]
    (mdir / 'lib' / 'Thm_Mini.lean').write_text('theorem a : ∑ s ∈ Finset.range 3, s = 3 := by\n  sorry\n')
    assert any('`s`' in why for _, why in D.short_bundle_names(M, str(mdir)))
    # e43e780: `(K : Set ℝ)` in a statement that needs the bundle anyway (uses Kfull) is fine
    (mdir / 'lib' / 'Thm_Mini.lean').write_text('theorem b (x : ℕ) (h : x ∈ (K : Set ℕ)) : Kfull = 2 := by\n  sorry\n')
    assert D.short_bundle_names(M, str(mdir)) == []


def test_extract_payloads_keeps_primed_name(tmp_path):
    # was a strict xfail: `theorem (\\w+)` stopped at the prime
    p = tmp_path / 'T.lean'
    p.write_text("namespace Q\n\ntheorem foo' : True := by\n  sorry\n\nend Q\n")
    assert "foo'" in D.extract_payloads(str(p), 'Q', {})


def test_extract_payloads_ignores_doc_text_and_primed_identifiers(tmp_path):
    p = tmp_path / 'T.lean'
    p.write_text("/-!\ntheorem for balls -/\nnamespace Q\n\ntheorem t (h : K' = 1) : True := by\n  sorry\n\nend Q\n")
    pay = D.extract_payloads(str(p), 'Q', {'Definitions.Def_K': ['K']})
    assert list(pay) == ['t'] and 'Def_K' not in pay['t'][0]       # `K'` is not `K`


def test_extract_payloads_namespace_prefix_id(tmp_path):
    # moore-literal-readings passes 'MooreFoelner.' for a whole bundle: a prefix, not a name
    p = tmp_path / 'T.lean'
    p.write_text("namespace Q\n\ntheorem t : MooreFoelner.rightMul 1 1 = none := by\n  sorry\n\nend Q\n")
    assert 'import Definitions.Def_MooreFoelner' in \
        D.extract_payloads(str(p), 'Q', {'Definitions.Def_MooreFoelner': ['MooreFoelner.']})['t'][0]


def test_a_title_over_200_characters_is_refused_before_any_write(mdir, monkeypatch):
    # Erschler-Zheng 2026-10-04: the platform refuses a title over 200 characters, and the upload
    # stopped halfway with a Draft of two items; eight titles were too long
    fake, ids = live_from_repo(mdir)
    long = 'Lemma 1 — ' + 'x' * 200
    t = (mdir / 'mission.py').read_text().replace("title='Lemma 1 — one'", "title=%r" % long)
    (mdir / 'mission.py').write_text(t)
    with pytest.raises(SystemExit) as e:
        run_upload(mdir, fake, monkeypatch, '--go')
    assert 'over 200' in str(e.value) and 't1' in str(e.value)
    assert fake.writes == []


def test_missing_tags_default_to_the_mission_tags(mdir):
    t = (mdir / 'mission.py').read_text().replace(", tags=['x']", '') + "\nTAGS = ['mission-tag']\n"
    (mdir / 'mission.py').write_text(t)
    M = D.load(str(mdir))
    items, _, _, _ = D.desired(M, str(mdir))
    assert all(it['tags'] == ['mission-tag'] for it in items.values() if it['kind'] != 'reference')


def run_prune(mdir, fake, monkeypatch, *flags):
    import p2m
    monkeypatch.setattr(p2m, 'call', fake.call)
    monkeypatch.setattr(D.sys, 'argv', ['draft.py', str(mdir), 'prune'] + list(flags))
    D.main()


def test_prune_deletes_only_items_the_repo_dropped(mdir, monkeypatch, capsys):
    # Erschler-Zheng 2026-10-04: 28 auxiliary items left mission.py for a standalone package
    # (dbenbenn: auxiliary results are never milestones); upload only reports a stray, never deletes
    fake, ids = live_from_repo(mdir)
    fake.items['i_gone'] = dict(fake.items[ids['t1']], id='i_gone', theorem_name='Mini.gone')
    fake.miles['i_gone'] = ('Lemma 9 — gone', 'Dropped.')
    fake.prop['item_order'].insert(1, 'i_gone')
    st = json.loads((mdir / 'proposal.json').read_text())
    st['items']['gone'] = 'i_gone'
    (mdir / 'proposal.json').write_text(json.dumps(st))
    run_prune(mdir, fake, monkeypatch)
    assert fake.writes == [] and 'gone' in capsys.readouterr().out
    run_prune(mdir, fake, monkeypatch, '--go')
    assert fake.writes == [('DELETE', '/mission-proposals/P/items/i_gone')]
    assert 'gone' not in json.loads((mdir / 'proposal.json').read_text())['items']
    bad, _, _ = D.diff(D.load(str(mdir)), str(mdir), fake.call, json.loads((mdir / 'proposal.json').read_text()))
    assert bad == []
