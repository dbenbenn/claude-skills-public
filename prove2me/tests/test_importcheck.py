"""p2mlib.importcheck: what a solution imports, checked the same way by every submitter."""
import types

import pytest

from p2mlib import importcheck as I
from p2mlib.workspace import set_drafts, drafts


def rows(**status):
    """A fake /theorems?theorem_name= lookup: each named theorem is published with this status."""
    def call(method, path, body=None):
        assert method == 'GET' and path.startswith('/theorems?theorem_name=')
        name = path.split('=', 1)[1].split('&')[0]
        if name in status:
            return {'theorems': [{'theorem_name': name + 'X', 'status': 'Open'},
                                 {'theorem_name': name, 'id': 'id-' + name, 'status': status[name]}]}
        return {'theorems': []}
    return call


@pytest.fixture
def ws(tmp_path):
    (tmp_path / 'Theorems').mkdir()
    (tmp_path / 'Theorems' / 'Thm_N_a.lean').write_text('namespace N\n\ntheorem a : True := by\n  sorry\n\nend N\n')
    (tmp_path / 'Theorems' / 'Thm_N_Sub_b.lean').write_text(
        '/-! theorem for balls -/\nnamespace N\nnamespace Sub\n\nlemma b : True := by\n  sorry\n\nend Sub\nend N\n')
    (tmp_path / 'Theorems' / 'Thm_R_c.lean').write_text('namespace Q\ntheorem _root_.R.c : True := by sorry\nend Q\n')
    return tmp_path


def test_theorem_imports_ignore_comments_and_other_modules():
    text = '/- import Theorems.Thm_Z -/\nimport Mathlib\nimport Theorems.Thm_N_a\nimport Definitions.Def_D\n'
    assert I.theorem_imports(text) == ['Theorems.Thm_N_a']


def test_module_theorem_reads_nested_namespaces_root_names_and_lemmas(ws):
    assert I.module_theorem('Theorems.Thm_N_a', str(ws)) == 'N.a'
    assert I.module_theorem('Theorems.Thm_N_Sub_b', str(ws)) == 'N.Sub.b'
    assert I.module_theorem('Theorems.Thm_R_c', str(ws)) == 'R.c'
    assert I.module_theorem('Theorems.Thm_Missing', str(ws)) is None


def test_disproved_needs_the_exact_name():
    call = rows(**{'N.a': 'Disproved', 'N.b': 'Proved'})
    assert I.disproved(['N.b', 'N.a', 'N.z'], call=call) == ['N.a']
    assert I.disproved([], call=call) == []
    assert 'N.a' in I.disproved_message(['N.a']) and 'Disproved' in I.disproved_message(['N.a'])


def test_published_drafts_asks_the_platform_for_each_stub(ws):
    # oaiq-100: siblings of an in-review mission were published (and proved) while the workspace
    # still listed them as draft stubs
    got = I.published_drafts(['Theorems.Thm_N_a', 'Theorems.Thm_N_Sub_b'], str(ws), call=rows(**{'N.a': 'Proved'}))
    assert got == {'Theorems.Thm_N_a': 'N.a'}


def test_fetch_command_names_the_theorems():
    cmd = I.fetch_command(['N.a', 'N.Sub.b'])
    assert cmd.endswith('fetch_theorems.py --names N.a N.Sub.b') and cmd.startswith('python3 ')


def test_retire_published_runs_the_names_fetch_and_reports_what_is_left(ws):
    set_drafts({'Theorems.Thm_N_a': '/m', 'Theorems.Thm_N_Sub_b': '/m'}, str(ws))
    seen = []

    def run(cmd, **k):
        seen.append(cmd)
        set_drafts({'Theorems.Thm_N_Sub_b': '/m'}, str(ws))      # what fetch_theorems does for N.a
        return types.SimpleNamespace(returncode=0, stdout='1 draft stub(s) now published\n', stderr='')
    left, fetched = I.retire_published(['Theorems.Thm_N_a', 'Theorems.Thm_N_Sub_b'], str(ws),
                                       call=rows(**{'N.a': 'Open'}), run=run)
    assert fetched == ['N.a'] and left == ['Theorems.Thm_N_Sub_b']
    assert seen[0][-3].endswith('fetch_theorems.py') and seen[0][-2:] == ['--names', 'N.a']
    assert drafts(str(ws)) == {'Theorems.Thm_N_Sub_b': '/m'}


def test_retire_published_runs_nothing_while_none_is_published(ws):
    set_drafts({'Theorems.Thm_N_a': '/m'}, str(ws))

    def run(cmd, **k):
        raise AssertionError('nothing to fetch')
    assert I.retire_published(['Theorems.Thm_N_a'], str(ws), call=rows(), run=run) == (['Theorems.Thm_N_a'], [])


def test_oai_submit_submits_only_through_submit_solution():
    # oaiq-109: the Disproved-import and draft-stub checks live in submit_solution.py (through this
    # module); oai_submit.py runs that script for every attempt, and its refusal is final
    import oai_submit
    from p2mlib import oaiport
    assert oai_submit.SUBMIT.endswith('/submit_solution.py')
    v = oaiport.classify_attempt(I.disproved_message(['N.dep']))
    assert v[0] == 'REFUSED' and 'Disproved' in v[2]
