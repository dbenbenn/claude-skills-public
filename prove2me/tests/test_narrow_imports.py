"""p2mlib.narrow and narrow_imports.py: a statement preamble's `import Mathlib` narrowed to what the statement
uses, accepted only when the statement elaborates to the same `pp.all` term (x25519-dalek, 2026-11-23)."""
import json

import pytest

from p2mlib import narrow as N


FS = 'namespace Q\n\n/-- doc -/\ntheorem t (x : Nat) : x = x := by\n  sorry\n\nend Q\n'


def test_whole_mathlib_is_only_the_bare_import():
    assert N.whole_mathlib('import Mathlib\nimport Definitions.Def_A')
    assert N.whole_mathlib('import Definitions.Def_A\nimport Mathlib  ')
    assert not N.whole_mathlib('import Mathlib.Data.Nat.Basic\nimport Definitions.Def_A')
    assert not N.whole_mathlib('')


def test_probe_marks_the_declaration_before_its_docstring_and_checks_it_inside_the_namespace():
    text = N.probe_text('import Mathlib', FS, min_imports=True)
    assert '#min_imports in\n/-- doc -/\ntheorem t' in text
    assert 'set_option pp.all true in\n#check @t\n\nend Q' in text
    plain = N.probe_text('import Mathlib.Logic.Basic', FS, min_imports=False)
    assert '#min_imports' not in plain and plain.startswith('import Mathlib.Logic.Basic\n')


def test_probe_without_namespace_appends_the_check():
    text = N.probe_text('import Mathlib', 'theorem Q.t : True := by\n  sorry\n', min_imports=True)
    assert text.rstrip().endswith('set_option pp.all true in\n#check @Q.t')


LOG_FULL = ('lean-cap: all 12 Lean slots busy; queued (priority 5)\n'
            'public import Definitions.Def_A\npublic import Lean.Parser.Command\n'
            'public import Mathlib.Analysis.SpecialFunctions.Log.Basic\n'
            ".probe.lean:7:8: warning: declaration uses 'sorry'\n"
            '@Q.t : forall (x : Nat),\n  @Eq.{1} Nat x x\n')


def test_parse_suggestions_and_check_output():
    assert N.suggestions(LOG_FULL) == ['Definitions.Def_A', 'Lean.Parser.Command',
                                       'Mathlib.Analysis.SpecialFunctions.Log.Basic']
    assert N.check_output(LOG_FULL) == '@Q.t : forall (x : Nat),\n  @Eq.{1} Nat x x'


def test_narrowed_preamble_replaces_the_line_in_place():
    pre = 'import Definitions.Def_A\nimport Mathlib\nimport Theorems.Thm_Q_s'
    sug = ['Definitions.Def_A', 'Lean.Parser.Command', 'Mathlib.Order.Basic', 'Mathlib.Tactic.MinImports']
    assert N.narrowed_preamble(pre, sug) == ('import Definitions.Def_A\nimport Mathlib.Order.Basic\n'
                                             'import Theorems.Thm_Q_s')
    assert N.narrowed_preamble(pre, sug, with_lean=True) == (
        'import Definitions.Def_A\nimport Lean.Parser.Command\nimport Mathlib.Order.Basic\nimport Theorems.Thm_Q_s')
    # no Mathlib needed: the line goes
    assert N.narrowed_preamble('import Mathlib\nimport Definitions.Def_A', ['Definitions.Def_A']) == \
        'import Definitions.Def_A'


def test_narrowed_preamble_refuses_a_root_the_platform_may_not_have():
    with pytest.raises(N.NarrowError) as e:
        N.narrowed_preamble('import Mathlib', ['Aesop.Frontend.Attribute'])
    assert 'Aesop' in str(e.value)


class FakeLean:
    """compile(text) -> log: the full-Mathlib probe answers LOG_FULL; a narrowed one answers `narrow_log`."""
    def __init__(self, narrow_log):
        self.narrow_log, self.texts = narrow_log, []

    def __call__(self, text):
        self.texts.append(text)
        return LOG_FULL if 'import Mathlib\n' in text else self.narrow_log


def test_narrow_accepts_an_identical_elaboration():
    lean = FakeLean(".probe.lean:7:8: warning: declaration uses 'sorry'\n@Q.t : forall (x : Nat),\n  @Eq.{1} Nat x x\n")
    pre = N.narrow('import Mathlib\nimport Definitions.Def_A', FS, lean)
    assert pre == 'import Mathlib.Analysis.SpecialFunctions.Log.Basic\nimport Definitions.Def_A'
    assert len(lean.texts) == 2


def test_narrow_refuses_a_changed_elaboration():
    # fewer imports can pick another instance or coercion: then the statement says something else
    lean = FakeLean('@Q.t : forall (x : Nat),\n  @Eq.{1} Nat (id x) x\n')
    with pytest.raises(N.NarrowError) as e:
        N.narrow('import Mathlib\nimport Definitions.Def_A', FS, lean)
    assert 'elaborates differently' in str(e.value)


def test_narrow_retries_with_lean_modules_on_an_error():
    calls = []

    def lean(text):
        calls.append(text)
        if 'import Mathlib\n' in text:
            return LOG_FULL
        if 'Lean.Parser.Command' not in text:
            return ".probe.lean:3:0: error: unknown identifier 'foo'\n"
        return '@Q.t : forall (x : Nat),\n  @Eq.{1} Nat x x\n'
    pre = N.narrow('import Mathlib\nimport Definitions.Def_A', FS, lean)
    assert 'import Lean.Parser.Command' in pre and len(calls) == 3


def test_narrow_reports_a_full_probe_error():
    with pytest.raises(N.NarrowError) as e:
        N.narrow('import Mathlib', FS, lambda t: ".probe.lean:1:0: error: object file 'x.olean' does not exist\n")
    assert 'does not exist' in str(e.value)


def test_rewrite_file_replaces_only_the_bare_import(tmp_path):
    f = tmp_path / 'Thm_Q_t.lean'
    f.write_text('import Mathlib\nimport Definitions.Def_A\n\n' + FS)
    N.rewrite_file(str(f), 'import Mathlib.Order.Basic\nimport Definitions.Def_A')
    assert f.read_text() == 'import Mathlib.Order.Basic\nimport Definitions.Def_A\n\n' + FS
    g = tmp_path / 'Thm_Q_u.lean'
    g.write_text('import Mathlib\nimport Definitions.Def_A\n\n' + FS)
    N.rewrite_file(str(g), 'import Definitions.Def_A')
    assert g.read_text() == 'import Definitions.Def_A\n\n' + FS


def test_extract_payloads_reads_narrowed_imports(tmp_path):
    import draft
    (tmp_path / 'lib').mkdir()
    p = tmp_path / 'lib' / 'Thm.lean'
    p.write_text('namespace Q\n\ntheorem t : A.Word = A.Word := by\n  sorry\n\ntheorem u : True := by\n  sorry\n\nend Q\n')
    (tmp_path / 'imports.json').write_text(json.dumps({'t': ['Mathlib.Order.Basic'], 'u': []}))
    out = draft.extract_payloads(str(p), 'Q', {'Definitions.Def_A': ['A.Word']})
    assert out['t'][0] == 'import Mathlib.Order.Basic\nimport Definitions.Def_A'
    assert out['u'][0] == ''


def test_draft_verify_flags_whole_mathlib_only_on_a_draft():
    import draft

    class M:
        WHOLE_MATHLIB = {'w': 'the statement quantifies over all of Mathlib (test)'}
    its = {'t': {'kind': 'theorem', 'preamble': 'import Mathlib\nimport Definitions.Def_A'},
           'n': {'kind': 'theorem', 'preamble': 'import Mathlib.Order.Basic'},
           'w': {'kind': 'theorem', 'preamble': 'import Mathlib'},
           'D': {'kind': 'definition', 'definition': 'import Mathlib\n'}}
    bad = draft.whole_mathlib_preambles(M, its, 'Draft')
    assert [k for k, _ in bad] == ['t'] and 'narrow_imports.py' in bad[0][1]
    assert draft.whole_mathlib_preambles(M, its, 'Live') == []      # published: frozen, nothing to do


def test_publish_standalone_refuses_a_new_whole_mathlib_statement(tmp_path):
    import publish_standalone as PS
    payloads = [{'theorem_name': 'Q.t', 'preamble': 'import Mathlib'},
                {'theorem_name': 'Q.u', 'preamble': 'import Mathlib'},
                {'theorem_name': 'Q.v', 'preamble': 'import Mathlib'},
                {'theorem_name': 'Q.n', 'preamble': 'import Definitions.Def_A'}]
    assert PS.whole_mathlib_new(payloads, {'Q.u': 'T1'}, {'v': 'reason'}) == ['Q.t']
