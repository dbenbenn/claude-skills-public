"""check_pronouns.py and p2m.py's refusal to publish comments."""
import pytest

import check_pronouns as CP
import p2m


def test_pronoun_scan(tmp_path):
    (tmp_path / 'prose.md').write_text('Moore proves it in his paper.\nThe shell game; `he` in code.\n')
    (tmp_path / 'X.lean').write_text('theorem foo (he : 1 = 1) : True := trivial -- she shows this\n')
    (tmp_path / 'readbacks').mkdir()
    (tmp_path / 'readbacks' / 'r.md').write_text('He wrote it.\n')       # auditor testimony: skipped
    hits = sorted((p.split('/')[-1], w) for p, _, w, _ in CP.scan_local([str(tmp_path)]))
    assert hits == [('X.lean', 'she'), ('prose.md', 'his')]


def test_pronoun_scan_accepts_a_file_argument(tmp_path):
    # F-amenability 2026-09-30: a file argument was walked as a directory and scanned nothing
    f = tmp_path / 'description.md'
    f.write_text('Chornyi gives her proof.\n')
    assert [w for _, _, w, _ in CP.scan_local([str(f)])] == ['her']


@pytest.mark.parametrize('field,text,refused', [
    ('formal_statement', 'theorem t : True := by\n  -- a note\n  sorry', True),
    ('formal_statement', '/-- doc -/\ntheorem t : True := by\n  sorry', True),
    ('preamble', 'import Mathlib -- why', True),
    ('formal_statement', 'theorem t : "a--b" = "a--b" := by\n  sorry', False),     # a literal, not a comment
    ('natural_language_statement', '-- prose may say anything', False),
])
def test_no_comments_in_frozen_fields(monkeypatch, field, text, refused):
    monkeypatch.delenv('P2M_ALLOW_DOCSTRING', raising=False)
    body = {'problems': [{field: text}]}
    if refused:
        with pytest.raises(SystemExit):
            p2m._no_docstring(body)
    else:
        p2m._no_docstring(body)


def test_override_and_definitions_untouched(monkeypatch):
    p2m._no_docstring({'definition': '/-- bundles keep docstrings -/\ndef k := 1'})
    monkeypatch.setenv('P2M_ALLOW_DOCSTRING', '1')
    p2m._no_docstring({'problems': [{'formal_statement': '-- deliberate'}]})
