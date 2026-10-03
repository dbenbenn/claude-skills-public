"""stage_auditor.py: comment stripping, staging, collection checks, safe teardown."""
import os

import pytest

import stage_auditor as SA


@pytest.mark.parametrize('src,want', [
    ('/-- doc -/\ntheorem a : True := trivial -- tail\n', 'theorem a : True := trivial\n'),
    ('/- outer /- nested -/ still -/\ndef b := 1\n', 'def b := 1\n'),
    ('def s := "a--b /- not a comment -/"\n', 'def s := "a--b /- not a comment -/"\n'),
    ("def c := '-'  -- gone\n", "def c := '-'\n"),
    ("theorem x' : True := trivial -- note\n", "theorem x' : True := trivial\n"),   # prime, then comment
    ('def r := r#"-- raw"#\n', 'def r := r#"-- raw"#\n'),
    ('def g := «foo--bar»\n', 'def g := «foo--bar»\n'),
])
def test_strip(src, want):
    assert SA.strip(src) == want


def test_strip_refuses_unclosed_block_comment():
    with pytest.raises(ValueError):
        SA.strip('/- never closed\ntheorem a : True := trivial\n')


@pytest.fixture
def root(tmp_path, monkeypatch):
    libs = tmp_path / 'libs' / 'mathlib' / 'Mathlib'
    libs.mkdir(parents=True)
    (libs / 'Keep.lean').write_text('-- a shared library file teardown must never touch\n')
    monkeypatch.setattr(SA, 'ROOT', str(tmp_path / 'auditors'))
    monkeypatch.setattr(SA, 'LIBS', str(tmp_path / 'libs'))
    monkeypatch.setattr(SA, 'TOOLCHAIN', str(tmp_path / 'toolchain'))
    monkeypatch.setattr(SA, 'WS', str(tmp_path / 'ws'))
    monkeypatch.setattr(SA, 'REV', 'mathlib test')
    monkeypatch.setattr(SA, 'fresh_oleans', lambda files: None)
    art = tmp_path / 'Thm_a.lean'
    art.write_text('/-- the intended reading -/\ntheorem a : True := trivial\n')
    return tmp_path, str(art), libs / 'Keep.lean'


def test_stage_strips_and_refuses_restaging(root, capsys):
    tmp, art, _ = root
    SA.stage('s1', art, [])
    d = os.path.join(SA.ROOT, 's1')
    assert open(os.path.join(d, 'Thm_a.lean')).read() == 'theorem a : True := trivial\n'
    assert os.path.exists(os.path.join(d, 'readback-brief.md')) and os.path.islink(os.path.join(d, 'Mathlib'))
    with pytest.raises(SystemExit):
        SA.stage('s1', art, [])


def test_stage_refuses_shared_basenames(root):
    tmp, art, _ = root
    other = tmp / 'sub'
    other.mkdir()
    (other / 'Thm_a.lean').write_text('theorem b : True := trivial\n')
    with pytest.raises(SystemExit):
        SA.stage('s2', art, [str(other / 'Thm_a.lean')])


def test_teardown_waits_for_audit_and_never_follows_links(root):
    tmp, art, keep = root
    SA.stage('s3', art, [])
    d = os.path.join(SA.ROOT, 's3')
    open(os.path.join(d, 'readback.md'), 'w').write('x')
    with pytest.raises(SystemExit):                # readback written, audit.md not yet: still working
        SA.teardown('s3')
    open(os.path.join(d, 'audit.md'), 'w').write('y')
    SA.teardown('s3')
    assert not os.path.exists(d) and keep.exists()


def test_collect_checks_and_import_denials(root, tmp_path, capsys):
    tmp, art, _ = root
    SA.stage('s4', art, [])
    d = os.path.join(SA.ROOT, 's4')
    open(os.path.join(d, 'readback.md'), 'w').write('# a\n\nFor every $n$, `Nat.succ` holds; see /home/x/f.lean:3.\n')
    open(os.path.join(d, 'audit.md'), 'w').write(
        '- No imported definition file goes entirely unused.\n'
        '- Def_Bar is not used by the artifact.\n'
        '- No, the import Def_Baz is not used.\n')
    capsys.readouterr()
    failed = SA.collect('s4', str(tmp_path / 'out'))
    out = capsys.readouterr().out
    assert failed
    assert 'FAIL Lean identifiers (want 0; use $math$): 1' in out and 'FAIL absolute paths (want 0): 1' in out
    imports = [l for l in out.split('\n') if l.startswith('IMPORTS')]
    assert len(imports) == 2 and 'goes entirely unused' not in ' '.join(imports)   # 00cf91e: denials skipped


def test_collect_all_names_stagings_left_by_a_renamed_item(tmp_path, monkeypatch, capsys):
    # dense-subgroups (2026-10-03): exists_injective_lift_pow_of_proximal was renamed after staging;
    # collect-all went by the new names and the old staging (testimony of the old Lean) lingered
    import stage_auditor as SA
    root = tmp_path / 'auditors'
    for d in ('pkg-old_name', 'pkg-new_name', 'other-thing', '_prompts'):
        (root / d).mkdir(parents=True)
    monkeypatch.setattr(SA, 'ROOT', str(root))
    monkeypatch.setattr(SA, 'mission_items', lambda mdir: [('new_name', None, [])])
    mdir = tmp_path / 'pkg'
    mdir.mkdir()
    assert SA.stale_stagings(str(mdir)) == ['pkg-old_name']
