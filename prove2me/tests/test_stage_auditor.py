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


def test_probe_runs_lean_through_the_cap(root):
    """The probe's `lake` is the lean-cap wrapper, not whatever PATH a session inherited: shells
    started before the cap existed resolve `lake` to elan's, and six auditors probing at once then
    run six uncapped Lean processes (2026-10-09)."""
    tmp, art, _ = root
    SA.stage('s3', art, [])
    text = open(os.path.join(SA.ROOT, 's3', 'probe')).read()
    export = 'export PATH="%s:$PATH"' % SA.LEAN_CAP
    assert export in text and text.index(export) < text.index('exec ')


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


@pytest.mark.parametrize('bad', ['.', '..', '', 'a/b', '/tmp', 'a/..'])
def test_teardown_refuses_anything_but_one_staging_dir(root, bad):
    # Viterbo 2026-10-30: `teardown --force . NAME` took '.' as the slug and removed the
    # whole staging root, with eight live auditors' directories in it
    tmp, art, keep = root
    SA.stage('s4', art, [])
    with pytest.raises(SystemExit):
        SA.teardown(bad, force=True)
    assert os.path.isdir(os.path.join(SA.ROOT, 's4'))


def test_teardown_cli_rejects_extra_arguments(root, monkeypatch):
    tmp, art, keep = root
    SA.stage('s5', art, [])
    monkeypatch.setattr(SA.sys, 'argv', ['stage_auditor.py', 'teardown', '--force', 's5', 'x'])
    with pytest.raises(SystemExit):
        SA.main()
    assert os.path.isdir(os.path.join(SA.ROOT, 's5'))


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


AUDIT = """# Audit notes: Def_B.lean

## Conventions settled
- `x / 0 = ⊤` in ℝ≥0∞ (`Mathlib/Data/ENNReal/Inv.lean:1`).

## What it does not say
- nothing
"""


def test_conventions_section_is_extracted_alone():
    assert SA.conventions_section(AUDIT) == (
        "## Conventions settled\n- `x / 0 = ⊤` in ℝ≥0∞ (`Mathlib/Data/ENNReal/Inv.lean:1`).\n")
    assert SA.conventions_section('# no such section\n') is None


def test_statement_readbacks_get_the_current_bundles_settled_conventions(root, tmp_path, monkeypatch):
    # Viterbo 2026-10-30: 19 statement auditors each re-derived the same ENNReal / deriv / infimum
    # conventions from Mathlib source; the bundle's blind read-back had already settled them
    tmp, art, keep = root
    bundle = tmp_path / 'Def_B.lean'
    bundle.write_text('def b : Nat := 1\n')
    mdir = tmp_path / 'm'
    (mdir / 'readbacks').mkdir(parents=True)
    (mdir / 'readbacks' / 'Def_B.audit.md').write_text(AUDIT)
    monkeypatch.setattr(SA, 'mission_items',
                        lambda d: [('Def_B', str(bundle), []), ('thm', art, [str(bundle)])])
    # no recorded hash yet: the conventions are not passed on
    SA.stage_all(str(mdir), ['thm'])
    d = os.path.join(SA.ROOT, SA.slug_of(str(mdir), 'thm'))
    assert not os.path.exists(os.path.join(d, 'settled-conventions.md'))
    # the bundle's read-back recorded the current bundle's hash: they are
    (mdir / 'readbacks' / 'Def_B.artifact.sha256').write_text(SA.stripped_sha(str(bundle)))
    SA.stage_all(str(mdir), ['thm'], force=True)
    text = open(os.path.join(d, 'settled-conventions.md')).read()
    assert 'Def_B' in text and 'x / 0' in text and 'What it does not say' not in text
    assert 'settled-conventions.md' in open(os.path.join(SA.ROOT, '_prompts', SA.slug_of(str(mdir), 'thm') + '.txt')).read()
    # a changed bundle makes the recorded hash stale: not passed on
    bundle.write_text('def b : Nat := 2\n')
    SA.stage_all(str(mdir), ['thm'], force=True)
    assert not os.path.exists(os.path.join(d, 'settled-conventions.md'))


def test_staging_records_the_artifact_hash(root):
    tmp, art, keep = root
    SA.stage('s6', art, [])
    assert open(os.path.join(SA.ROOT, 's6', 'ARTIFACT.sha256')).read().strip() == SA.stripped_sha(art)
