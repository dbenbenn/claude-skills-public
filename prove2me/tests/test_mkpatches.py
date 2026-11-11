"""mkpatches.py: patches.json entries derived from hand-repaired port modules (lessons oaiq-080,
oaiq-043, oaiq-063, oaiq-071, oaiq-072)."""
import json
import os
import subprocess
import sys

import pytest

import carve_prep
import mkpatches as M
from p2mlib import oaiport as O


def check(pristine, repaired, existing=()):
    """Derive, then the port's own apply_patches on the pristine text must give the repair, every
    `old` must be unique where it applies and cut no identifier; returns (patches, report)."""
    pats, rep = M.derive(pristine, repaired, list(existing))
    got = O.apply_patches(pristine, pats, route='modules')
    for f in pristine:
        assert got[f] == repaired.get(f, pristine[f]), f
    keep, drop = carve_prep.filter_patches([p for p in pats if not O.single_file_only(p)], pristine)
    assert not drop, drop
    for p in pats[len(existing):]:
        assert p['count'] == 1 and p['route'] == 'modules' and p['why']
    return pats, rep


def test_repeated_line_needs_more_context():
    a = 'theorem a : True := by\n  simp\n  trivial\n'
    b = 'theorem b : True := by\n  simp\n  trivial\n'
    pristine = {'A.lean': a + a.replace('a :', 'a2 :'), 'B.lean': b}
    repaired = {'A.lean': a + a.replace('a :', 'a2 :').replace('  simp\n', '  simp only []\n'),
                'B.lean': b}
    pats, _ = check(pristine, repaired)
    assert len(pats) == 1
    assert 'a2 :' in pats[0]['old']          # widened until unique over both modules


def test_edit_at_file_start_and_end():
    pristine = {'A.lean': 'import X\nimport Y\nfoo\nbar\n', 'B.lean': 'baz\nqux'}   # B: no final newline
    repaired = {'A.lean': 'import X\nimport Z\nfoo\nbar\nend\n', 'B.lean': 'baz\nquux'}
    pats, _ = check(pristine, repaired)
    assert len(pats) == 3


def test_first_line_changed():
    pristine = {'A.lean': 'import Mathlib\nx\n', 'B.lean': 'import Mathlib\ny\n'}
    repaired = {'A.lean': 'import Mathlib.Tactic\nx\n', 'B.lean': 'import Mathlib\ny\n'}
    check(pristine, repaired)


def test_insertion_only_hunk():
    pristine = {'A.lean': 'lemma p : 1 = 1 := by\n  rfl\n\nlemma q : 2 = 2 := by\n  rfl\n'}
    repaired = {'A.lean': 'lemma p : 1 = 1 := by\n  rfl\n\nset_option maxHeartbeats 400000 in\n'
                          'lemma q : 2 = 2 := by\n  rfl\n'}
    pats, _ = check(pristine, repaired)
    assert pats[0]['old']                     # never an empty `old`


def test_deletion_only_hunk():
    pristine = {'A.lean': 'x\n  decide\ny\n'}
    repaired = {'A.lean': 'x\ny\n'}
    check(pristine, repaired)


def test_identifier_boundary():
    # the line `foo x` is a suffix of `barfoo x`: a bare `foo x\n` would occur twice and cut `barfoo`
    pristine = {'A.lean': 'barfoo x\nfoo x\n', 'B.lean': 'hpositive\nhpos\n'}
    repaired = {'A.lean': 'barfoo x\nfoo y\n', 'B.lean': 'hpositive\nhpos2\n'}
    pats, _ = check(pristine, repaired)
    for p in pats:
        assert carve_prep.cut_identifier(p['old'], pristine.values()) is None


def test_same_line_two_modules_different_new():
    line = '  exact Finset.sum_le_sum fun i _ => h i\n'
    pristine = {'A.lean': 'lemma a := by\n' + line, 'B.lean': 'lemma b := by\n' + line}
    repaired = {'A.lean': 'lemma a := by\n  exact Finset.sum_le_sum (fun i _ => h i)\n',
                'B.lean': 'lemma b := by\n  gcongr with i\n'}
    pats, _ = check(pristine, repaired)
    assert len(pats) == 2 and pats[0]['old'] != pats[1]['old']


def test_nearby_hunks_merge_when_context_overlaps():
    pristine = {'A.lean': 's\nx\ns\ny\ns\n' * 2}
    repaired = {'A.lean': 's\nx\ns\ny\ns\n' + 's\nX\ns\nY\ns\n'}
    check(pristine, repaired)


def test_generated_and_new_files_reported_not_patched():
    pristine = {'A.lean': 'a\n', 'Compat.lean': 'c\n'}
    repaired = {'A.lean': 'a2\n', 'Compat.lean': 'c2\n', 'New.lean': 'n\n'}
    pats, rep = M.derive(pristine, repaired, [])
    assert len(pats) == 1
    assert any('Compat.lean' in r for r in rep['skipped'])
    assert any('New.lean' in r for r in rep['skipped'])


def test_merge_keeps_existing_and_adds_new():
    pristine = {'A.lean': 'one\ntwo\nthree\n'}
    existing = [{'old': 'one\n', 'new': 'ONE\n', 'count': 1, 'why': 'kept'},
                {'old': 'zzz', 'new': 'y', 'route': 'single', 'why': 'single file only'}]
    repaired = {'A.lean': 'ONE\ntwo\nTHREE\n'}
    pats, rep = check(pristine, repaired, existing)
    assert pats[:2] == existing and len(pats) == 3
    assert not rep['stale'] and not rep['amends']


def test_existing_patch_already_in_repair_adds_nothing():
    pristine = {'A.lean': 'one\ntwo\n'}
    existing = [{'old': 'one\n', 'new': 'ONE\n', 'count': 1, 'why': 'kept'}]
    pats, _ = check(pristine, {'A.lean': 'ONE\ntwo\n'}, existing)
    assert pats == existing


def test_stale_existing_patch_reported():
    pristine = {'A.lean': 'one\ntwo\n'}
    existing = [{'old': 'gone\n', 'new': 'x\n', 'count': 1, 'why': 'stale'}]
    pats, rep = M.derive(pristine, {'A.lean': 'one\nTWO\n'}, existing)
    assert rep['stale'] and rep['stale'][0][1] is existing[0]
    assert existing[0] not in pats            # derive leaves it out; the CLI refuses to write


def test_hunk_amending_existing_patch_reported():
    pristine = {'A.lean': 'one\ntwo\n'}
    existing = [{'old': 'one\n', 'new': 'ONE\n', 'count': 1, 'why': 'first try'}]
    pats, rep = check(pristine, {'A.lean': 'ONE!\ntwo\n'}, existing)
    assert rep['amends'] and len(pats) == 2


def test_pristine_equal_repaired_gives_nothing():
    pristine = {'A.lean': 'x\n'}
    assert M.derive(pristine, dict(pristine), [])[0] == []


def test_cli_merges_into_out(tmp_path):
    pri, rep = tmp_path / 'pri', tmp_path / 'rep'
    pri.mkdir(), rep.mkdir()
    (pri / 'A.lean').write_text('x\ny\nz\n')
    (rep / 'A.lean').write_text('x\nY\nz\n')
    out = tmp_path / 'patches.json'
    out.write_text(json.dumps([{'old': 'x\n', 'new': 'x\n', 'count': 1, 'why': 'noop'}]))
    script = os.path.join(os.path.dirname(M.__file__), 'mkpatches.py')
    r = subprocess.run([sys.executable, script, str(pri), str(rep), str(out), '--why', 'drift'],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr + r.stdout
    got = json.loads(out.read_text())
    assert len(got) == 2 and got[1]['why'] == 'drift'
    assert '1 new' in r.stdout


def test_cli_refuses_stale_without_flag(tmp_path):
    pri, rep = tmp_path / 'pri', tmp_path / 'rep'
    pri.mkdir(), rep.mkdir()
    (pri / 'A.lean').write_text('x\n')
    (rep / 'A.lean').write_text('X\n')
    out = tmp_path / 'patches.json'
    before = json.dumps([{'old': 'gone', 'new': 'x', 'count': 1, 'why': 'stale'}])
    out.write_text(before)
    script = os.path.join(os.path.dirname(M.__file__), 'mkpatches.py')
    r = subprocess.run([sys.executable, script, str(pri), str(rep), str(out)], capture_output=True, text=True)
    assert r.returncode == 1 and out.read_text() == before
    r = subprocess.run([sys.executable, script, str(pri), str(rep), str(out), '--drop-stale'],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr + r.stdout
    assert [p['old'] for p in json.loads(out.read_text())] == ['x\n']


def test_context_never_widens_into_folder_imports():
    """filter-patches ports under the placeholder folder `Solutions.FilterPatches`, so an `old` that
    holds an `import Solutions.<FOLDER>.…` line counts 0 there and the pipeline refuses the patch
    (q147-ostmann-retry: a compat theorem inserted right after the header). Context widens downward
    instead."""
    hdr = ('import Mathlib\nimport Solutions.F.%s\n\nset_option linter.all false\n\nnamespace OAI\n\n'
           'namespace E\nopen scoped E\n\nsection\nnamespace W\n\nopen X Y\n\n')
    pristine = {'A.lean': hdr % 'C' + 'theorem a : True := trivial\n',
                'B.lean': hdr % 'C' + 'theorem b : True := trivial\n',
                'C.lean': 'import Mathlib\n\ntheorem c : True := trivial\n'}
    repaired = dict(pristine)
    repaired['A.lean'] = (hdr % 'C').replace('namespace OAI', 'theorem shim : True := trivial\n\nnamespace OAI') \
        + 'theorem a : True := trivial\n'
    pats, _ = check(pristine, repaired)
    assert pats and not any('import Solutions.' in p['old'] for p in pats), pats
    ren = {f: t.replace('Solutions.F.', 'Solutions.FilterPatches.') for f, t in pristine.items()}
    keep, drop = carve_prep.filter_patches(pats, ren)
    assert not drop, drop


# ---- q243-free-ising: a `--why` naming a lemma our Mathlib lacks, in backticks, lands in every generated piece
# explanation the patch touches, and check-text stops on it (NOT FOUND) hours later at pieces_prep.

def _fake_ws(tmp_path):
    ws = tmp_path / 'ws'
    lib = ws / '.lake' / 'packages' / 'mathlib' / 'Mathlib'
    lib.mkdir(parents=True)
    (lib / 'Norm.lean').write_text("theorem eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm : True := trivial\n")
    return ws


def test_why_names_checked_like_check_text(tmp_path):
    ws = _fake_ws(tmp_path)
    texts = {'A.lean': 'theorem localThing : True := trivial\n'}
    why = ("`eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm` is now `eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm`; "
           "`localThing` stays")
    missing, searched = M.why_missing_names(why, texts, str(ws))
    assert searched and missing == ['eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm']
    assert M.why_missing_names('renamed eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm', texts, str(ws))[0] == []
    # no Mathlib to search: nothing can be judged (a warning, never a refusal)
    assert M.why_missing_names(why, texts, str(tmp_path / 'nows')) == ([], False)


def _cli(tmp_path, *extra, pristine=None, repaired=None):
    pri, rep = tmp_path / 'pri', tmp_path / 'rep'
    pri.mkdir(exist_ok=True), rep.mkdir(exist_ok=True)
    for d, files in ((pri, pristine or {'A.lean': 'x\ny\nz\n'}), (rep, repaired or {'A.lean': 'x\nY\nz\n'})):
        for f, t in files.items():
            (d / f).write_text(t)
    out = tmp_path / 'patches.json'
    script = os.path.join(os.path.dirname(M.__file__), 'mkpatches.py')
    if '--ws' not in extra:
        extra = ('--ws', str(tmp_path / 'emptyws')) + extra     # hermetic: no workspace folder to find
    r = subprocess.run([sys.executable, script, str(pri), str(rep), str(out)] + list(extra),
                       capture_output=True, text=True)
    return r, out


def test_cli_refuses_why_with_a_name_mathlib_lacks(tmp_path):
    ws = _fake_ws(tmp_path)
    r, out = _cli(tmp_path, '--ws', str(ws), '--why', '`eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm` was renamed')
    assert r.returncode == 1 and not out.exists(), r.stdout + r.stderr
    assert 'eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm' in r.stdout and 'check-text' in r.stdout
    r, out = _cli(tmp_path, '--ws', str(ws), '--why', "now `eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm`")
    assert r.returncode == 0 and out.exists(), r.stdout + r.stderr


# ---- q220-uniform-kserver: counts are taken over PRISTINE only; a scratch PRISTINE of the two repaired modules
# gave count 1 to a hunk occurring 96 times over the port, and filter_patches dropped it.

def test_cli_refuses_an_old_that_occurs_in_port_modules_pristine_lacks(tmp_path):
    port = tmp_path / 'port'
    port.mkdir()
    (port / 'A.lean').write_text('x\n  rfl\nz\n')
    (port / 'B.lean').write_text('b\n  exact h\n')      # in the port, not in PRISTINE
    (port / 'C.lean').write_text('c\n')
    r, out = _cli(tmp_path, '--port-dir', str(port), pristine={'A.lean': 'x\n  rfl\nz\n'},
                  repaired={'A.lean': 'x\n  simp\nz\n'})
    assert 'PRISTINE holds 1 of the 3 modules' in r.stdout, r.stdout + r.stderr
    assert r.returncode == 0 and out.exists()          # `  rfl` is unique over the whole port too: written
    out.unlink()
    (port / 'B.lean').write_text('b\n  rfl\n')
    r, out = _cli(tmp_path, '--port-dir', str(port), pristine={'A.lean': 'x\n  rfl\nz\n'},
                  repaired={'A.lean': 'x\n  simp\nz\n'})
    assert r.returncode == 1 and not out.exists(), r.stdout + r.stderr
    assert 'B.lean' in r.stdout


def test_port_folder_found_in_the_workspace(tmp_path):
    ws = tmp_path / 'ws'
    for folder, files in (('Mine', {'A.lean': 'mine\n', 'B.lean': 'b\n'}), ('Other', {'A.lean': 'other\n'}),
                          ('Third', {'A.lean': 'third\n', 'B.lean': 'b3\n'})):
        d = ws / 'Solutions' / folder
        d.mkdir(parents=True)
        for f, t in files.items():
            (d / f).write_text(t)
    # both Mine and Third hold A.lean; only Mine holds PRISTINE's text
    assert M.port_folder({'A.lean': 'mine\n'}, {'A.lean': 'fixed\n'}, str(ws)) == str(ws / 'Solutions' / 'Mine')
    assert M.port_folder({'A.lean': 'x\n'}, {'A.lean': 'third\n'}, str(ws)) == str(ws / 'Solutions' / 'Third')
    assert M.port_folder({'Z.lean': 'x\n'}, {}, str(ws)) is None
