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
