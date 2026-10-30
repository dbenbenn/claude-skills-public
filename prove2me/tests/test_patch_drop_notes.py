"""filter-patches says why a recorded hand patch no longer matches (oaiq-090): after a skill upgrade a newer
port rule rewrote the sites of three hand patches, filter_patches dropped them for their count (0), and the
worker had to work out by hand that the rule had made them unnecessary. Small sources, no Lean."""
import json

import carve_prep as CP
from p2mlib import oaiport as O

COMPAT = 'theorem ite_eq_left : True := trivial\n'

DERIV = ('import Mathlib\n\n'
         'theorem foo (x : ℝ) : HasDerivAt f (g x) x := by\n'
         '  have h := (hasDerivAt_id x).add_const 1\n'
         '  convert h using 1\n'
         '  · rfl\n'
         '  · change g x = 1\n'
         '    simp\n')
FIN = ('import Mathlib\n\n'
       'theorem bar (i : Fin 6) : tbl i ≤ 7 := by\n'
       '  fin_cases i <;> norm_num [tbl]\n')


def _sources():
    return {'OAI.Fam.D': ('D', DERIV), 'OAI.Fam.F': ('F', FIN)}


def test_note_names_the_rule_that_rewrote_the_site():
    pc = {'old': '  convert h using 1\n  · rfl\n', 'new': '  convert h using 1 <;> try rfl\n'}
    pf = {'old': 'fin_cases i <;> norm_num [tbl]', 'new': 'fin_cases i <;> simp [tbl] <;> norm_num'}
    gone = {'old': 'theorem baz', 'new': 'theorem baz\''}
    ok = {'old': 'theorem bar', 'new': 'theorem bar'}
    detail, notes = [], {}
    keep, drop = CP.port_filter_patches([pc, pf, gone, ok], _sources(), COMPAT, 'OAI', detail=detail, notes=notes)
    assert keep == [ok]
    assert [p for _, p in drop] == [pc, pf, gone]
    assert 'convert_funext_rfl_to_congr_deriv' in notes[pc['old']]
    assert 'refine h.congr_deriv (Eq.symm ?_)' in notes[pc['old']]
    assert 'fin_norm_num' in notes[pf['old']] and 'first | (simp [tbl]; all_goals' in notes[pf['old']]
    assert 'not in the port\'s input' in notes[gone['old']]
    assert ok['old'] not in notes


def test_note_for_an_unnamed_rewrite_and_a_patch_matching_too_often():
    src = {'OAI.Fam.E': ('E', 'import Mathlib\n\nexample := List.sum_le_length_nsmul\nexample := 1\nexample := 1\n')}
    pr = {'old': 'List.sum_le_length_nsmul', 'new': 'x'}
    many = {'old': 'example := 1', 'new': 'example := 2'}      # count 1, found 2: no note
    notes = {}
    CP.port_filter_patches([pr, many], src, COMPAT, 'OAI', notes=notes)
    assert 'not one of the named rules' in notes[pr['old']]
    assert 'List.sum_le_card_nsmul' in notes[pr['old']]
    assert many['old'] not in notes


def test_note_on_a_large_module_diffs_only_around_the_site():
    filler = ''.join('theorem t%d : True := trivial\n' % i for i in range(20000))
    src = {'OAI.Fam.D': ('D', DERIV.replace('import Mathlib\n\n', 'import Mathlib\n\n' + filler))}
    pc = {'old': '  convert h using 1\n  · rfl\n', 'new': 'x'}
    notes = {}
    CP.port_filter_patches([pc], src, COMPAT, 'OAI', notes=notes)
    assert 'refine h.congr_deriv' in notes[pc['old']]


def test_filter_patches_command_prints_the_note(tmp_path, capsys):
    lean = tmp_path / 'lean'
    (lean / 'OAI' / 'Fam').mkdir(parents=True)
    (lean / 'OAI' / 'Fam' / 'D.lean').write_text(DERIV, encoding='utf-8')
    pc = {'old': '  convert h using 1\n  · rfl\n', 'new': 'x'}
    pa = {'old': 'theorem baz', 'new': 'y', 'allow_drop': True}
    pj = tmp_path / 'p.json'
    pj.write_text(json.dumps([pc, pa]), encoding='utf-8')
    compat = tmp_path / 'compat.lean'
    compat.write_text(COMPAT, encoding='utf-8')
    out = tmp_path / 'out.json'
    try:
        CP.cmd_filter_patches([str(pj), str(lean), str(out), 'OAI.Fam', '--compat', str(compat)])
    except SystemExit:
        pass
    cap = capsys.readouterr()
    assert 'why: 1 occurrence(s) in the port\'s input: the port rule convert_funext_rfl_to_congr_deriv' in cap.err
    # an allow_drop patch is dropped quietly but still says why
    assert 'why: not in the port\'s input' in cap.out
