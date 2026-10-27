"""carve_prep.py prose-template (p2mlib.prosetemplate): the prose of a carve's intermediate items,
written from the plan, the carve's files and the declaration graph, with no model call (dbenbenn
2026-10-24: carved intermediate prose is rarely read and patchable, and written prose was the
biggest cost of a carve). Synthetic fixtures only: OpenAI's code never goes into this repo."""
import hashlib
import json
import os

import pytest

import carve_prep as CP
import check_pronouns as PR
from p2mlib import explanation as E
from p2mlib import prosetemplate as T
from p2mlib.mission import front_matter

COMMIT = '0123456789abcdef0123456789abcdef01234567'
META = {'title': 'A Synthetic Result', 'date': 'September 1, 2026', 'family': 7, 'commit': COMMIT,
        'paper': 'https://github.com/openai/math/blob/%s/preprints/Synthetic/main.pdf' % COMMIT,
        'prefixes': ['OAI.Fam.Synth']}

DEF = '''import Mathlib
import Definitions.Def_Fam

section
-- module Solutions.F.Basic
set_option linter.all false

namespace OAI

namespace Fam

def Foo (n : ℕ) : ℕ := n + base

structure Bar where
  x : ℕ

instance instInhabitedBar : Inhabited Bar := ⟨⟨0⟩⟩

theorem foo_pos (n : ℕ) : 0 < Foo n + 1 := Nat.succ_pos _

end Fam

end OAI
end

section
-- module Solutions.F.Sub_Deep
namespace OAI.Fam
def Baz : ℕ := 3
end OAI.Fam
end
'''

STUB_LEM = '''import Mathlib
import Definitions.Def_FAMQ000

section

set_option linter.all false

namespace OAI

noncomputable section

namespace Fam.Lemmas

open Finset

theorem lemA (n : ℕ) (he : 1 ≤ n) (b : Bar) :
    Foo n ≤ Foo (n + b.x) + Baz := by
  sorry

end Fam.Lemmas

end

end OAI
end
'''

STUB_NAMED = '''import Mathlib
import Definitions.Def_FAMQ000

namespace OAI.Fam

theorem named (n : ℕ) : Foo n = Foo n := by
  sorry

end OAI.Fam
'''

COMPAT = '''section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434
'''

SOL_LEM = '''import Mathlib
import Definitions.Def_Fam
import Definitions.Def_FAMQ000

section
-- module Solutions.F.Compat
namespace OAI
''' + COMPAT + '''end OAI
end

section
-- module Solutions.F.Lemmas
set_option linter.all false
set_option linter.unusedVariables false
namespace OAI.Fam.Lemmas
theorem helper (n : ℕ) : Foo n ≤ Foo n := le_refl _
theorem lemA_oai (n : ℕ) (he : 1 ≤ n) (b : Bar) : Foo n ≤ Foo (n + b.x) + Baz := by
  simp [Foo, Baz]; omega
end OAI.Fam.Lemmas
end

theorem solution : type_of% @OAI.Fam.Lemmas.lemA_oai := @OAI.Fam.Lemmas.lemA_oai
'''

SOL_NAMED = '''import Mathlib
import Definitions.Def_FAMQ000
import Theorems.Thm_OAI_Fam_Lemmas_lemA

namespace OAI.Fam
theorem named_oai (n : ℕ) : Foo n = Foo n := rfl
end OAI.Fam

theorem solution : type_of% @OAI.Fam.named_oai := @OAI.Fam.named_oai
'''

SOL_MAIN = '''import Mathlib
import Theorems.Thm_OAI_Fam_named

theorem main_oai : True := trivial
theorem solution : type_of% @main_oai := @main_oai
'''

GRAPH = [
    {'n': 'OAI.Fam.Foo', 'm': 'Solutions.F.Basic', 'k': 'def', 'i': False, 't': ['OAI.Fam.base']},
    {'n': 'OAI.Fam.Bar', 'm': 'Solutions.F.Basic', 'k': 'inductive', 'i': False, 't': []},
    {'n': 'OAI.Fam.Bar.x', 'm': 'Solutions.F.Basic', 'k': 'def', 'i': False, 't': ['OAI.Fam.Bar']},
    {'n': 'OAI.Fam.instInhabitedBar', 'm': 'Solutions.F.Basic', 'k': 'def', 'i': True, 't': ['OAI.Fam.Bar']},
    {'n': 'OAI.Fam.foo_pos', 'm': 'Solutions.F.Basic', 'k': 'theorem', 'i': False, 't': ['OAI.Fam.Foo']},
    {'n': 'OAI.Fam.Baz', 'm': 'Solutions.F.Sub_Deep', 'k': 'def', 'i': False, 't': []},
    {'n': 'OAI.Fam.Lemmas.helper', 'm': 'Solutions.F.Lemmas', 'k': 'theorem', 'i': False, 't': ['OAI.Fam.Foo']},
    {'n': 'OAI.Fam.Lemmas.lemA', 'm': 'Solutions.F.Lemmas', 'k': 'theorem', 'i': False,
     't': ['OAI.Fam.Foo', 'OAI.Fam.Bar', 'OAI.Fam.Bar.x', 'OAI.Fam.Baz']},
    {'n': 'OAI.Fam.named', 'm': 'Solutions.F.Named', 'k': 'theorem', 'i': False, 't': ['OAI.Fam.Foo']},
    {'n': 'OAI.main', 'm': 'Solutions.F.Main', 'k': 'theorem', 'i': False, 't': []},
]

PLAN = {
    'bundles': [{'name': 'FAMQ000', 'imports': [], 'cost': 1.0, 'size': 10,
                 'nodes': ['OAI.Fam.Foo', 'OAI.Fam.Bar', 'OAI.Fam.instInhabitedBar', 'OAI.Fam.foo_pos',
                           'OAI.Fam.Baz']}],
    'external': ['OAI.main'], 'targets': ['OAI.main'], 'forced': ['OAI.Fam.named'],
    'external_defs': {'OAI.Fam.base': 'Definitions.Def_Fam'},
    'nodes': ['OAI.Fam.Lemmas.lemA', 'OAI.Fam.named', 'OAI.main'],
    'stubs': {'OAI.Fam.Lemmas.lemA': {'bundles': ['FAMQ000']}, 'OAI.Fam.named': {'bundles': ['FAMQ000']},
              'OAI.main': {'bundles': []}},
    'pieces': {'OAI.Fam.Lemmas.lemA': {'bundles': ['FAMQ000'], 'imports': [],
                                        'keep': ['OAI.Fam.Lemmas.helper', 'OAI.Fam.Lemmas.lemA']},
               'OAI.Fam.named': {'bundles': ['FAMQ000'], 'imports': ['OAI.Fam.Lemmas.lemA'],
                                 'keep': ['OAI.Fam.named']},
               'OAI.main': {'bundles': [], 'imports': ['OAI.Fam.named'], 'keep': ['OAI.main']}},
    'statement_suffix': '', 'sorry': [], 'over': [], 'version': 1,
}


def make_carve(tmp_path):
    d = tmp_path / 'carve'
    ws = tmp_path / 'ws'
    (ws / 'Definitions').mkdir(parents=True)
    (ws / 'Definitions' / 'Def_Fam.lean').write_text('import Mathlib\nnamespace OAI.Fam\ndef base : ℕ := 1\nend OAI.Fam\n')
    (ws / 'Theorems').mkdir()
    (ws / 'Theorems' / 'Thm_OAI_main.lean').write_text('import Mathlib\ntheorem OAI.main : True := by\n  sorry\n')
    (ws / 'lean-toolchain').write_text('leanprover/lean4:v4.33.1\n')
    (ws / 'lake-manifest.json').write_text(json.dumps({'packages': [{'name': 'mathlib', 'rev': '0df444a' + '0' * 33}]}))
    for x in ('work', 'publish/out/lib', 'publish/out/solutions', 'publish/prose', 'publish/explanations'):
        (d / x).mkdir(parents=True)
    (d / 'config.json').write_text(json.dumps({'work': str(d / 'work'), 'src': str(ws),
                                               'targets': ['OAI.main'], 'forced': ['OAI.Fam.named']}))
    (d / 'work' / 'decl_graph.jsonl').write_text(''.join(json.dumps(x) + '\n' for x in GRAPH))
    (d / 'oai_meta.json').write_text(json.dumps(META))
    P = d / 'publish'
    (P / 'plan.json').write_text(json.dumps(PLAN))
    (P / 'out/lib/Def_FAMQ000.lean').write_text(DEF)
    (P / 'out/lib/Thm_OAI_Fam_Lemmas_lemA.lean').write_text(STUB_LEM)
    (P / 'out/lib/Thm_OAI_Fam_named.lean').write_text(STUB_NAMED)
    (P / 'out/solutions/Sol_OAI_Fam_Lemmas_lemA.lean').write_text(SOL_LEM)
    (P / 'out/solutions/Sol_OAI_Fam_named.lean').write_text(SOL_NAMED)
    (P / 'out/solutions/Sol_OAI_main.lean').write_text(SOL_MAIN)
    return d, ws


def run(d, force=False):
    return T.write_templates(str(d), meta=None, force=force)


def test_writes_intermediate_items_and_lists_the_goal_and_forced_nodes(tmp_path):
    d, _ = make_carve(tmp_path)
    rep = run(d)
    P = d / 'publish'
    assert sorted(os.listdir(P / 'prose')) == [T.MANIFEST, 'FAMQ000.md', 'OAI_Fam_Lemmas_lemA.md']
    assert sorted(os.listdir(P / 'explanations')) == [T.MANIFEST, 'OAI_Fam_Lemmas_lemA.md']
    assert sorted(rep['needs_written']) == [
        'explanation OAI.Fam.named (forced)', 'explanation OAI.main (goal)',
        'statement OAI.Fam.named (forced)']
    assert sorted(rep['written']) == ['explanations/OAI_Fam_Lemmas_lemA.md', 'prose/FAMQ000.md',
                                      'prose/OAI_Fam_Lemmas_lemA.md']


def test_statement_prose_credits_openai_links_the_source_and_renders_the_lean(tmp_path):
    d, _ = make_carve(tmp_path)
    run(d)
    text = (d / 'publish/prose/OAI_Fam_Lemmas_lemA.md').read_text()
    fields, body = front_matter(text)
    assert fields['template'] == T.MARK
    assert 0 < len(fields['title']) <= 200 and 'OAI.Fam.Lemmas.lemA' in fields['title']
    link = 'https://github.com/openai/math/blob/%s/lean/OAI/Fam/Synth/Lemmas.lean' % COMMIT
    assert link in fields['source'] and 'declaration OAI.Fam.Lemmas.lemA' in fields['source']
    assert 'result family 7' in fields['source'] and META['paper'] in fields['source']
    assert 'OpenAI' in body and '`OAI.main`' in body and 'A Synthetic Result' in body
    assert link in body
    # the published statement verbatim (no proof), with its namespace and opens
    assert ('```lean\ntheorem lemA (n : ℕ) (he : 1 ≤ n) (b : Bar) :\n'
            '    Foo n ≤ Foo (n + b.x) + Baz\n```') in body
    assert '`OAI.Fam.Lemmas`' in body and '`open Finset`' in body
    # the split's declarations its statement uses, by Lean's own record, with their bundle
    assert '`OAI.Fam.Foo`' in body and '`OAI.Fam.Bar`' in body and '`OAI.Fam.Baz`' in body
    assert '`OAI.Fam.Bar.x`' not in body          # a field is shown as its structure
    assert '`FAMQ000`' in body
    # who uses it: the proof of the forced named result imports it
    assert '`OAI.Fam.named`' in body


def test_bundle_prose_lists_kinds_modules_sources_and_importers(tmp_path):
    d, _ = make_carve(tmp_path)
    run(d)
    fields, body = front_matter((d / 'publish/prose/FAMQ000.md').read_text())
    assert fields['template'] == T.MARK and 'FAMQ000' in fields['title']
    assert 'lean/OAI/Fam/Synth' in fields['source'] and COMMIT[:7] in fields['source']
    # 5 declarations: Foo, Baz (definitions), Bar (inductive type or structure), one instance, one theorem
    assert '5 declarations' in body
    assert '2 definitions' in body and '1 instance' in body and '1 inductive type or structure' in body \
        and '1 theorem' in body
    assert '`Basic`' in body and '`Sub_Deep`' in body
    assert 'https://github.com/openai/math/blob/%s/lean/OAI/Fam/Synth/Sub/Deep.lean' % COMMIT in body
    assert '`Def_Fam`' in body                     # the published bundle it imports
    # what imports it: two statements and two proofs
    assert '`OAI.Fam.Lemmas.lemA`' in body and '`OAI.Fam.named`' in body
    assert 'Lean 4.33.1' in body and 'Mathlib 0df444a' in body


def test_explanation_meets_the_platform_rules_and_says_what_the_port_changed(tmp_path):
    d, _ = make_carve(tmp_path)
    run(d)
    t = (d / 'publish/explanations/OAI_Fam_Lemmas_lemA.md').read_text()
    assert E.problems(t) == []
    assert not t.startswith('---')                  # sent to the platform as is: no front matter
    assert t.lstrip().startswith('$$')
    assert '```lean\ntheorem lemA' in t
    assert '`lemA_oai`' in t and '`dite_eq_left`' in t and '`FAMQ000`' in t and '`Def_Fam`' in t
    assert 'OpenAI' in t and '2 declarations' in t
    assert 'no `sorry`' in t


def test_explanation_names_imported_statements_and_never_claims_sorry_free_wrongly(tmp_path):
    d, _ = make_carve(tmp_path)
    P = d / 'publish'
    # the forced node's piece: written by hand, but the function itself renders any piece
    plan = json.loads((P / 'plan.json').read_text())
    ctx = T.Context(str(d), META)
    t = T.explanation(ctx, 'OAI.Fam.named')
    assert '`OAI.Fam.Lemmas.lemA`' in t and E.problems(t) == []
    (P / 'out/solutions/Sol_OAI_Fam_named.lean').write_text(SOL_NAMED.replace(':= rfl', ':= by sorry'))
    t = T.explanation(T.Context(str(d), META), 'OAI.Fam.named')
    assert 'no `sorry`' not in t
    assert plan['pieces']['OAI.Fam.named']['imports'] == ['OAI.Fam.Lemmas.lemA']


def test_generated_text_passes_check_text_and_the_pronoun_check(tmp_path, capsys):
    d, ws = make_carve(tmp_path)
    run(d)
    with pytest.raises(SystemExit) as e:
        CP.cmd_check_text([str(d / 'publish'), '--ws', str(ws)])
    out = capsys.readouterr().out
    assert e.value.code == 0, out
    # a Lean binder named `he` inside a fenced code block is code, not a pronoun
    assert PR.scan_local([str(d / 'publish' / 'prose'), str(d / 'publish' / 'explanations')]) == []


def test_pronoun_check_still_sees_prose_outside_code_blocks(tmp_path):
    f = tmp_path / 'x.md'
    f.write_text('```lean\ntheorem t (he : 1 ≤ n) : True\n```\nThe author says he proved it.\n')
    hits = PR.scan_local([str(f)])
    assert [h[1] for h in hits] == [4]


def test_check_text_skips_fenced_lean(tmp_path):
    md = 'Text.\n\n```lean\ntheorem t (hdet : x) : `foo_bar` True\n```\n'
    assert CP.missing_names(md, '', lambda n: False) == []


def test_check_text_accepts_openai_name_when_only_its_suffixed_statement_is_published():
    md = 'The declaration `OAI.Foo.bar_lemma` of OpenAI.\n'
    local = 'lemma bar_lemma_q44 (x : Nat) : x = x := rfl'
    assert CP.missing_names(md, local, lambda n: False) == ['OAI.Foo.bar_lemma']
    assert CP.missing_names(md, local, lambda n: False, suffix='_q44') == []


def test_reruns_regenerate_templates_but_keep_written_prose(tmp_path):
    d, _ = make_carve(tmp_path)
    run(d)
    P = d / 'publish'
    f = P / 'prose' / 'OAI_Fam_Lemmas_lemA.md'
    first = f.read_text()
    # an unchanged template is regenerated (same text)
    rep = run(d)
    assert f.read_text() == first and 'prose/OAI_Fam_Lemmas_lemA.md' in rep['written']
    # an edited one is written prose: kept, unless --force
    f.write_text(first.replace('OpenAI', 'OpenAI (edited)', 1))
    rep = run(d)
    assert 'OpenAI (edited)' in f.read_text() and 'prose/OAI_Fam_Lemmas_lemA.md' in rep['kept']
    # a hand-written explanation (never generated) is kept too
    x = P / 'explanations' / 'OAI_Fam_Lemmas_lemA.md'
    x.write_text('hand written')
    (P / 'explanations' / T.MANIFEST).unlink()
    rep = run(d)
    assert x.read_text() == 'hand written' and 'explanations/OAI_Fam_Lemmas_lemA.md' in rep['kept']
    rep = run(d, force=True)
    assert f.read_text() == first and x.read_text() != 'hand written'


def test_is_template_tells_generated_from_written(tmp_path):
    d, _ = make_carve(tmp_path)
    run(d)
    P = str(d / 'publish')
    assert T.is_template(P, 'prose/FAMQ000.md')
    assert T.is_template(P, 'explanations/OAI_Fam_Lemmas_lemA.md')
    m = json.load(open(os.path.join(P, 'explanations', T.MANIFEST)))
    t = open(os.path.join(P, 'explanations', 'OAI_Fam_Lemmas_lemA.md'), 'rb').read()
    assert m['OAI_Fam_Lemmas_lemA.md'] == hashlib.sha1(t).hexdigest()


def test_meta_is_required_and_checked(tmp_path):
    d, _ = make_carve(tmp_path)
    os.remove(str(d / 'oai_meta.json'))
    with pytest.raises(SystemExit, match='oai_meta.json'):
        run(d)
    (d / 'oai_meta.json').write_text(json.dumps(dict(META, commit='adc7f12')))
    with pytest.raises(SystemExit, match='commit'):
        run(d)


def test_cli_reports_written_and_needs_written(tmp_path, capsys):
    d, _ = make_carve(tmp_path)
    CP.main(['prose-template', str(d)])
    out = capsys.readouterr().out
    assert 'wrote prose/OAI_Fam_Lemmas_lemA.md' in out
    assert 'needs written prose: statement OAI.Fam.named (forced)' in out
    assert 'needs written prose: explanation OAI.main (goal)' in out


def test_stub_statement_reads_an_indented_theorem():
    # OpenAI's VariableWL source starts its theorem lines with one space (2026-10-26)
    text = ("namespace OAI\n\nnamespace VariableWL\n theorem general_hard : \u2200R : Language, InEXPTIME R \u2192 "
            "PolytimeReduces R WL := by\n  sorry\nend VariableWL\n\nend OAI\n")
    decl, ns, opens = T.stub_statement(text)
    assert decl.strip().startswith('theorem general_hard') and 'sorry' not in decl
    assert ns == 'OAI.VariableWL'
