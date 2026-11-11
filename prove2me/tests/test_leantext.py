

def test_import_names_reads_module_system_forms():
    # OpenAI's sources use `public import`, `meta import` and `import all M` (oaiq-093, RiemannDiskSeed); the closure
    # walkers over raw OpenAI text read them all, and `import all M` is M
    from p2mlib.leantext import import_names
    t = ('module\nimport Mathlib.A\npublic import OAI.B\npublic meta import OAI.C\nimport all OAI.D\n'
         'meta import OAI.E\n-- import OAI.F\n\ndef x := 1\n')
    assert import_names(t) == ['Mathlib.A', 'OAI.B', 'OAI.C', 'OAI.D', 'OAI.E']


def test_strip_leanarchitect_removes_the_blueprint_annotations():
    # oaiq-083, q233: PrimeNumberTheoremAnd's sources carry LeanArchitect annotations (`import Architect`, multi-line
    # `@[blueprint …]` attributes with nested doc comments and strings, `blueprint_comment /-- … -/`, `set_option
    # lang.lemmaCmd`), which our toolchain lacks; oaiq-083's prep_upstream.py stripped them by hand
    from p2mlib.leantext import strip_leanarchitect
    t = ('import Mathlib.Analysis.Complex.Basic\nimport Architect\npublic import Architect.Basic\n\n'
         'set_option lang.lemmaCmd true\n\nopen Complex\n\n'
         'blueprint_comment /--\nIn this section, we prove the Perron formula (see `]` and /- nested -/).\n-/\n\n'
         '@[blueprint\n  (title := "SmoothExistence")\n  (statement := /--\n  A [bracket] "and a quote\n  -/)\n'
         '  (proof := /-- uses \\ref{x} -/)\n  (latexEnv := "lemma")]\n'
         'theorem smooth_existence : True := trivial\n\n'
         '@[blueprint "D" (title := "x]y")] lemma short : True := trivial\n\n'
         '@[simp, blueprint "Z"]\ntheorem kept_simp : True := trivial\n\n'
         '-- @[blueprint\n/- @[blueprint "in a comment"] -/\n'
         'theorem uses_blueprint_word : True := by\n  -- the blueprint proof\n  trivial\n')
    out = strip_leanarchitect(t)
    assert out == ('import Mathlib.Analysis.Complex.Basic\n\n\nopen Complex\n\n\n'
                   'theorem smooth_existence : True := trivial\n\n'
                   'lemma short : True := trivial\n\n'
                   '@[simp]\ntheorem kept_simp : True := trivial\n\n'
                   '-- @[blueprint\n/- @[blueprint "in a comment"] -/\n'
                   'theorem uses_blueprint_word : True := by\n  -- the blueprint proof\n  trivial\n')
    assert strip_leanarchitect(out) == out
    plain = 'import Mathlib\n\ntheorem a : True := trivial\n'
    assert strip_leanarchitect(plain) == plain
