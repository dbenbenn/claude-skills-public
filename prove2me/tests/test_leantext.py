import re


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


def _data_line(n):
    # q259's shape: one `def` whose value is a nested term on a single line
    return 'def big : Nat := ' + 'Nat.add 0 (' * n + '0' + ')' * n


def test_wrap_long_lines_breaks_a_long_data_line_inside_brackets_only():
    from p2mlib.leantext import wrap_long_lines
    line = _data_line(4000)                                  # ~48k characters
    text = 'import Mathlib\n\n%s\n\ntheorem t : True := trivial\n' % line
    out, left = wrap_long_lines(text, limit=20000, width=1500)
    assert left == []
    body = out.split('\n')[2:-3]
    assert max(len(x) for x in body[:-1]) < 1600 and body[-1].rstrip(')').endswith('0')   # a run of `)` has no space
    assert re.sub(r'\s+', ' ', out) == re.sub(r'\s+', ' ', text)       # whitespace only
    for x in body[1:]:
        assert x.startswith('    (') or x.startswith('    Nat.add')   # a continuation, inside the term
    assert out.split('\n')[0] == 'import Mathlib' and 'theorem t : True := trivial' in out
    assert wrap_long_lines(text, limit=len(line)) == (text, [])      # nothing over the limit: unchanged


def test_wrap_long_lines_keeps_literals_comments_and_column_sensitive_lines():
    from p2mlib.leantext import wrap_long_lines
    s = '"' + 'a b (c ' * 400 + '"'
    lit = 'def s : List String := [' + ', '.join([s] * 20) + ']'           # spaces inside strings only... and after commas
    out, left = wrap_long_lines(lit, limit=20000, width=1500)
    assert left == [] and all(s in out for _ in [0])                     # no string was cut
    assert re.sub(r'\s+', ' ', out) == re.sub(r'\s+', ' ', lit)
    tactic = 'theorem x : P := (by ' + 'simp; ' * 5000 + 'rfl)'          # a tactic block: columns matter
    out, left = wrap_long_lines('-- c\n' + tactic, limit=20000)
    assert out == '-- c\n' + tactic and left == [2]
    com = '/- ' + 'x (y ' * 6000 + '-/'                                 # a comment has no code to break
    assert wrap_long_lines(com, limit=20000) == (com, [])
