

def test_import_names_reads_module_system_forms():
    # OpenAI's sources use `public import`, `meta import` and `import all M` (oaiq-093, RiemannDiskSeed); the closure
    # walkers over raw OpenAI text read them all, and `import all M` is M
    from p2mlib.leantext import import_names
    t = ('module\nimport Mathlib.A\npublic import OAI.B\npublic meta import OAI.C\nimport all OAI.D\n'
         'meta import OAI.E\n-- import OAI.F\n\ndef x := 1\n')
    assert import_names(t) == ['Mathlib.A', 'OAI.B', 'OAI.C', 'OAI.D', 'OAI.E']
