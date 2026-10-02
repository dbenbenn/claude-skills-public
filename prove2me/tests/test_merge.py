"""merge.py: concatenate modules into one solution file (run as the CLI, as build_solutions does)."""
import os
import subprocess
import sys

from conftest import SCRIPTS


def merge(tmp_path, *mods):
    paths = []
    for i, text in enumerate(mods):
        p = tmp_path / ('M%d.lean' % i)
        p.write_text(text)
        paths.append(str(p))
    out = tmp_path / 'out.lean'
    r = subprocess.run([sys.executable, os.path.join(SCRIPTS, 'merge.py'), str(out)] + paths,
                       capture_output=True, text=True)
    return r, (out.read_text() if out.exists() else '')


def test_same_short_name_in_different_namespaces_is_not_a_clash(tmp_path):
    # 5bc26ab: CFP §6's S6.W and S6.CoxA.W were refused as a clash
    r, out = merge(tmp_path, 'namespace S6\ndef W : Nat := 1\nend S6\n',
                   'namespace S6.CoxA\ndef W : Nat := 2\nend S6.CoxA\n')
    assert r.returncode == 0, r.stderr
    assert out.count('def W') == 2


def test_true_duplicate_is_dropped_and_clash_refused(tmp_path):
    r, out = merge(tmp_path, 'theorem t : True := trivial\n', 'theorem t : True := trivial\n')
    assert r.returncode == 0 and out.count('theorem t ') == 1
    r, _ = merge(tmp_path, 'theorem t : True := trivial\n', 'theorem t : True := by trivial\n')
    assert r.returncode != 0 and 'refusing' in (r.stdout + r.stderr)


def test_dropping_a_duplicate_keeps_the_next_lemmas_attribute(tmp_path):
    # merge.blocks docstring: a dropped duplicate once stripped the `@[simp]` off the lemma after it
    r, out = merge(tmp_path, 'theorem t : True := trivial\n',
                   'theorem t : True := trivial\n@[simp] theorem u : True := trivial\n')
    assert r.returncode == 0 and '@[simp] theorem u' in out


def test_each_module_is_its_own_section(tmp_path):
    # Monod 2026-09-30: one module's `open` leaked into the next and made a name ambiguous
    r, out = merge(tmp_path, 'open Nat\ntheorem a : True := trivial\n', 'theorem b : True := trivial\n')
    assert r.returncode == 0
    a, b = out.index('open Nat'), out.index('theorem b')
    assert 'end' in out[a:b]


def test_universe_levels_declared_once(tmp_path):
    r, out = merge(tmp_path, 'universe u v\ndef f (α : Type u) : Type u := α\n',
                   'universe u\ndef g (α : Type u) : Type u := α\n')
    assert r.returncode == 0
    assert sum(1 for l in out.split('\n') if l.startswith('universe') and ' u' in l) == 1


def test_existing_solution_refused(tmp_path):
    r, _ = merge(tmp_path, 'theorem solution : True := trivial\n')
    assert r.returncode != 0
