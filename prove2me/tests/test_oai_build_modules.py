"""scripts/oai_build_modules.py: module names may end in a prime (OpenAI's IntegralDensityMeasureLp'
beside IntegralDensityMeasureLp; WeakHessian, oaiq-052)."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts'))
import oai_build_modules as B  # noqa: E402


def test_module_imports_keep_a_trailing_prime(tmp_path):
    (tmp_path / 'A.lean').write_text("import Mathlib\nimport P.B'\nimport P.C\nimport P.D.E'\n")
    assert B.module_imports(str(tmp_path), 'P', 'A') == ["B'", 'C', "D.E'"]
