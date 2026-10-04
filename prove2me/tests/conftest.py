"""Shared test setup for the prove2me scripts (see scripts/README.md, "Tests").

Markers:
  live  -- talks to prove2.me (read-only); skipped unless P2M_LIVE=1
  lean  -- runs the Lean toolchain in the prove2me workspace; skipped unless P2M_LEAN=1
"""
import os
import sys

import pytest

SCRIPTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts')
sys.path.insert(0, SCRIPTS)
sys.path.insert(0, os.path.dirname(SCRIPTS))          # p2mlib


def pytest_configure(config):
    config.addinivalue_line('markers', 'live: read-only calls to prove2.me (P2M_LIVE=1 to run)')
    config.addinivalue_line('markers', 'lean: runs Lean in the workspace (P2M_LEAN=1 to run)')


def pytest_collection_modifyitems(config, items):
    for item in items:
        if 'live' in item.keywords and os.environ.get('P2M_LIVE') != '1':
            item.add_marker(pytest.mark.skip(reason='live platform test; set P2M_LIVE=1'))
        if 'lean' in item.keywords and os.environ.get('P2M_LEAN') != '1':
            item.add_marker(pytest.mark.skip(reason='Lean test; set P2M_LEAN=1'))



@pytest.fixture(autouse=True)
def no_live_submissions(monkeypatch):
    """No test reaches POST /verify: a submit test whose refusal regresses would otherwise submit for
    real (no live-write tests). A test that needs a verdict monkeypatches post_verify itself."""
    import submit_verify

    def refuse(*a, **k):
        raise AssertionError('a test reached POST /verify')
    monkeypatch.setattr(submit_verify, 'post_verify', refuse)
