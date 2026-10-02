"""Shared test setup for the prove2me scripts (see scripts/ENGINEERING_PLAN.md, "Test layers").

Markers:
  live  -- talks to prove2.me (read-only); skipped unless P2M_LIVE=1
  lean  -- runs the Lean toolchain in the prove2me workspace; skipped unless P2M_LEAN=1
"""
import os
import sys

import pytest

SCRIPTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'scripts')
sys.path.insert(0, SCRIPTS)


def pytest_configure(config):
    config.addinivalue_line('markers', 'live: read-only calls to prove2.me (P2M_LIVE=1 to run)')
    config.addinivalue_line('markers', 'lean: runs Lean in the workspace (P2M_LEAN=1 to run)')


def pytest_collection_modifyitems(config, items):
    for item in items:
        if 'live' in item.keywords and os.environ.get('P2M_LIVE') != '1':
            item.add_marker(pytest.mark.skip(reason='live platform test; set P2M_LIVE=1'))
        if 'lean' in item.keywords and os.environ.get('P2M_LEAN') != '1':
            item.add_marker(pytest.mark.skip(reason='Lean test; set P2M_LEAN=1'))
