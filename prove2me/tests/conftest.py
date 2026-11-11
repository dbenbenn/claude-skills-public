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


def fake_olean(path, payload=64):
    """Write `path` as a minimal .olean that p2mlib.leaninfo.olean_ok accepts: the `olean` header, a base
    address, and a root pointer to an object 56 bytes before the end (as Lean writes one); `payload` bytes
    (a multiple of 8, at least 56) after the 96-byte header. Returns the path."""
    import struct
    base = 0x59cabc30000
    head = b'olean\x02\x01' + b'4.33.1'.ljust(33, b'\0') + b'0' * 40
    body = struct.pack('<QQ', base, base + 96 + payload - 56) + b'\0' * payload
    os.makedirs(os.path.dirname(str(path)) or '.', exist_ok=True)
    with open(str(path), 'wb') as f:
        f.write(head + body)
    return path


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


@pytest.fixture(autouse=True)
def private_monitor_home(monkeypatch, tmp_path):
    """Monitoring-page sections (p2mlib.carvemonitor, the monitor skill's section.py) go to a tmp dir,
    never the machine's page."""
    monkeypatch.setenv('MONITOR_HOME', str(tmp_path / 'monitor-home'))
