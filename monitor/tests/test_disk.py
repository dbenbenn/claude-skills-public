"""monitor.py: disk in use by category (dbenbenn 2026-11-02, after the disk filled on 2026-11-01)."""
import os

import monitor as M

K = 1024


def put(p, nbytes):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, 'wb') as f:
        f.write(b'\1' * nbytes)


def tree(tmp_path):
    """A home with every category's places; returns the roots disk_scan takes."""
    h = tmp_path / 'home'
    put(str(h / 'claude/ws/.lake/build/lib/A.olean'), 400 * K)
    put(str(h / 'claude/ws/.lake/packages/mathlib/.lake/build/M.olean'), 300 * K)   # a library's own build
    put(str(h / 'claude/ws/Solutions/A.lean'), 20 * K)
    put(str(h / 'claude/repo/.lake/build/B.olean'), 100 * K)
    put(str(h / 'claude/repo/.git/objects/x'), 30 * K)
    put(str(h / '.claude/jobs/oaiq-1/cv/olean/D.olean'), 200 * K)
    put(str(h / '.claude/projects/p/t.jsonl'), 50 * K)
    put(str(h / '.cache/mathlib/c.ltar'), 60 * K)
    put(str(h / '.cache/p2m/leaninfo/x.json'), 70 * K)
    put(str(h / '.elan/toolchains/lean'), 80 * K)
    put(str(tmp_path / 'tmp/scratch'), 90 * K)
    return {'claude': str(h / 'claude'), 'dotclaude': str(h / '.claude'), 'cache': str(h / '.cache'),
            'elan': str(h / '.elan'), 'tmp': str(tmp_path / 'tmp')}


def near(x, kib, slack=64):
    """du counts blocks: a file of n KiB takes n KiB plus at most a few blocks, and each directory a block."""
    return kib * K <= x <= (kib + slack) * K


def test_disk_scan_splits_by_category(tmp_path):
    c = M.disk_scan(tree(tmp_path))
    assert set(c) == set(M.DISK_CATS)
    assert near(c['lean_build'], 500)                # both .lake/build trees, not the packages
    assert near(c['lean_lib'], 300 + 80 + 60)        # .lake/packages (with their own builds), ~/.elan, mathlib cache
    assert near(c['jobs'], 200)
    assert near(c['sources'], 20 + 30)              # ~/claude outside .lake, .git included
    assert near(c['cache'], 70 + 50 + 90)            # other caches, ~/.claude outside jobs, /tmp


def test_disk_scan_skips_missing_roots(tmp_path):
    r = tree(tmp_path)
    r['elan'] = str(tmp_path / 'nope')
    r['tmp'] = str(tmp_path / 'nope2')
    c = M.disk_scan(r)
    assert near(c['lean_lib'], 300 + 60) and near(c['cache'], 70 + 50)


def test_disk_row_puts_the_unaccounted_rest_in_rest():
    G = M.G
    row = M.disk_row(1000, {k: 10 * G for k in M.DISK_CATS}, {'used': 80.0, 'total': 384.0, 'free': 300.0}, secs=42)
    assert row['cats']['rest'] == 30.0 and row['cats']['jobs'] == 10.0
    assert row == dict(row, t=1000, used=80.0, total=384.0, secs=42)
    over = M.disk_row(1000, {k: 20 * G for k in M.DISK_CATS}, {'used': 80.0, 'total': 384.0, 'free': 300.0})
    assert over['cats']['rest'] == 0                 # a scan that saw more than statvfs (it took minutes) never goes negative


def test_disk_scan_due_hourly_and_history_kept_30_days():
    rows = [{'t': t} for t in (0, 100, 3 * 86400)]
    assert M.disk_due(rows, now=3 * 86400 + M.DISK_EVERY - 1) is False
    assert M.disk_due(rows, now=3 * 86400 + M.DISK_EVERY) is True
    assert M.disk_due([], now=5) is True
    assert M.disk_keep(rows + [{'t': 40 * 86400}], now=40 * 86400) == [{'t': 40 * 86400}]


def test_low_disk_is_machine_trouble():
    assert M.pressure_alerts(None, free_gib=None, disk_free_gib=12.3) == ['only 12.3 GiB of disk free']
    assert M.pressure_alerts(None, free_gib=None, disk_free_gib=M.DISK_LOW_GIB + 1) == []


def test_status_banner_reports_low_disk():
    system = {'psi': [], 'free_gib': 40, 'swap_free_gib': 10, 'disk': {'now': {'used': 380, 'total': 384, 'free': 3.4}}}
    st = M.build_status(1000, [], [], system, [], [])
    assert 'only 3.4 GiB of disk free' in st['alerts']
