"""Live, read-only contract tests: prove2.me behaves the way our scripts assume.

Run with P2M_LIVE=1. Every assumption here once broke a script:
  * list pages are capped (a single /missions call returned 50 of ~1200; /submissions returned
    100 of 981) -- callers must paginate;
  * GET /submissions/:id/solution serves any submission's source (we wrongly believed it did not,
    2026-09-24 to 2026-10-02);
  * graph sketch nodes carry submission_id / parent_theorem_id / status / deprecated_at, and
    sketch edges point at 'sketch-<sid>';
  * GET /submissions/:id reports deprecated_at (the list endpoint does not).
The fixtures are public items of our own missions."""
import pytest

pytestmark = pytest.mark.live

CHORNYI_COR3 = 'c7bf7b0c-d905-4721-a2c6-b010d814b0ea'      # ThompsonAmenability Cor 3 (public)
KEPT = '666719da-8f0a-4c56-aa09-ac8fa41b2b02'               # its live proof
DEPRECATED = 'ee5164fb-5ea4-4ef3-b5f9-d14baf40c6ee'         # its deprecated duplicate


@pytest.fixture(scope='module')
def call():
    from p2m import call
    return call


def test_missions_list_is_paged(call):
    first = call('GET', '/missions?limit=100&offset=0')['missions']
    assert 0 < len(first) <= 100
    second = call('GET', '/missions?limit=100&offset=%d' % len(first))['missions']
    assert second and {m['id'] for m in first}.isdisjoint(m['id'] for m in second)


def test_submissions_list_reports_total_and_pages(call):
    d = call('GET', '/submissions?page=1')
    assert 'total' in d and d['total'] > len(d['submissions'])


def test_submission_source_is_served(call):
    r = call('GET', '/submissions/%s/solution' % KEPT)
    assert 'theorem solution' in r['content']


def test_deprecation_visible_on_detail_endpoint(call):
    assert call('GET', '/submissions/' + DEPRECATED).get('deprecated_at') not in (None, 'None')
    assert call('GET', '/submissions/' + KEPT).get('deprecated_at') in (None, 'None')


def test_graph_sketch_shape(call):
    g = call('GET', '/theorems/%s/graph' % CHORNYI_COR3)
    sketches = [n for n in g['nodes'] if n.get('node_type') == 'sketch']
    keys = {'submission_id', 'parent_theorem_id', 'status', 'deprecated_at'}
    assert sketches and all(keys <= set(n) for n in sketches)
    assert any(e['target'] == 'sketch-' + KEPT for e in g['edges'])
    # a deprecated sketch is hidden from the graph
    assert not any(n['submission_id'] == DEPRECATED for n in sketches)


def test_verify_reports_final_status_for_old_submission(call):
    assert call('GET', '/verify?submission_id=' + KEPT).get('status') == 'ACCEPTED'
