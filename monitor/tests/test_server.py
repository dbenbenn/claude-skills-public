"""The monitor's HTTP routes: pages and static files, /agents.json, /agent/<name>/<file>, quota in status."""
import json
import threading
import urllib.error
import urllib.request
from http.server import ThreadingHTTPServer

import pytest

import agents as A
import monitor as M
from test_agents import make_agent, rl


@pytest.fixture
def server(tmp_path, monkeypatch):
    www = tmp_path / 'site' / 'www'
    (www / 'vendor').mkdir(parents=True)
    (www / 'index.html').write_text('<h1>main</h1>')
    (www / 'agent.html').write_text('<h1>log</h1>')
    (www / 'app.js').write_text('1')
    (www / 'vendor' / 'lib.js').write_text('2')
    (www / 'secret.py').write_text('print(1)')
    (tmp_path / 'site' / 'outside.js').write_text('x')
    root = tmp_path / 'agents'
    root.mkdir()
    monkeypatch.setattr(M, 'HERE', str(tmp_path / 'site'))
    monkeypatch.setattr(A, 'AGENTS_DIR', str(root))
    monkeypatch.setattr(A, 'JOBS_DIR', str(tmp_path / 'jobs'))
    monkeypatch.setattr(A, 'PORTS_DIR', str(tmp_path / 'ports'))
    monkeypatch.setattr(M.State, 'agents', (0, b'{}'))
    monkeypatch.setattr(M.State, 'status', b'{"ok": true}')
    srv = ThreadingHTTPServer(('127.0.0.1', 0), M.Handler)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    yield 'http://127.0.0.1:%d' % srv.server_port, root
    srv.shutdown()


def get(base, path):
    try:
        r = urllib.request.urlopen(base + path)
        return r.status, r.read(), r.headers
    except urllib.error.HTTPError as e:
        return e.code, e.read(), e.headers


def test_pages_and_static_assets(server):
    base, _ = server
    assert get(base, '/')[1] == b'<h1>main</h1>'
    assert get(base, '/page/agent.html')[1] == b'<h1>log</h1>'
    s, b, h = get(base, '/app.js')
    assert s == 200 and h['Content-Type'] == 'text/javascript'
    assert get(base, '/vendor/lib.js')[0] == 200
    assert get(base, '/status.json')[1] == b'{"ok": true}'
    for bad in ('/secret.py', '/page/secret.py', '/../outside.js', '/%2e%2e/outside.js', '/vendor/../../outside.js',
                '/vendor/', '/page/missing.html', '/.hidden.js', '//etc/passwd.js'):
        assert get(base, bad)[0] == 404, bad


def test_agents_json_route(server):
    base, root = server
    make_agent(root, 'oaiq-001')
    s, b, _ = get(base, '/agents.json')
    d = json.loads(b)
    assert s == 200 and [r['name'] for r in d['running']] == ['oaiq-001'] and d['recent'] == []


def test_agent_file_route_allowlist_and_ranges(server):
    base, root = server
    make_agent(root, 'a1', transcript='l1\nl2\nl3\n')
    (root / 'a1' / 'unit.log').write_text('secret')
    s, b, h = get(base, '/agent/a1/transcript.jsonl')
    assert s == 200 and b == b'l1\nl2\nl3\n' and h['X-End'] == '9' and h['X-Size'] == '9'
    s, b, h = get(base, '/agent/a1/transcript.jsonl?from=3')
    assert b == b'l2\nl3\n' and h['X-Start'] == '3'
    assert get(base, '/agent/a1/transcript.jsonl?from=-4')[1] == b'l3\n'
    assert get(base, '/agent/a1/transcript.jsonl?from=x')[0] == 400
    assert json.loads(get(base, '/agent/a1/state.json')[1])['state'] == 'running'
    assert get(base, '/agent/a1/brief.md')[1] == b'# brief'
    for bad in ('/agent/a1/unit.log', '/agent/a1/last_text.txt', '/agent/../state.json', '/agent/a1/../a1/state.json',
                '/agent/a1/%2e%2e/a1/state.json', '/agent/nope/state.json', '/agent/a1', '/agent/a1/state.json/x',
                '/agent/%2e%2e/queue/registry.json'):
        assert get(base, bad)[0] == 404, bad


def test_agent_file_route_caps_response_size(server):
    base, root = server
    make_agent(root, 'big', transcript='x' * 99 + '\n' * 1)
    (root / 'big' / 'transcript.jsonl').write_text(('y' * 99 + '\n') * 20000)      # 2 MB
    s, b, h = get(base, '/agent/big/transcript.jsonl?max=99999999')
    assert s == 200 and len(b) <= A.MAX_BYTES and b.endswith(b'\n') and int(h['X-Size']) == 2000000
    s, b, h = get(base, '/agent/big/transcript.jsonl?from=-1000000&max=1000')
    assert len(b) <= 1000
    (root / 'big' / 'brief.md').write_text('z' * (A.MAX_BYTES + 5000))
    assert len(get(base, '/agent/big/brief.md')[1]) == A.MAX_BYTES


def test_symlink_out_of_agent_dir_is_not_served(server, tmp_path):
    base, root = server
    d = make_agent(root, 'a1')
    (tmp_path / 'private.txt').write_text('private')
    (d / 'brief.md').unlink()
    (d / 'brief.md').symlink_to(tmp_path / 'private.txt')
    assert get(base, '/agent/a1/brief.md')[0] == 404


def test_step_adds_quota_and_costs(tmp_path, monkeypatch):
    root = tmp_path / 'agents'
    root.mkdir()
    make_agent(root, 'a', transcript=rl(0.2, 0.5))
    monkeypatch.setattr(A, 'AGENTS_DIR', str(root))
    home = tmp_path / 'home'
    M.step(str(home), now=1793010000)
    st = json.loads((home / 'state' / 'status.json').read_text())
    assert st['quota']['series'][-1][:2] == [1793010000, 20.0]
    assert json.loads((home / 'state' / 'agent_costs.json').read_text())['a'][-1][1] == 1.5
