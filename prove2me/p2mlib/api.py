"""The prove2.me API client -- the one copy (it was p2m.py, with paging, polling and the graph
helpers re-implemented per script).

Every assumption here is pinned by tests/test_live_contract.py, which sync_workspace.py runs at
the start of each session:
* lists are paged: `paginate` (offset/limit; a short page ends the list, which is right only
  because `limit=100` really returns 100 while more exist) and `paginate_numbered` (`?page=N`,
  which reports `total`; an unpaginated GET /submissions once returned 100 of 981);
* a verdict that has not arrived is PENDING, never a rejection (`poll_verdict`; a 21-minute
  compile was once reported as "not accepted: None");
* any submission's Lean source is served (`submission_source`);
* a deprecated proof is hidden from the graph, and only GET /submissions/:id says deprecated_at.
"""
import json
import os
import sys
import time
import urllib.error
import urllib.request

from .leantext import strip
from .workspace import workspace

BASE = 'https://prove2.me/api/v1'
LIVE = ('ACCEPTED', 'SKETCH_ACCEPTED')
_token = None


def _api_key():
    return json.load(open(os.path.join(workspace(), 'credentials.json')))['api_key']


def token(refresh=False):
    """Access tokens last an hour; `call` refreshes on a 401, so a long watch does not go blind."""
    global _token
    if _token is None or refresh:
        req = urllib.request.Request(BASE + '/agent/refresh', data=json.dumps({'api_key': _api_key()}).encode(),
                                     headers={'Content-Type': 'application/json'})
        _token = json.load(urllib.request.urlopen(req))['access_token']
    return _token


def no_frozen_comments(body):
    """A published statement carries no comment: `formal_statement` and `preamble` freeze at
    publish and the blind read-back never sees comments, so one is unauditable and unfixable.
    Detection is literal-aware (`"a--b"` is not a comment); definition bundles are untouched.
    P2M_ALLOW_DOCSTRING=1 overrides deliberately."""
    if os.environ.get('P2M_ALLOW_DOCSTRING') == '1' or not isinstance(body, dict):
        return
    for part in [body] + list(body.get('problems') or []):
        for field in ('formal_statement', 'preamble'):
            fs = part.get(field) if isinstance(part, dict) else None
            if fs and ('--' in fs or '/-' in fs) and strip(fs).split() != fs.split():
                raise SystemExit('refusing: %s carries a comment, which freezes at publish and is never read '
                                 'back. Put it in natural_language_statement, or set P2M_ALLOW_DOCSTRING=1.' % field)


def call(method, path, body=None):
    """One request; dict back. Retries 5xx/429 and network errors with backoff, refreshes an expired
    token once; any other error comes back as {'__error': '<code> <text>'}."""
    if method in ('POST', 'PATCH'):
        no_frozen_comments(body)
    url = BASE + path
    data = json.dumps(body).encode() if body is not None else None
    headers = {'Authorization': 'Bearer ' + token()}
    if data:
        headers['Content-Type'] = 'application/json'
    refreshed = False
    for attempt in range(3):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, data=data, headers=headers, method=method),
                                        timeout=180) as f:
                return json.loads(f.read().decode() or '{}')
        except urllib.error.HTTPError as e:
            if e.code >= 500 or e.code == 429:
                time.sleep(6 * (attempt + 1)); continue
            if e.code == 401 and not refreshed:
                refreshed = True
                headers['Authorization'] = 'Bearer ' + token(refresh=True); continue
            return {'__error': '%d %s' % (e.code, e.read().decode()[:400])}
        except Exception:
            time.sleep(4 * (attempt + 1))
    return {'__error': 'retries exhausted'}


def paginate(path, key, limit=100, call=None):
    """Every item of an offset-paged list (`/missions`, `/theorems?…`)."""
    call = call or globals()['call']
    out, off = [], 0
    while True:
        r = call('GET', '%s%slimit=%d&offset=%d' % (path, '&' if '?' in path else '?', limit, off))
        page = (r.get(key) if isinstance(r, dict) else None) or []
        out += page
        if len(page) < limit:
            return out
        off += limit


def paginate_numbered(path, key, call=None):
    """Every item of a page-numbered list that reports `total` (`/submissions`)."""
    call = call or globals()['call']
    out, page = [], 1
    while True:
        r = call('GET', '%s%spage=%d' % (path, '&' if '?' in path else '?', page))
        batch = (r.get(key) if isinstance(r, dict) else None) or []
        out += batch
        if not batch or len(out) >= (r.get('total') or 0):
            return out
        page += 1


def poll_verdict(sid, minutes=60, every=15, call=None, sleep=time.sleep):
    """The verdict of a submission: its final record, or {'status': 'PENDING', ...} after `minutes`."""
    call = call or globals()['call']
    for _ in range(max(1, minutes * 60 // every)):
        r = call('GET', '/verify?submission_id=' + sid)
        if r.get('status') and r.get('status') != 'PENDING':
            return r
        sleep(every)
    return {'status': 'PENDING', '__error': 'no verdict after %d minutes' % minutes}


def submission_source(sid, call=None):
    """The exact solution.lean of any submission, or None."""
    call = call or globals()['call']
    r = call('GET', '/submissions/%s/solution' % sid)
    return r.get('content') if isinstance(r, dict) else None


def live_sketch_edges(tid, call=None):
    """{submission id: set of theorem names it imports} for the live (accepted, not deprecated)
    proofs of theorem `tid`, from its graph."""
    call = call or globals()['call']
    g = call('GET', '/theorems/%s/graph' % tid)
    names = {n.get('theorem_id'): n.get('theorem_name') for n in g.get('nodes', []) if n.get('node_type') == 'theorem'}
    out = {}
    for n in g.get('nodes', []):
        if n.get('node_type') != 'sketch' or n.get('parent_theorem_id') != tid \
                or n.get('status') not in LIVE or n.get('deprecated_at') not in (None, 'None'):
            continue
        node = 'sketch-' + n['submission_id']
        out[n['submission_id']] = {names[e['source']] for e in g.get('edges', [])
                                   if e['target'] == node and '.' in (names.get(e['source']) or '')}
    return out


def theorem_id(name, call=None):
    """The id of the published theorem named exactly `name`, or None."""
    call = call or globals()['call']
    r = call('GET', '/theorems?theorem_name=%s&limit=5' % name)
    hit = [t for t in (r.get('theorems') or []) if t.get('theorem_name') == name]
    return (hit[0].get('id') or hit[0].get('theorem_id')) if hit else None
