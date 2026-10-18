#!/usr/bin/env python3
"""Submit a solution file to POST /verify (multipart) and poll for the verdict.

usage: submit_verify.py [--disprove] [--also REASON] <theorem_id> <solution.lean> [explanation.md]

It refuses a theorem that already has a live proof (accepted, sketch-accepted or pending) and names
it: read that proof first (submit_solution.py saves it under others/ and compares edges). Pass
--also REASON (in code: also=REASON) to submit anyway, the reason saying why ours is meaningfully
different or what it replaces. submit_solution.py, which runs the fuller check itself, passes
checked=True.
"""
import json, os, sys, time, uuid, urllib.request, urllib.error
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import token, call


class ExistingProof(RuntimeError):
    """The theorem already has a live proof; a RuntimeError, so the split runner stops that item."""


def guard(theorem_id, also=None):
    from p2mlib.api import live_proofs
    if also and also.strip():
        return
    live = live_proofs(theorem_id, call=call)
    if live:
        raise ExistingProof(
            'theorem %s already has %d live proof(s): %s. Read it first (submit_solution.py saves it '
            'under others/ and compares edges); submit only if ours is meaningfully different or '
            'replaces it, saying why: also="<reason>" (CLI --also REASON).' % (
                theorem_id, len(live), '; '.join('%s %s %s by %s' % (p['id'], p.get('status'),
                                                  (p.get('created_at') or '')[:10], p.get('username'))
                                                  for p in live)))


def post_verify(theorem_id, path, explanation=None, proof_type=None, also=None, checked=False):
    if not checked:
        guard(theorem_id, also)
    boundary = '----p2m' + uuid.uuid4().hex
    parts = []

    def field(name, value):
        parts.append(('--' + boundary + '\r\n'
                      'Content-Disposition: form-data; name="%s"\r\n\r\n' % name
                      + value + '\r\n').encode('utf-8'))

    field('theorem_id', theorem_id)
    if proof_type:
        field('proof_type', proof_type)
    if explanation:
        field('explanation', explanation)
    body = open(path, 'rb').read()
    parts.append(('--' + boundary + '\r\n'
                  'Content-Disposition: form-data; name="file"; filename="solution.lean"\r\n'
                  'Content-Type: text/plain\r\n\r\n').encode('utf-8'))
    parts.append(body)
    parts.append(('\r\n--' + boundary + '--\r\n').encode('utf-8'))
    data = b''.join(parts)
    req = urllib.request.Request(
        'https://prove2.me/api/v1/verify', data=data, method='POST',
        headers={'Authorization': 'Bearer ' + token(),
                 'Content-Type': 'multipart/form-data; boundary=' + boundary})
    for attempt in (0, 1):
        try:
            with urllib.request.urlopen(req, timeout=300) as f:
                return json.loads(f.read().decode() or '{}')
        except urllib.error.HTTPError as e:
            if e.code == 401 and attempt == 0:    # the cached token expired: refresh once
                req.add_header('Authorization', 'Bearer ' + token(refresh=True))
                continue
            return {'__error': '%d %s' % (e.code, e.read().decode()[:600])}


def poll(sid, tries=240, delay=15):
    """The verdict, or {'status': 'PENDING', ...} after tries*delay seconds (p2mlib.api.poll_verdict)."""
    from p2mlib.api import poll_verdict
    return poll_verdict(sid, minutes=max(1, tries * delay // 60), every=delay, call=call)


def parse_args(argv):
    """(theorem_id, solution, explanation or None, proof_type or None, also or None)."""
    args, ptype, also, i = [], None, None, 0
    while i < len(argv):
        a = argv[i]
        if a == '--disprove':
            ptype = 'disprove'
        elif a == '--also':
            if i + 1 >= len(argv) or argv[i + 1].startswith('--') or not argv[i + 1].strip():
                sys.exit('--also needs a reason\n' + __doc__)
            also = argv[i + 1]; i += 1
        elif a.startswith('--'):
            # a mistyped flag (`--disproof`) must not silently submit a proof instead of a disproof
            sys.exit(__doc__)
        else:
            args.append(a)
        i += 1
    if len(args) not in (2, 3):
        sys.exit(__doc__)
    return args[0], args[1], (args[2] if len(args) > 2 else None), ptype, also


if __name__ == '__main__':
    # `--disprove` sends proof_type=disprove: the solution must prove the negation of the whole
    # quantified statement, and may import Definitions.Def_* and Mathlib but not Theorems.Thm_*.
    tid, path, epath, ptype, also = parse_args(sys.argv[1:])
    expl = open(epath, encoding='utf-8').read() if epath else None
    try:
        r = post_verify(tid, path, expl, ptype, also=also)
    except ExistingProof as e:
        sys.exit('REFUSED: %s' % e)
    print(json.dumps(r, indent=1)[:2000])
    sid = r.get('submission_id')
    if not sid:
        sys.exit(1)
    print('POLLING', sid)
    v = poll(sid)
    print(json.dumps(v, indent=1)[:3000])
    # exit status is the verdict, so a caller in a loop cannot mistake a rejection for success
    sys.exit(0 if v.get('status') in ('ACCEPTED', 'SKETCH_ACCEPTED') else 1)
