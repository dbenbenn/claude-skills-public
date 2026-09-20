#!/usr/bin/env python3
"""Submit a solution file to POST /verify (multipart) and poll for the verdict.

usage: submit_verify.py [--disprove] <theorem_id> <solution.lean> [explanation.md]
"""
import json, os, sys, time, uuid, urllib.request, urllib.error
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import token, call


def post_verify(theorem_id, path, explanation=None, proof_type=None):
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
    try:
        with urllib.request.urlopen(req, timeout=300) as f:
            return json.loads(f.read().decode() or '{}')
    except urllib.error.HTTPError as e:
        return {'__error': '%d %s' % (e.code, e.read().decode()[:600])}


def poll(sid, tries=80, delay=15):
    for _ in range(tries):
        r = call('GET', '/verify?submission_id=' + sid)
        st = r.get('status')
        if st and st != 'PENDING':
            return r
        time.sleep(delay)
    return {'__error': 'timeout waiting for verdict'}


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    # `--disprove` sends proof_type=disprove: the solution must prove the negation of the whole
    # quantified statement, and may import Definitions.Def_* and Mathlib but not Theorems.Thm_*.
    ptype = 'disprove' if '--disprove' in sys.argv else None
    tid, path = args[0], args[1]
    expl = open(args[2], encoding='utf-8').read() if len(args) > 2 else None
    r = post_verify(tid, path, expl, ptype)
    print(json.dumps(r, indent=1)[:2000])
    sid = r.get('submission_id')
    if sid:
        print('POLLING', sid)
        print(json.dumps(poll(sid), indent=1)[:3000])
