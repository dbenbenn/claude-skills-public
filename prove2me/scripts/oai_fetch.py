#!/usr/bin/env python3
"""Fetch an openai/math module's OAI.* import closure at a commit, into DEST/lean/... (files already
there are reused). Network reads only.

usage: oai_fetch.py DEST ROOT_MODULE [--commit SHA] [EXTRA_PATH ...]   (EXTRA_PATH relative to lean/)
  default commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a (the release the published OAI goals
  were generated from)."""
import os
import re
import sys
import time
import urllib.request

COMMIT = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'


def fetch(dest, root, commit=COMMIT, extra=()):
    def get(rel):
        p = os.path.join(dest, 'lean', rel)
        if os.path.exists(p):
            return open(p, encoding='utf-8').read()
        url = 'https://raw.githubusercontent.com/openai/math/%s/lean/%s' % (commit, rel)
        for i in range(4):
            try:
                t = urllib.request.urlopen(url, timeout=60).read().decode('utf-8')
                break
            except Exception as e:
                if i == 3:
                    raise SystemExit('fetch failed %s: %s' % (url, e))
                time.sleep(2 * (i + 1))
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'w', encoding='utf-8').write(t)
        return t
    seen, todo, total = set(), [root], 0
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        t = get(m.replace('.', '/') + '.lean')
        total += len(t.encode())
        for imp in re.findall(r'^import\s+(\S+)', t, re.M):
            if imp.split('.')[0] in ('OAI', 'ComparatorChallenges'):
                todo.append(imp)
    for rel in extra:
        get(rel)
    return len(seen), total


def main(argv):
    args = [a for a in argv]
    commit = COMMIT
    if '--commit' in args:
        i = args.index('--commit')
        commit = args[i + 1]
        del args[i:i + 2]
    if len(args) < 2:
        sys.exit(__doc__)
    n, total = fetch(args[0], args[1], commit, args[2:])
    print('%d modules, %d bytes' % (n, total))


if __name__ == '__main__':
    main(sys.argv[1:])
