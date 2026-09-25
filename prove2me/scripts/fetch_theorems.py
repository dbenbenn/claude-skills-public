#!/usr/bin/env python3
"""Write a mission's published statements into the workspace, so solutions can import them.

usage: fetch_theorems.py MISSION_ID_OR_PREFIX [...] [--out DIR] [--no-build]
       fetch_theorems.py --proposal PROPOSAL_ID [--out DIR] [--no-build]

--proposal is for the window between Submit and approval: the statements are published but the
mission does not exist yet, so each item's theorem is looked up by its exact name instead.

For every theorem of the missions, writes Theorems/Thm_<Name_with_underscores>.lean in server
shape (preamble + formal_statement, whose proof is `sorry`), and for every definition bundle
Definitions/Def_<name>.lean from its published code -- the exact text the verifier compiles an
import against. A file whose content is already right is left alone, so `lake build` rebuilds only
what changed; the modules are then built and any failure is reported.

Each mission used to carry its own fetch_thms.py reading a hand-kept published_ids.json; this one
asks the platform for the mission's theorems, so a statement added after launch is not missed.
--out writes somewhere else (for a comparison, say) and skips the build.
"""
import os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p2m import call
from prune_solution import _workspace


def paged(path, key):
    out, off = [], 0
    while True:
        r = call('GET', '%s%slimit=100&offset=%d' % (path, '&' if '?' in path else '?', off))
        b = r.get(key) or []
        out += b
        if len(b) < 100:
            return out
        off += 100


def main():
    args = sys.argv[1:]
    out_dir, build = None, '--no-build' not in args
    args = [a for a in args if a != '--no-build']
    if '--out' in args:
        i = args.index('--out'); out_dir = args[i + 1]; del args[i:i + 2]; build = False
    if not args or (args[0] != '--proposal' and any(a.startswith('--') for a in args)) \
            or (args[0] == '--proposal' and len(args) != 2):
        sys.exit(__doc__)
    ws = _workspace()
    root = out_dir or ws
    ids = []
    if args[0] == '--proposal':
        p = call('GET', '/mission-proposals/' + args[1])
        p = p.get('proposal', p)
        for it in p.get('items') or []:
            n = it.get('theorem_name') or it.get('definition_name')
            r = call('GET', '/theorems?theorem_name=%s&limit=5' % n)
            hit = [t for t in (r.get('theorems') or []) if t.get('theorem_name') == n]
            if hit:
                ids.append(hit[0].get('id') or hit[0].get('theorem_id'))
            else:
                print('   not published (yet?): %s' % n)
    else:
        missions = [m for m in paged('/missions', 'missions') if any(m['id'].startswith(a) for a in args)]
        if not missions:
            sys.exit('no mission matches %s' % args)
        for m in missions:
            ids += [t.get('id') or t.get('theorem_id') for t in paged('/theorems?mission_id=%s' % m['id'], 'theorems')]
    written, same, mods = [], 0, []
    for tid in ids:
        if True:
            d = call('GET', '/theorems/' + tid)
            d = d.get('theorem', d)
            name = d['theorem_name']
            if d.get('status') == 'Definition':
                code = d.get('definition')
                if not code:
                    print('   no code served for definition %s; skipped' % name); continue
                rel, text = os.path.join('Definitions', 'Def_%s.lean' % name), code.rstrip() + '\n'
            else:
                rel = os.path.join('Theorems', 'Thm_%s.lean' % name.replace('.', '_'))
                text = (d.get('preamble') or '').strip() + '\n\n' + (d.get('formal_statement') or '').strip() + '\n'
            p = os.path.join(root, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            if os.path.exists(p) and open(p, encoding='utf-8').read().rstrip() == text.rstrip():
                same += 1
            else:
                open(p, 'w', encoding='utf-8').write(text)
                written.append(rel)
                print('   wrote %-8s %s' % (d.get('status'), rel))
            mods.append(rel[:-5].replace(os.sep, '.'))
    print('%d files: %d written, %d already current' % (len(mods), len(written), same))
    if build and written:
        r = subprocess.run(['lake', 'build'] + sorted(set(mods)), cwd=ws, capture_output=True, text=True)
        errs = [l for l in (r.stdout + r.stderr).split('\n') if 'error' in l.lower()]
        print('build:', 'ok' if r.returncode == 0 else 'FAILED')
        for l in errs[:8]:
            print('   ', l[:200])
        sys.exit(r.returncode)


if __name__ == '__main__':
    main()
