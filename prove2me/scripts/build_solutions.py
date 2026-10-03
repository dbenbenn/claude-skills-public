#!/usr/bin/env python3
"""Build a mission's solutions from its development's check files: one file per statement.

usage: build_solutions.py MISSION_DIR --check MOD [--check MOD ...] [--out DIR] [NAME ...]

  MOD      a check module under $P2M_WORKSPACE/Solutions, e.g. Monod/AlgCheck
  NAME     statements to build (default: every THEOREMS entry of MISSION_DIR/mission.py that
           some check file proves)
  --out    default MISSION_DIR/solutions; writes Sol_<name>.lean and Sol_<name>.log

A development proves each statement in a check file, as `theorem <name>` or `theorem chk_<name>`,
from the development's own modules, which carry primed copies of sibling statements because
nothing was published when they were written. For each statement this merges the Solutions modules
that check file imports and the check file itself (dependencies first, with merge.py), removes every
check block, appends this one renamed to `theorem solution` at the top level in a section that
re-creates its scope (its `open`s and `variable`s, its namespace opened; all from Lean's parse,
p2mlib.leanedit.scope_wrap), then runs rewire.py, which turns each copy of a published theorem
into a call to it plus an import, prunes and compiles.

Run `fetch_theorems.py` first, so every published name is in $P2M_WORKSPACE/Theorems; rewire only
sees names there. Afterwards run `edge_audit.py --local` on the output: rewire finds a copy of a sibling
by its statement, under any name, but a helper that re-derives only part of one is invisible to it.

Generalised 2026-09-30 from the per-mission builders of CFP §5, §6 and §7.
"""
import argparse, os, re, subprocess, sys, tempfile

SK = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SK)
sys.path.insert(0, os.path.dirname(SK))  # p2mlib
from merge import merge  # noqa: E402
from p2mlib import leanedit, leaninfo  # noqa: E402
from p2mlib.copies import imports_of  # noqa: E402
from p2mlib.leantext import header_end  # noqa: E402
from p2mlib.workspace import workspace as _workspace, drafts  # noqa: E402


def deps(sol, mod, seen):
    """Append Solutions module `mod` ('Monod/AlgG') after the Solutions modules it imports."""
    text = open(os.path.join(sol, mod + '.lean'), encoding='utf-8').read()
    for m in imports_of(text[:header_end(text)]):
        if m.startswith('Solutions.'):
            dep = m[len('Solutions.'):].replace('.', '/')
            if dep not in seen:
                deps(sol, dep, seen)
    if mod not in seen:
        seen.append(mod)
    return seen


def _last(n):
    return n.rsplit('.', 1)[-1]


def check_block(info, start, name):
    """The command of the check module (the region from byte `start`) that proves `name`:
    `chk_<name>` if there is one, else `<name>` -- full names compared by their last component,
    so `isMarginal_EBad'` is never taken for `isMarginal_EBad`."""
    region = [c for c in info.commands if c.start.byte >= start]
    for want in ('chk_' + name, name):
        for c in region:
            if any(_last(n) == want for n in c.names):
                return c
    return None


def solution_text(info, c, name):
    """Check command c as `theorem solution`, at the top level, in a section that re-creates its
    scope (leanedit.scope_wrap): the `open`s and `variable`s in force, and its namespace opened.
    Its own `open X in` prefix comes with it as part of the command; one above another block does
    not (copying `open` lines by regex gave `open X in in`, and swallowed the next block's prefix)."""
    k = next(j for j, n in enumerate(c.names) if _last(n) in ('chk_' + name, name))
    a, b = c.ids[k]
    t = info.text_bytes
    head = t[c.start.byte:a.byte].decode('utf-8')
    head = re.sub(r'^\s*/--.*?-/\s*', '', head, flags=re.S)       # no docstring on `solution`
    head = re.sub(r'\b(?:private|protected)\s+', '', head)         # nor a private one
    head = re.sub(r'\blemma(\s+)$', r'theorem\1', head)
    pre, post = leanedit.scope_wrap(info, c.index, top_level=True)
    return pre + head + 'solution' + t[b.byte:c.end.byte].decode('utf-8') + '\n' + post


# Inside `namespace A.B` a name defined in both A and A.B means the inner one; at the top level,
# under `open A` and `open A.B`, it is ambiguous (CFW Corollary 13, 2026-10-03). Lean's own error,
# printed with full names, lists the candidates; the one Lean took inside the namespace is the
# candidate in the longest namespace enclosing the check block's.
AMBIGUOUS = re.compile(r'^[^\n]*?:(\d+):(\d+): error: Ambiguous term\n  (\S+)\n'
                       r'Possible interpretations:\n((?:(?:  [^\n]*)?\n)+)', re.M)


def parse_ambiguities(out):
    """[(line, col, term, [candidate full names])] from Lean's output under -Dpp.fullNames=true."""
    res = []
    for m in AMBIGUOUS.finditer(out):
        cands = [re.match(r'  [(@]*([^\s()]+)', l).group(1) for l in m.group(4).split('\n')
                 if re.match(r'  [^\s]', l)]                  # a wrapped type line is indented more
        res.append((int(m.group(1)), int(m.group(2)), m.group(3), cands))
    return res


def qualify_ambiguous(text, amb, ns):
    """Write each ambiguous term (1-based line, codepoint column) as the candidate in the longest
    namespace enclosing `ns`; leave it when none encloses (then it was ambiguous inside too).
    Returns (text, [(term, replacement)])."""
    lines = text.split('\n')
    done, seen = [], set()
    for line, col, term, cands in sorted(amb, key=lambda a: (a[0], a[1]), reverse=True):
        if (line, col) in seen:
            continue
        seen.add((line, col))
        best = None
        for full in cands:
            part = '' if full == term else full[:-len(term) - 1] if full.endswith('.' + term) else None
            if part is None or (part and not (ns == part or ns.startswith(part + '.'))):
                continue
            if best is None or len(part) > len(best[0]):
                best = (part, full)
        l = lines[line - 1] if line <= len(lines) else ''
        end = col + len(term)
        if best is None or l[col:end] != term or re.match(r"[\w']", l[end:end + 1]) \
                or re.match(r"[\w'.]", l[col - 1:col] if col else ''):
            continue
        repl = best[1] if best[0] else '_root_.' + term
        lines[line - 1] = l[:col] + repl + l[end:]
        done.append((term, repl))
    return '\n'.join(lines), done[::-1]


def repair_ambiguity(path, ns, rounds=3):
    """Elaborate `path` and qualify its ambiguous terms as `namespace ns` resolved them, until Lean
    reports no more. Returns [(term, replacement)]."""
    done = []
    for _ in range(rounds):
        p = subprocess.run(['lake', 'env', 'lean', '-Dpp.fullNames=true', os.path.abspath(path)],
                           capture_output=True, text=True, cwd=_workspace())
        text = open(path, encoding='utf-8').read()
        new, d = qualify_ambiguous(text, parse_ambiguities(p.stdout + p.stderr), ns)
        if not d:
            break
        open(path, 'w', encoding='utf-8').write(new)
        done += d
    return done


def assemble(sol, checks, name, scratch):
    """(status, merged text ending in `theorem solution`, namespace of the check block)."""
    for mod in checks:
        text = open(os.path.join(sol, mod + '.lean'), encoding='utf-8').read()
        if not re.search(r"(?<![\w'.])(?:chk_)?%s(?![\w'])" % re.escape(name), text):
            continue
        seen = []
        for m in imports_of(text[:header_end(text)]):
            if m.startswith('Solutions.'):
                deps(sol, m[len('Solutions.'):].replace('.', '/'), seen)
        # the check file itself is merged whole: its own helpers (the Moore weak-reading
        # counterexamples kept `wAct`, `mu`, ... there, and a solution once named undefined helpers)
        files = [os.path.join(sol, s + '.lean') for s in seen] + [os.path.join(sol, mod + '.lean')]
        try:
            merged, starts = merge(files, scratch=scratch)
        except SystemExit as e:
            return 'MERGE-FAIL: %s' % e, '', ''
        fd, tmp = tempfile.mkstemp(suffix='.lean', prefix='.build_', dir=scratch)
        with os.fdopen(fd, 'w', encoding='utf-8') as f:
            f.write(merged)
        try:
            info = leaninfo.run(tmp, parse_only=True, use_cache=False)
        finally:
            os.remove(tmp)
        c = check_block(info, starts[-1], name)
        if c is None:
            continue
        # check blocks are found by name and all stripped, so a `chk_` name must mean one block: an
        # `alias chk_x := Dev.chk_x` reports no names, survived the stripping while its target did
        # not, and every solution failed with "Unknown constant" (CFW 2026-10-03)
        region = info.text_bytes[starts[-1]:].decode('utf-8', 'replace')
        chk = [_last(n) for x in info.commands if x.start.byte >= starts[-1] for n in x.names
               if _last(n).startswith('chk_')]
        bad = sorted({n for n in chk if chk.count(n) > 1} |
                     set(re.findall(r"(?m)^\s*(?:(?:private|protected)\s+)?alias\s+(?:\S+\.)?(chk_[\w']+)", region)))
        if bad:
            return ('CHECK-AMBIGUOUS: %s is an alias or names more than one block; rename the '
                    'development\'s own copy so only the final check block starts with chk_' % ', '.join(bad)), '', ''
        # every check block goes: each proves some statement, and only this one is the solution;
        # so does every diagnostic command (`#print axioms LodhaMoore.chk_…` named the renamed
        # block and the solution stopped compiling, Lodha-Moore 2026-10-02)
        from p2mlib.prune import DIAGNOSTIC
        drop = [x.index for x in info.commands if x.short_kind in DIAGNOSTIC or (x.start.byte >= starts[-1]
                and any(_last(n).startswith('chk_') or _last(n) == name for n in x.names))]
        body = leanedit.remove_commands(info, drop).rstrip('\n') + '\n'
        return 'OK', body + '\n' + solution_text(info, c, name), c.namespace
    return 'NO-CHECK', '', ''


def build(mdir, checks, name, out):
    ws = _workspace()
    sol = os.path.join(ws, 'Solutions')
    st, body, ns = assemble(sol, checks, name, out)
    if st != 'OK':
        for kind in ('MERGE-FAIL', 'CHECK-AMBIGUOUS'):
            if st.startswith(kind):
                open(os.path.join(out, 'Sol_%s.log' % name), 'w').write(st)
                st = kind
        return name, st, []
    block = body[body.rindex('theorem solution'):]
    # A check block that names a published sibling statement directly (`Gpp_eq_G_top_and_Hpp_eq_H_top.2`)
    # needs its import, and the import is what draws the graph edge (Monod 2026-09-30).
    thm = os.path.join(ws, 'Theorems')
    for tok in sorted(set(re.findall(r"(?<![\w'])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)", block))):
        short = tok.split('.')[-1] if not ns or not tok.startswith(ns + '.') else tok[len(ns) + 1:]
        short = short.split('.')[0] if '.' in short else short
        if short == name:
            continue
        for cand in ([ns.split('.')[0] + '_' + short] if ns else []) + [tok.replace('.', '_')]:
            if os.path.exists(os.path.join(thm, 'Thm_%s.lean' % cand)) and 'Theorems.Thm_%s' % cand not in drafts(ws):
                imp = 'import Theorems.Thm_%s' % cand
                if imp not in body:
                    body = imp + '\n' + body
                break
    merged = os.path.join(out, '.merged_%s.lean' % name)
    open(merged, 'w', encoding='utf-8').write(body)
    dst = os.path.join(out, 'Sol_%s.lean' % name)

    def rewire():
        return subprocess.run([sys.executable, os.path.join(SK, 'rewire.py'), merged, '--target', name,
                               '-o', dst], capture_output=True, text=True, cwd=ws)
    p = rewire()
    log = p.stdout + p.stderr
    if p.returncode and 'does not elaborate' in log and os.path.exists(dst):
        fixed = repair_ambiguity(dst, ns)
        if fixed:
            os.replace(dst, merged)
            p = rewire()
            log = ('qualified ambiguous names (as namespace %s resolved them): %s\n' % (
                ns, ', '.join('%s -> %s' % f for f in fixed)) + p.stdout + p.stderr)
    open(os.path.join(out, 'Sol_%s.log' % name), 'w').write(log)
    if os.path.exists(merged):
        os.remove(merged)
    imps = re.findall(r'^import Theorems\.(\S+)', open(dst).read(), re.M) if os.path.exists(dst) else []
    # rewire exits 1 when it left a copy it could not prove from the published theorem (a genuinely
    # different statement sharing a name); the file itself still compiles: report OK*, read the log
    st = 'OK' if p.returncode == 0 else \
        'OK*' if 'compiles clean' in p.stdout + p.stderr and 'could not prove' in p.stdout + p.stderr \
        else 'RC%d' % p.returncode
    # a proof may never import its own target (the verifier answers FAILED); this happens when a
    # development lemma was re-derived from the published statement and the check block still uses it
    if any(i.endswith('_' + name) and i.startswith((ns.split('.')[0] if ns else '') + '_') for i in imps):
        st = 'SELF-IMPORT'
    return name, st, imps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mission_dir')
    # repeatable, not nargs='+': a list option swallows the positional NAMEs after it
    ap.add_argument('--check', dest='checks', action='append', required=True)
    ap.add_argument('--out')
    ap.add_argument('names', nargs='*')
    a = ap.parse_intermixed_args()
    mdir = os.path.abspath(a.mission_dir)
    out = a.out or os.path.join(mdir, 'solutions')
    os.makedirs(out, exist_ok=True)
    names = a.names
    if not names:
        sys.path.insert(0, mdir)
        from p2mlib.mission import load
        mission = load(mdir)
        names = [T['name'] for T in mission.THEOREMS]
    for n in names:
        name, st, imps = build(mdir, a.checks, n, out)
        print('%-9s %-52s imports: %s' % (st, name, ', '.join(imps) or '(none)'), flush=True)


if __name__ == '__main__':
    main()
