"""The module-route carve as one resumable pipeline (scripts/carve_pipeline.py).

Replaces the per-job bash drivers (plain_carve.sh, plain_pipeline*.sh, ext_publish.sh ...): one
tracked implementation, every step idempotent and logged, state in DIR/pipeline_state.json, every
sub-tool called from one skill snapshot (p2mlib.snapshot) so editing or pushing the live skill
cannot reach a running carve."""
import fcntl
import json
import os
import re
import subprocess
import sys
import time

from . import runlock, snapshot, workspace as wslib

STEPS = ['fetch', 'filter_patches', 'port', 'build', 'wsbuild', 'config', 'graph', 'extdefs', 'plan', 'gen',
         'order', 'measure', 'publish_prep', 'prose', 'check_text', 'dryrun', 'publish']
DEFAULT_LEAN_CAP = '~/claude/claude-private/tools/lean-cap'
PARAM_KEYS = ['folder', 'root_module', 'targets', 'bundle_prefix', 'defs', 'forced', 'patches', 'compat_imports',
              'stdsimplex', 'budget', 'lean_src', 'commit', 'fetch', 'config_set', 'measure_flags', 'meta', 'tags']


class StepFailed(Exception):
    pass


def module_root_name(rootmod, prefixes, files):
    """The ported file (stem) holding OpenAI module ROOTMOD: oai_port_modules.py names a module
    after its path below the longest matching prefix, '.' -> '_', possibly with a further
    directory prefix; an exact stem wins over a suffix match."""
    best = [p for p in prefixes if rootmod.startswith(p + '.')]
    if best:
        root = rootmod[len(max(best, key=len)) + 1:].replace('.', '_')
    else:
        root = rootmod.rsplit('.', 1)[-1]
    stems = [f[:-5] for f in sorted(files) if f.endswith('.lean')]
    if root in stems:
        return root
    for s in stems:
        if s.endswith('_' + root):
            return s
    raise StepFailed('no ported module for %s (looked for %s.lean or *_%s.lean)' % (rootmod, root, root))


def derive_defs(ws, targets):
    defs = []
    for t in targets:
        _, rel = wslib.statement_module(t)
        p = os.path.join(ws, rel)
        if not os.path.exists(p):
            raise StepFailed('the statement of %s is not in the workspace (%s); fetch_theorems.py first' % (t, rel))
        for line in open(p, encoding='utf-8'):
            m = re.match(r'import\s+(Definitions\.\S+)', line)
            if m and m.group(1) not in defs:
                defs.append(m.group(1))
    return defs


def openai_prefixes(lean_src):
    oai = os.path.join(lean_src, 'OAI')
    return ['OAI.' + d for d in sorted(os.listdir(oai)) if os.path.isdir(os.path.join(oai, d))]


def _now():
    return time.strftime('%Y-%m-%dT%H:%M:%S')


class Pipeline:
    def __init__(self, d, params, snap_root, ws=None):
        self.d = os.path.abspath(d)
        self.p = params
        self.snap = snap_root
        self.ws = ws or wslib.workspace()
        self.scripts = os.path.join(snap_root, 'prove2me', 'scripts')
        self.state_path = os.path.join(self.d, 'pipeline_state.json')
        self.state = json.load(open(self.state_path)) if os.path.exists(self.state_path) else {'steps': {}}
        self.lean_src = os.path.abspath(os.path.expanduser(params.get('lean_src') or os.path.join(self.d, 'src', 'lean')))
        self.meta = os.path.abspath(os.path.expanduser(params.get('meta') or os.path.join(self.d, 'oai_meta.json')))

    # -- state ------------------------------------------------------------------------------
    def save(self):
        tmp = self.state_path + '.tmp'
        json.dump(self.state, open(tmp, 'w'), indent=1)
        os.replace(tmp, self.state_path)

    def invalidate(self, frm):
        i = STEPS.index(frm)
        for s in STEPS[i:]:
            self.state['steps'].pop(s, None)

    # -- running ----------------------------------------------------------------------------
    def env(self):
        e = dict(os.environ)
        cap = os.environ.get('P2M_LEAN_CAP', DEFAULT_LEAN_CAP)
        cap = os.path.expanduser(cap) if cap else ''
        if cap and os.path.isdir(cap):
            e['PATH'] = cap + os.pathsep + e.get('PATH', '')
        e['P2M_SKILL_ROOT'] = self.snap
        e['P2M_WORKSPACE'] = self.ws
        return e

    def tool(self, name, *args):
        return [sys.executable, os.path.join(self.scripts, name + '.py'), *map(str, args)]

    def run_cmds(self, step, cmds, cwd=None):
        log = os.path.join(self.d, 'logs', step + '.log')
        os.makedirs(os.path.dirname(log), exist_ok=True)
        with open(log, 'a') as f:
            f.write('==== %s %s (skill %s)\n' % (_now(), step, os.path.basename(self.snap)))
            for c in cmds:
                f.write('$ %s\n' % ' '.join(c))
                f.flush()
                r = subprocess.run(c, cwd=cwd or self.d, env=self.env(), stdout=f, stderr=subprocess.STDOUT)
                if r.returncode:
                    f.write('(exit %d)\n' % r.returncode)
                    f.flush()
                    tail = ''.join(open(log, errors='replace').readlines()[-15:])
                    raise StepFailed("step '%s' failed (exit %d); log %s\n%s" % (step, r.returncode, log, tail))

    # -- steps ------------------------------------------------------------------------------
    def prefixes(self):
        return openai_prefixes(self.lean_src)

    def defs(self):
        return self.p.get('defs') or derive_defs(self.ws, self.p['targets'])

    def root(self):
        files = os.listdir(os.path.join(self.ws, 'Solutions', self.p['folder']))
        return module_root_name(self.p['root_module'], self.prefixes(), files)

    def port_patches(self):
        return os.path.join(self.d, 'port_patches.json')

    def compat_args(self):
        a = []
        if self.p.get('compat_imports'):
            a += ['--compat-imports', self.p['compat_imports']]
        if self.p.get('stdsimplex'):
            a += ['--stdsimplex', self.p['stdsimplex']]
        return a

    def step_fetch(self):
        if not self.p.get('fetch'):
            return 'skipped'
        a = [os.path.join(self.d, 'src'), self.p['root_module']]
        if self.p.get('commit'):
            a += ['--commit', self.p['commit']]
        self.run_cmds('fetch', [self.tool('oai_fetch', *a)])

    def step_filter_patches(self):
        if not self.p.get('patches'):
            return 'skipped'
        self.run_cmds('filter_patches', [self.tool('carve_prep', 'filter-patches', os.path.expanduser(self.p['patches']),
                                                   self.lean_src, self.port_patches(), *self.prefixes(), *self.compat_args())])

    def step_port(self):
        a = [self.lean_src, self.p['folder'], *self.prefixes()]
        if self.p.get('patches'):
            a += ['--patches', self.port_patches()]
        self.run_cmds('port', [self.tool('oai_port_modules', *a, *self.compat_args())])

    def step_build(self):
        self.run_cmds('build', [self.tool('oai_build_modules', self.p['folder'], self.root(), '--log', 'build.log',
                                          '--elab-log', 'build_elab.log')])

    def step_wsbuild(self):
        mods = self.defs() + [wslib.statement_module(t)[0] for t in self.p['targets']]
        self.run_cmds('wsbuild', [['lake', 'build', *mods]], cwd=self.ws)

    def step_config(self):
        a = ['config', self.d, self.p['folder'], self.root(), self.p['targets'][0]]
        for d in self.defs():
            a += ['--def', d]
        a += ['--bundle-prefix', self.p['bundle_prefix'], '--budget', '%g' % self.p.get('budget', 55)]
        for f in self.p.get('forced') or []:
            a += ['--forced', f]
        self.run_cmds('config', [self.tool('carve_prep', *a)])
        path = os.path.join(self.d, 'config.json')
        cfg = json.load(open(path))
        cfg['targets'] = list(self.p['targets'])
        cfg['external'] = sorted(set(cfg.get('external', [])) | set(self.p['targets']))
        if self.p.get('compat_imports'):
            cfg['collapse_mathlib'] = False
        cfg.update(self.p.get('config_set') or {})
        json.dump(cfg, open(path, 'w'), indent=1)

    def step_graph(self):
        self.run_cmds('graph', [self.tool('carve', 'graph', 'config.json')])

    def step_extdefs(self):
        a = ['ext-defs', 'config.json']
        for d in self.defs():
            a += ['--def', d]
        self.run_cmds('extdefs', [self.tool('carve_prep', *a)])

    def step_plan(self):
        self.run_cmds('plan', [self.tool('carve', 'plan', 'config.json')])

    def step_gen(self):
        self.run_cmds('gen', [self.tool('carve', 'gen', 'config.json')])

    def step_order(self):
        self.run_cmds('order', [self.tool('carve', 'order', 'config.json')])

    def step_measure(self):
        self.run_cmds('measure', [self.tool('carve_measure', 'config.json', *(self.p.get('measure_flags') or []))])

    def source_line(self):
        m = json.load(open(self.meta))
        return ('OpenAI, %s, OpenAI Math Release, %s, https://github.com/openai/math (result family %s), '
                'Apache License 2.0' % (m['title'], m['date'], m['family']))

    def step_publish_prep(self):
        self.run_cmds('publish_prep', [self.tool('carve_prep', 'publish-prep', self.d, self.source_line(),
                                                 self.p.get('tags') or 'openai-math')])

    def step_prose(self):
        self.run_cmds('prose', [self.tool('carve_prep', 'prose-template', self.d, '--meta', self.meta)])
        log = os.path.join(self.d, 'logs', 'prose.log')
        need = [l for l in open(log).read().splitlines() if 'needs written prose' in l]
        if need:
            print('NOTE: written prose still needed (goal and forced items):', *need, sep='\n  ', file=sys.stderr)

    def step_check_text(self):
        self.run_cmds('check_text', [self.tool('carve_prep', 'check-text', os.path.join(self.d, 'publish'))])

    def step_dryrun(self):
        self.run_cmds('dryrun', [self.tool('split_run', 'publish/run.json')])

    def step_publish(self):
        if not self.p.get('go'):
            return 'skipped'
        self.run_cmds('publish', [self.tool('split_run', 'publish/run.json', '--go')])

    # -- driver -----------------------------------------------------------------------------
    def run(self, stop_after=None, only_redo=()):
        for s in STEPS:
            rec = self.state['steps'].get(s)
            if rec and rec['status'] in ('done', 'skipped') and s not in only_redo:
                if s == stop_after:
                    break
                continue
            if s == 'publish' and not self.p.get('go'):
                break                                              # publishing is opt-in, never recorded
            print('== %s %s' % (s, _now()), flush=True)
            rec = self.state['steps'][s] = {'status': 'running', 'started': _now()}
            self.save()
            try:
                res = getattr(self, 'step_' + s)()
            except StepFailed as e:
                rec.update(status='failed', finished=_now(), message=str(e).splitlines()[0])
                self.save()
                raise
            rec.update(status=res or 'done', finished=_now())
            self.save()
            if s == stop_after:
                break
        return self.state


def lock(d):
    runlock.hold(runlock.dir_key('pipeline', d), 'carve_pipeline.py on %s (pid %d)' % (d, os.getpid()))
