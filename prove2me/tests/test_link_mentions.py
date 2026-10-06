"""link_mentions.py: link the published theorems a live mission's texts name (fake platform)."""
import pytest

import link_mentions as L

URL = 'https://prove2.me/theorems/'


class Fake:
    def __init__(self):
        self.thm = {'N.a': 'ida', 'N.b': 'idb', 'N.goal': 'idg'}
        self.nls = {'ida': 'Uses `N.b` and itself `N.a`, and `Garrido.BinaryTreeAut`.',
                    'idb': 'See `N.goal`.', 'idg': 'The goal; no mentions.'}
        self.desc = 'Targets `N.a`; already [`N.b`](%sidb); a definition `Defn.X`.' % URL
        self.ms = [{'id': 'm1', 'title': 'T1', 'theorem': {'id': 'ida'}, 'milestone_description': 'Quote. Route via `N.b`.'},
                   {'id': 'm2', 'title': 'T2', 'theorem': {'id': 'idb'}, 'milestone_description': 'No mentions.'}]
        self.patched = []

    def call(self, m, p, b=None):
        if m == 'GET' and p.startswith('/missions?'):
            return {'missions': [{'id': 'M', 'description': self.desc, 'main_theorem': {'id': 'idg'}}]}
        if m == 'GET' and p.startswith('/missions/M/milestones'):
            off = int(p.split('offset=')[1]) if 'offset=' in p else 0
            return {'milestones': [dict(x) for x in self.ms][off:]}
        if m == 'GET' and p.startswith('/theorems?theorem_name='):
            n = p.split('=', 1)[1]
            return {'theorems': [{'theorem_name': n, 'id': self.thm[n]}] if n in self.thm else []}
        if m == 'GET' and p.startswith('/theorems/'):
            tid = p.split('/')[2]
            name = next(k for k, v in self.thm.items() if v == tid)
            return {'id': tid, 'theorem_name': name, 'natural_language_statement': self.nls[tid]}
        if m == 'PATCH' and p.startswith('/theorems/'):
            self.patched.append(('thm', p.split('/')[2]))
            self.nls[p.split('/')[2]] = b['natural_language_statement']
            return {}
        if m == 'PATCH' and p.startswith('/milestones/'):
            self.patched.append(('ms', p.split('/')[2]))
            next(x for x in self.ms if x['id'] == p.split('/')[2])['milestone_description'] = b['milestone_description']
            return {}
        if m == 'PATCH' and p == '/missions/M':
            self.patched.append(('desc', 'M'))
            self.desc = b['description']
            return {}
        raise AssertionError((m, p))


def test_link_text_links_published_names_only():
    res = {'N.a': 'ida', 'N.b': 'idb'}.get
    out, n = L.link_text('`N.a`, `N.b`, `Defn.X`, [`N.b`](%sidb), `N.a`' % URL, res, own='N.a')
    assert out == '`N.a`, [`N.b`](%sidb), `Defn.X`, [`N.b`](%sidb), `N.a`' % (URL, URL)
    assert n == ['N.b']


def test_dry_run_patches_nothing(monkeypatch, capsys):
    f = Fake()
    L.run('M', go=False, call=f.call)
    out = capsys.readouterr().out
    assert f.patched == [] and 'description' in out and 'N.a' in out and 'dry run' in out


def test_go_patches_each_changed_text_once_and_reads_back(monkeypatch):
    f = Fake()
    L.run('M', go=True, call=f.call)
    assert sorted(f.patched) == [('desc', 'M'), ('ms', 'm1'), ('thm', 'ida'), ('thm', 'idb')]
    assert f.desc.startswith('Targets [`N.a`](%sida)' % URL) and '`Defn.X`' in f.desc
    assert f.nls['ida'] == 'Uses [`N.b`](%sidb) and itself `N.a`, and `Garrido.BinaryTreeAut`.' % URL
    assert f.nls['idb'] == 'See [`N.goal`](%sidg).' % URL
    f.patched.clear()
    L.run('M', go=True, call=f.call)            # a rerun changes nothing
    assert f.patched == []


def test_repo_files_get_the_same_links(tmp_path):
    f = Fake()
    (tmp_path / 'prose').mkdir()
    (tmp_path / 'prose' / 'a.md').write_text('---\ntitle: A\n---\n\nUses `N.b` and `N.a`.\n\n## Milestone\nRoute via `N.b`.\n')
    (tmp_path / 'description.md').write_text('Targets `N.a`.\n')
    (tmp_path / 'mission.py').write_text("NAMESPACE='N'\nTHEOREMS=[dict(name='a')]\n")
    L.run('M', go=False, call=f.call, repo=str(tmp_path))      # a dry run writes nothing
    assert '`N.b` and' in (tmp_path / 'prose' / 'a.md').read_text()
    L.run('M', go=True, call=f.call, repo=str(tmp_path))
    assert (tmp_path / 'prose' / 'a.md').read_text() == (
        '---\ntitle: A\n---\n\nUses [`N.b`](%sidb) and `N.a`.\n\n## Milestone\nRoute via [`N.b`](%sidb).\n' % (URL, URL))
    assert (tmp_path / 'description.md').read_text() == 'Targets [`N.a`](%sida).\n' % URL
