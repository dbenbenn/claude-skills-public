"""workspace_audit.py: which untracked workspace files have no copy anywhere we keep work.

Offline: a throwaway workspace repo and a throwaway mission repo with a local bare remote (the
`backed` predicate accepts it, as it would accept github.com in real use)."""
import json
import os
import subprocess
import time

import pytest

import workspace_audit as WA

OLD = time.time() - 30 * 86400


def sh(cwd, *args):
    subprocess.run(args, cwd=cwd, check=True, capture_output=True)


def write(path, text, mtime=OLD):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, 'w').write(text)
    os.utime(path, (mtime, mtime))


PROOF = '''import Mathlib

theorem foo_le_bar (n : Nat) : n ≤ n + 1 := by
  exact Nat.le_succ n

theorem baz_comm (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b
'''


@pytest.fixture
def world(tmp_path):
    remote = tmp_path / 'remote.git'
    sh(tmp_path, 'git', 'init', '-q', '--bare', str(remote))
    repo = tmp_path / 'mission'
    sh(tmp_path, 'git', 'clone', '-q', str(remote), str(repo))
    for k, v in (('user.name', 't'), ('user.email', 't@t')):
        sh(repo, 'git', 'config', k, v)
    write(str(repo / 'proofs' / 'Foo.lean'), PROOF)
    sh(repo, 'git', 'add', '.')
    sh(repo, 'git', 'commit', '-q', '-m', 'pushed')
    sh(repo, 'git', 'push', '-q', 'origin', 'HEAD:main')
    sh(repo, 'git', 'fetch', '-q')
    # committed but never pushed: must not count as backed
    write(str(repo / 'proofs' / 'Local.lean'), 'theorem only_local : True := by\n  trivial -- not pushed\n')
    sh(repo, 'git', 'add', '.')
    sh(repo, 'git', 'commit', '-q', '-m', 'local only')

    ws = tmp_path / 'ws'
    sh(tmp_path, 'git', 'init', '-q', str(ws))
    for d in ('Definitions', 'Theorems', 'Solutions'):
        write(str(ws / d / '.gitkeep'), '')
    sh(ws, 'git', 'add', '.')
    sh(ws, 'git', '-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-q', '-m', 'skeleton')
    return dict(ws=str(ws), repo=str(repo))


def audit(world, **kw):
    idx = WA.Index.build([world['repo']], backed=lambda url: True, cache_dir=None)
    return {r.path: r for r in WA.audit(world['ws'], idx, **kw)}


def test_exact_copy_is_backed(world):
    write(os.path.join(world['ws'], 'Solutions', 'Sol_foo.lean'), PROOF)
    assert audit(world)['Solutions/Sol_foo.lean'].kind == 'backed'


def test_unpushed_commit_is_not_backed(world):
    text = open(os.path.join(world['repo'], 'proofs', 'Local.lean')).read()
    write(os.path.join(world['ws'], 'Solutions', 'Local.lean'), text)
    assert audit(world)['Solutions/Local.lean'].kind == 'unbacked'


def test_near_copy_by_lines(world):
    edited = PROOF.replace('import Mathlib\n', 'import Mathlib\nimport Definitions.Def_X\n') + '\n\n'
    write(os.path.join(world['ws'], 'Solutions', 'Sol_foo2.lean'), edited)
    r = audit(world)['Solutions/Sol_foo2.lean']
    assert r.kind == 'near-copy' and r.coverage == 1.0


def test_new_work_is_unbacked(world):
    write(os.path.join(world['ws'], 'Solutions', 'New.lean'),
          'theorem brand_new_result (n : Nat) : 0 ≤ n := by\n  exact Nat.zero_le n\n')
    r = audit(world)['Solutions/New.lean']
    assert r.kind == 'unbacked' and r.coverage == 0.0


def test_recent_files_are_active_not_judged(world):
    write(os.path.join(world['ws'], 'Solutions', 'Wip.lean'), 'theorem wip_thing : True := by\n  trivial\n',
          mtime=time.time())
    assert audit(world, min_age_days=2)['Solutions/Wip.lean'].kind == 'active'


def test_mirror_and_draft_stub(world):
    write(os.path.join(world['ws'], 'Theorems', 'Thm_X_pub.lean'), 'theorem pub_thing_here : True := sorry\n')
    write(os.path.join(world['ws'], 'Theorems', 'Thm_X_draft.lean'), 'theorem draft_thing_here : True := sorry\n')
    write(os.path.join(world['ws'], 'Theorems', '.drafts.json'),
          json.dumps({'Theorems.Thm_X_draft': '/some/mission'}))
    rs = audit(world)
    assert rs['Theorems/Thm_X_pub.lean'].kind == 'mirror'
    assert rs['Theorems/Thm_X_draft.lean'].kind == 'draft-stub'
    assert 'Theorems/.drafts.json' not in rs          # tooling state, not work


def test_a_carve_owner_file_is_tooling_state(world):
    write(os.path.join(world['ws'], 'Solutions', 'OAIQ1_X', '.carve_owner.json'), '{"carve": "/x"}')
    assert 'Solutions/OAIQ1_X/.carve_owner.json' not in audit(world)


def test_tracked_files_are_ignored(world):
    assert 'Solutions/.gitkeep' not in audit(world)


def test_non_lean_files_are_reported_by_hash_only(world):
    write(os.path.join(world['ws'], 'Solutions', 'notes.md'), 'some notes that exist nowhere else\n')
    assert audit(world)['Solutions/notes.md'].kind == 'unbacked'


def test_backed_predicate_excludes_non_github_remotes(world):
    write(os.path.join(world['ws'], 'Solutions', 'Sol_foo.lean'), PROOF)
    idx = WA.Index.build([world['repo']], backed=lambda url: 'github.com' in url, cache_dir=None)
    rs = {r.path: r for r in WA.audit(world['ws'], idx)}
    assert rs['Solutions/Sol_foo.lean'].kind == 'unbacked'


def test_index_cache_round_trip(world, tmp_path):
    cache = str(tmp_path / 'cache')
    a = WA.Index.build([world['repo']], backed=lambda url: True, cache_dir=cache)
    b = WA.Index.build([world['repo']], backed=lambda url: True, cache_dir=cache)
    assert a.blobs == b.blobs and a.lines == b.lines and os.listdir(cache)


def test_quiet_groups_unbacked_by_two_levels(world, monkeypatch, capsys):
    write(os.path.join(world['ws'], 'Solutions', 'Port', 'Deep', 'A', 'x.lean'), 'theorem deep_new_thing : True := trivial\n')
    write(os.path.join(world['ws'], 'Solutions', 'Port', 'Other', 'y.lean'), 'theorem other_new_thing : True := trivial\n')
    write(os.path.join(world['ws'], 'Solutions', 'top.lean'), 'theorem top_new_thing_here : True := trivial\n')
    monkeypatch.setattr(WA, 'workspace', lambda: world['ws'])
    monkeypatch.setattr(WA, 'find_repos', lambda: [world['repo']])
    monkeypatch.setattr(WA, 'github', lambda url: True)
    monkeypatch.setattr(WA, 'CACHE', None)
    WA.main(['--quiet'])
    out = capsys.readouterr().out
    assert 'Solutions/Port 2' in out and 'Solutions 1' in out


def test_summary_line_counts_kinds(world):
    write(os.path.join(world['ws'], 'Solutions', 'Sol_foo.lean'), PROOF)
    write(os.path.join(world['ws'], 'Solutions', 'New.lean'), 'theorem brand_new_result : True := by\n  trivial\n')
    s = WA.summary(list(audit(world).values()))
    assert 'backed 1' in s and 'unbacked 1' in s


def test_partial_clones_are_skipped(world):
    # 2026-10-28: the blobless openai/math clone under ~/claude made `rev-list --objects` fetch every
    # missing blob from GitHub, one by one: sync_workspace hung with no output
    WA.git(world['repo'], 'config', 'remote.origin.promisor', 'true')
    idx = WA.Index.build([world['repo']], backed=lambda url: True, cache_dir=None)
    assert idx.repos == [] and idx.blobs == set()


# --- copies: does a Solutions/<FOLDER> file have a byte-identical copy in some mission repo's proofs/?
# q157 (2026-11-03): a sorry-free Solutions/JM31/PartC.lean sat untracked in the workspace, and the
# RESUME called it lost after checking only jm-mission/proofs/.

PART_C = 'theorem part_c_main_result (n : Nat) : n ≤ n * 1 := by\n  simp\n'


@pytest.fixture
def missions(tmp_path):
    """root/ holding two mission repos, a non-repo folder, and the workspace (itself a repo)."""
    root = tmp_path / 'claude'
    for r in ('jm-mission', 'p2m-standalone', 'prove2me_workspace'):
        os.makedirs(str(root / r / '.git'))
    ws = str(root / 'prove2me_workspace')
    jm = str(root / 'jm-mission')
    write(os.path.join(jm, 'proofs', 's31', 'PartA.lean'), PROOF)
    write(os.path.join(jm, 'proofs', 's31', 'PartB.lean'), PART_C.replace('part_c', 'part_b'))
    write(os.path.join(ws, 'Solutions', 'JM31', 'PartA.lean'), PROOF)
    write(os.path.join(ws, 'Solutions', 'JM31', 'PartB.lean'), PART_C.replace('part_c', 'part_b'))
    write(os.path.join(ws, 'Solutions', 'JM31', 'PartC.lean'), PART_C)
    return dict(root=str(root), ws=ws, jm=jm, sa=str(root / 'p2m-standalone'))


def copies(m, folders=None, include_oai=False):
    repos = WA.mission_repos(m['root'], exclude=(m['ws'],))
    return {f.path: f for f in WA.folder_copies(m['ws'], repos, folders=folders, include_oai=include_oai)}


def test_mission_repos_are_the_repos_directly_under_root(missions):
    os.makedirs(os.path.join(missions['root'], 'notes'))                        # not a repo
    os.makedirs(os.path.join(missions['root'], 'jm-mission', 'sub', '.git'))    # nested: not direct
    names = [os.path.basename(r) for r in WA.mission_repos(missions['root'], exclude=(missions['ws'],))]
    assert names == ['jm-mission', 'p2m-standalone']


def test_workspace_only_part_is_reported(missions):
    fs = copies(missions, folders=['JM31'])
    assert fs['Solutions/JM31/PartC.lean'].copy is None
    assert fs['Solutions/JM31/PartA.lean'].copy == os.path.join(missions['jm'], 'proofs', 's31', 'PartA.lean')
    assert fs['Solutions/JM31/PartB.lean'].copy is not None


def test_copy_may_have_another_name_and_sit_deep_in_a_standalone_folder(missions):
    write(os.path.join(missions['sa'], 'openai-ports', 'q157', 'proofs', 'x', 'C_final.lean'), PART_C)
    assert copies(missions, folders=['JM31'])['Solutions/JM31/PartC.lean'].copy.endswith('C_final.lean')


def test_one_changed_byte_is_not_a_copy(missions):
    write(os.path.join(missions['jm'], 'proofs', 's31', 'PartC.lean'), PART_C + '\n')
    assert copies(missions, folders=['JM31'])['Solutions/JM31/PartC.lean'].copy is None


def test_only_proofs_trees_count(missions):
    write(os.path.join(missions['jm'], 'statements', 'PartC.lean'), PART_C)
    write(os.path.join(missions['jm'], '.lake', 'proofs', 'PartC.lean'), PART_C)
    write(os.path.join(missions['jm'], 'proofs', '.lake', 'build', 'PartC.lean'), PART_C)
    assert copies(missions, folders=['JM31'])['Solutions/JM31/PartC.lean'].copy is None


def test_the_workspace_is_not_its_own_backup(missions):
    write(os.path.join(missions['ws'], 'proofs', 'PartC.lean'), PART_C)
    assert copies(missions, folders=['JM31'])['Solutions/JM31/PartC.lean'].copy is None


def test_every_folder_but_oai_ports_by_default(missions):
    write(os.path.join(missions['ws'], 'Solutions', 'OAIQ1_X', 'Main.lean'), 'theorem oai_port_only : True := trivial\n')
    write(os.path.join(missions['ws'], 'Solutions', 'Viterbo', 'deep', 'P.lean'), 'theorem vit_only_here : True := trivial\n')
    write(os.path.join(missions['ws'], 'Solutions', 'Sol_top.lean'), 'theorem top_level_sol : True := trivial\n')
    write(os.path.join(missions['ws'], 'Solutions', 'JM31', '.lake', 'build', 'x.lean'), 'junk\n')
    write(os.path.join(missions['ws'], 'Solutions', 'JM31', 'notes.md'), 'not lean\n')
    fs = copies(missions)
    assert 'Solutions/Viterbo/deep/P.lean' in fs and 'Solutions/JM31/PartC.lean' in fs
    assert not any(p.startswith('Solutions/OAI') for p in fs)
    assert 'Solutions/Sol_top.lean' not in fs                  # not in a folder
    assert not any('.lake' in p or p.endswith('.md') for p in fs)
    assert 'Solutions/OAIQ1_X/Main.lean' in copies(missions, include_oai=True)


def test_carve_owned_folders_count_as_oai_ports(missions):
    # Solutions/Q146_CD (2,921 files) is a carve port without the OAI prefix; its source is the carve dir
    write(os.path.join(missions['ws'], 'Solutions', 'Q146_CD', 'Main.lean'), 'theorem carve_port_only : True := trivial\n')
    write(os.path.join(missions['ws'], 'Solutions', 'Q146_CD', WA.CARVE_OWNER), '{"carve": "/x"}')
    assert 'Solutions/Q146_CD/Main.lean' not in copies(missions)
    assert 'Solutions/Q146_CD/Main.lean' in copies(missions, include_oai=True)
    assert 'Solutions/Q146_CD/Main.lean' in copies(missions, folders=['Q146_CD'])


def test_a_named_oai_folder_is_reported(missions):
    write(os.path.join(missions['ws'], 'Solutions', 'OAIQ1_X', 'Main.lean'), 'theorem oai_port_only : True := trivial\n')
    assert copies(missions, folders=['OAIQ1_X'])['Solutions/OAIQ1_X/Main.lean'].copy is None


def test_folder_names_are_normalised_and_checked(missions):
    assert 'Solutions/JM31/PartC.lean' in copies(missions, folders=['Solutions/JM31/'])
    with pytest.raises(SystemExit):
        copies(missions, folders=['NoSuchFolder'])


@pytest.fixture
def main_env(missions, monkeypatch):
    monkeypatch.setattr(WA, 'workspace', lambda: missions['ws'])
    monkeypatch.setattr(WA, 'MISSION_ROOT', missions['root'])
    return missions


def test_folder_mode_lists_the_workspace_only_part_and_skips_the_git_index(main_env, monkeypatch, capsys):
    def no_index(*a, **k):
        raise AssertionError('--folder must not build the git index')
    monkeypatch.setattr(WA.Index, 'build', no_index)
    WA.main(['--folder', 'JM31'])
    out = capsys.readouterr().out
    assert 'Solutions/JM31: 3 .lean files, 1 with no copy' in out
    nocopy = [l.strip() for l in out.splitlines() if l.strip().startswith('no-copy')]
    assert len(nocopy) == 1 and nocopy[0].endswith('Solutions/JM31/PartC.lean')
    assert 'proofs/s31/PartA.lean' in out                       # where the copies are


def test_full_report_has_a_no_copy_section(main_env, monkeypatch, capsys):
    monkeypatch.setattr(WA, 'find_repos', lambda: [])
    monkeypatch.setattr(WA, 'CACHE', None)
    WA.main([])
    out = capsys.readouterr().out
    assert 'no copy under a mission repo' in out and 'Solutions/JM31/PartC.lean' in out
    assert 'PartA.lean' not in out.split('no copy under a mission repo', 1)[1]


def test_quiet_counts_no_copy_files_by_folder(main_env, monkeypatch, capsys):
    monkeypatch.setattr(WA, 'find_repos', lambda: [])
    monkeypatch.setattr(WA, 'CACHE', None)
    WA.main(['--quiet'])
    out = capsys.readouterr().out
    assert 'no copy under a mission repo' in out and 'JM31 1' in out
