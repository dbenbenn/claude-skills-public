"""section.py: what a producer writes, and the checks that keep a bad file off the page."""
import json
import os

import pytest

import section as S


def read(home, sid):
    return json.load(open(os.path.join(home, 'sections', sid + '.json')))


def test_publish_writes_a_complete_section(tmp_path):
    S.publish('erdos3-v2', title='Erdős 3 v2', phases=[{'name': 'Bundles', 'done': 3, 'total': 10}],
              processes=[{'label': 'publisher', 'match': r'split_run\.py'}], home=str(tmp_path), now=100)
    s = read(tmp_path, 'erdos3-v2')
    assert s['title'] == 'Erdős 3 v2' and s['updated'] == 100 and s['state'] == 'running'
    assert s['phases'] == [{'name': 'Bundles', 'done': 3, 'total': 10, 'state': 'running', 'note': ''}]
    assert not [f for f in os.listdir(tmp_path / 'sections') if f.endswith('.tmp')]


def test_bad_sections_are_refused_before_writing(tmp_path):
    with pytest.raises(ValueError, match='id'):
        S.publish('Bad Id', title='x', home=str(tmp_path))
    with pytest.raises(ValueError, match='state'):
        S.publish('ok', title='x', state='busy', home=str(tmp_path))
    with pytest.raises(ValueError, match='done'):
        S.publish('ok', title='x', phases=[{'name': 'p', 'done': 'three', 'total': 4}], home=str(tmp_path))
    with pytest.raises(ValueError, match='regex'):
        S.publish('ok', title='x', processes=[{'label': 'l', 'match': '('}], home=str(tmp_path))
    assert not (tmp_path / 'sections' / 'ok.json').exists()


def test_validate_reports_every_problem():
    probs = S.validate({'title': '', 'updated': 'x', 'state': 'busy', 'phases': [{'name': 'p'}]})
    assert len(probs) >= 4


def test_cli_set_merges_phases_by_name(tmp_path, capsys):
    h = str(tmp_path)
    S.main(['--home', h, 'set', 'job', '--title', 'A job', '--phase', 'Build=1/4', '--phase', 'Test=0/2:waiting'])
    S.main(['--home', h, 'set', 'job', '--phase', 'Build=4/4:done:all built'])
    s = read(tmp_path, 'job')
    assert [(p['name'], p['done'], p['state'], p['note']) for p in s['phases']] == [
        ('Build', 4, 'done', 'all built'), ('Test', 0, 'waiting', '')]
    assert s['title'] == 'A job'


def test_cli_alerts_processes_links_and_remove(tmp_path):
    h = str(tmp_path)
    S.main(['--home', h, 'set', 'job', '--title', 'J', '--alert', 'NEEDS A PERSON: B12',
            '--process', 'lake=lake build', '--link', 'log=http://x/y'])
    s = read(tmp_path, 'job')
    assert s['alerts'] == ['NEEDS A PERSON: B12']
    assert s['processes'] == [{'label': 'lake', 'match': 'lake build'}]
    assert s['links'] == [{'label': 'log', 'url': 'http://x/y'}]
    S.main(['--home', h, 'set', 'job', '--clear-alerts', '--state', 'done'])
    s = read(tmp_path, 'job')
    assert s['alerts'] == [] and s['state'] == 'done'
    S.main(['--home', h, 'remove', 'job'])
    assert not (tmp_path / 'sections' / 'job.json').exists()


def test_cli_needs_a_title_for_a_new_section(tmp_path):
    with pytest.raises(SystemExit):
        S.main(['--home', str(tmp_path), 'set', 'job', '--phase', 'A=1/2'])


def test_phase_note_may_contain_colons(tmp_path):
    S.main(['--home', str(tmp_path), 'set', 'job', '--title', 'J', '--phase', 'A=1/2:running:ETA 12:30'])
    assert read(tmp_path, 'job')['phases'][0]['note'] == 'ETA 12:30'
