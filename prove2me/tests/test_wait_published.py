"""wait_published.py: wait for named statements, or a proposal's queue, to publish (fake platform)."""
import pytest

import wait_published as W


class Fake:
    """A platform whose state advances one step per poll (each `/theorems?theorem_name=` round)."""

    def __init__(self, published_after=None, jobs=None, items=None):
        self.published_after = dict(published_after or {})   # name -> poll number it publishes at
        self.jobs = list(jobs or [])                          # publish-job dicts
        self.items = items                                    # proposal items, or None
        self.polls = 0

    def call(self, m, p, b=None):
        assert m == 'GET', (m, p)
        if p.startswith('/theorems?theorem_name='):
            name = p.split('=', 1)[1]
            n = self.published_after.get(name)
            if n is not None and self.polls >= n:
                return {'theorems': [{'theorem_name': name, 'id': 'id-' + name}]}
            return {'theorems': []}
        if p.startswith('/publish-jobs?status='):
            st = p.split('=', 1)[1].split('&')[0]
            return {'publish_jobs': [j for j in self.jobs if j['status'] == st]}
        if p.startswith('/mission-proposals/'):
            return {'proposal': {'status': 'Draft', 'items': self.items(self.polls)}}
        raise AssertionError(p)


def run(fake, argv, monkeypatch):
    monkeypatch.setattr(W, 'call', fake.call)

    def tick(_s):
        fake.polls += 1
    monkeypatch.setattr(W.time, 'sleep', tick)
    with pytest.raises(SystemExit) as e:
        W.main(argv)
    return e.value.code


def test_exits_when_every_name_is_published(monkeypatch, capsys):
    fake = Fake(published_after={'N.a': 0, 'N.b': 2})
    assert run(fake, ['N.a', 'N.b', '--every', '1'], monkeypatch) == 0
    out = capsys.readouterr().out
    assert 'published N.a' in out and 'published N.b' in out and 'ALL PUBLISHED' in out
    assert fake.polls == 2


def test_a_job_scrolled_out_of_the_recent_jobs_still_counts(monkeypatch, capsys):
    # 2026-10-06: an ad-hoc waiter polled `/publish-jobs?limit=6`; once 33 later jobs were queued the
    # bundle's job left that window, "not found" read as "not done", and the waiter never exited.
    # Publication is looked up by name, whatever the job listing shows.
    fake = Fake(published_after={'HomeomorphAction': 1}, jobs=[])
    assert run(fake, ['HomeomorphAction', '--every', '1'], monkeypatch) == 0


def test_a_failed_job_ends_the_wait_with_its_message(monkeypatch, capsys):
    fake = Fake(published_after={}, jobs=[{'status': 'FAILED', 'theorem_name': 'N.a', 'id': 'j1',
                                           'created_at': '2026-10-06T10:00:00Z', 'error_message': 'boom'}])
    assert run(fake, ['N.a', '--every', '1'], monkeypatch) == 1
    out = capsys.readouterr().out
    assert 'FAILED N.a' in out and 'boom' in out


def test_an_old_failure_does_not_count_while_a_newer_job_is_queued(monkeypatch):
    fake = Fake(published_after={'N.a': 2}, jobs=[
        {'status': 'FAILED', 'theorem_name': 'N.a', 'id': 'old', 'created_at': '2026-10-05T09:00:00Z'},
        {'status': 'PENDING', 'theorem_name': 'N.a', 'id': 'new', 'created_at': '2026-10-06T10:00:00Z'}])
    assert run(fake, ['N.a', '--every', '1'], monkeypatch) == 0


def test_definitions_are_found_by_their_definition_name(monkeypatch):
    fake = Fake(published_after={}, jobs=[{'status': 'FAILED', 'definition_name': 'Bun', 'id': 'j',
                                           'created_at': '2026-10-06T10:00:00Z', 'error_message': 'x'}])
    assert run(fake, ['Bun', '--every', '1'], monkeypatch) == 1


def test_timeout(monkeypatch):
    fake = Fake(published_after={})
    assert run(fake, ['N.a', '--every', '10', '--timeout', '25'], monkeypatch) == 2


def test_proposal_mode_waits_until_every_item_has_a_theorem(monkeypatch, capsys):
    def items(polls):
        return [{'theorem_name': 'N.a', 'theorem_id': 't1'},
                {'theorem_name': 'N.b', 'theorem_id': 't2' if polls >= 3 else None}]
    fake = Fake(items=items)
    assert run(fake, ['--proposal', 'P', '--every', '1'], monkeypatch) == 0
    assert fake.polls == 3 and 'ALL PUBLISHED' in capsys.readouterr().out
