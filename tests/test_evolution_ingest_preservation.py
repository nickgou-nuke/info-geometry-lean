"""History refresh must preserve preexisting documents when explicitly requested."""
import json

import pytest

from tools.infra.evolution_ingest import ingest


class Collection:
    def __init__(self):
        self.rows = {}

    def import_bulk(self, rows, *, overwrite, on_duplicate, sync):
        assert overwrite is False
        for row in rows:
            if row['_key'] not in self.rows or on_duplicate == 'replace':
                self.rows[row['_key']] = dict(row)
        return {'errors': 0}

    def truncate(self):
        raise AssertionError('preservation must never truncate')


class Database:
    def __init__(self):
        self.collections = {}

    def has_collection(self, name):
        return name in self.collections

    def create_collection(self, name, *, edge=False):
        self.collections[name] = Collection()

    def collection(self, name):
        return self.collections[name]


def write_rows(path, rows):
    path.write_text(''.join(json.dumps(row) + '\n' for row in rows))
    return path


def weak_label(sha):
    return {
        'schema': 'info_geometry.commit_change_labels.v1',
        'sha': sha,
        'labels': [{
            'category': 'Bug Fix', 'categoryId': 'bugFix',
            'ruleWeightPercent': 85,
            'evidence': ['subject-body-rule:Bug Fix'],
            'evidenceKinds': ['subjectBodyRule'], 'status': 'weak_rule',
        }],
        'method': 'weak-rule-v3',
    }


def test_preserve_existing_protects_every_collection_and_adds_missing_commits(tmp_path):
    db = Database()
    commits = write_rows(tmp_path / 'commits.jsonl', [
        {'type': 'commit', 'sha': 'a', 'parents': []},
        {'type': 'commit', 'sha': 'b', 'parents': ['a']},
    ])
    labels = write_rows(tmp_path / 'labels.jsonl', [weak_label('a'), weak_label('b')])
    paths = write_rows(tmp_path / 'paths.jsonl', [{'sha': 'b', 'path': 'A.lean', 'change_type': 'A'}])
    stats = write_rows(tmp_path / 'stats.jsonl', [{'sha': 'b', 'path': 'A.lean', 'additions': 1}])
    ingest(db, commits, labels, paths, stats, batch_size=1)
    original = {}
    for name, collection in db.collections.items():
        assert collection.rows
        for row in collection.rows.values():
            row['reviewed_annotation'] = 'must survive'
            row['custom_value'] = 42
        original[name] = {key: dict(row) for key, row in collection.rows.items()}
    # The incoming value intentionally conflicts with the stored observation.
    write_rows(commits, [
        {'type': 'commit', 'sha': 'a', 'parents': [], 'custom_value': 999},
        {'type': 'commit', 'sha': 'b', 'parents': ['a']},
        {'type': 'commit', 'sha': 'c', 'parents': ['b']},
    ])
    write_rows(labels, [weak_label(key) for key in 'abc'])
    ingest(db, commits, labels, paths, stats, batch_size=1, preserve_existing=True)
    for name, rows in original.items():
        for key, row in rows.items():
            assert db.collection(name).rows[key] == row
    assert db.collection('evo_commits').rows['c']['sha'] == 'c'
    assert db.collection('evo_parent_edges').rows['b__c']['_to'] == 'evo_commits/c'


def test_ingest_rejects_reviewed_taxonomy_record_as_weak_commit_label(tmp_path):
    db = Database()
    commits = write_rows(tmp_path / 'commits.jsonl', [
        {'type': 'commit', 'sha': 'a', 'parents': []},
    ])
    reviewed = weak_label('a')
    reviewed['schema'] = 'info_geometry.reviewed_taxonomy_annotation.v4'
    labels = write_rows(tmp_path / 'labels.jsonl', [reviewed])

    with pytest.raises(ValueError, match='unsupported schema or method'):
        ingest(db, commits, labels, batch_size=1)
    assert db.collection('evo_commits').rows == {}
    assert db.collection('evo_labels').rows == {}


@pytest.mark.parametrize('options', [
    {'replace': True, 'preserve_existing': True}, {'batch_size': 0},
])
def test_invalid_modes_fail_before_database_mutation(tmp_path, options):
    db = Database()
    with pytest.raises(ValueError):
        ingest(db, tmp_path / 'not-read.jsonl', **options)
    assert db.collections == {}
