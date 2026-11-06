"""UNRUN candidate; parent destination: tests/test_decl_graph_receipt_integrity.py.

Requires g_a_receipt_integrity_v2.patch integrated against its observed owners.
All processes, credentials and database objects are mocked; no real services.
"""
from argparse import Namespace
import io
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import Mock, patch

from tools.infra import refresh_decl_graph as refresh
from tools.infra.decl_graph_generation import (
    resolve_decl_graph_generation, validate_generation_id,
)


class ReceiptValidationTests(unittest.TestCase):
    def fixture(self, **updates):
        receipt = dict(schema='info_geometry.decl_graph_generation.v1', status='complete',
                       buildFingerprint='a' * 64, importRoot='InfoGeometry.All',
                       namespace='InfoGeometry', declCollection='decls_g_test',
                       edgeCollection='edges_g_test', declarationCount=2,
                       emittedEdgeCount=1, validEdgeCount=1, removedOrphanCount=0)
        receipt.update(updates)
        db = Mock()
        db.aql.execute.side_effect = lambda query, **kw: (
            [receipt] if 'decl_graph_generations' in query else [])
        db.has_collection.return_value = True
        collections = {name: Mock() for name in ('decls_g_test', 'edges_g_test')}
        collections['decls_g_test'].count.return_value = 2
        collections['edges_g_test'].count.return_value = receipt['validEdgeCount']
        db.collection.side_effect = collections.__getitem__
        return db, receipt

    def test_invalid_ids_rejected_before_database_or_process_access(self):
        for value in ('', 'with-hyphen', 'é', 'Ａ', 'a\n', 'a/b', 'a' * 33):
            with self.subTest(value=value):
                db = Mock()
                with self.assertRaises(ValueError):
                    validate_generation_id(value)
                with self.assertRaises(ValueError):
                    resolve_decl_graph_generation(db, value)
                db.aql.execute.assert_not_called()
                with patch.object(refresh.subprocess, 'run') as run:
                    self.assertNotEqual(refresh.stream_to_arango(
                        Path('/unused'), 'InfoGeometry.All', 'InfoGeometry',
                        'unused', 'run', value, 'a' * 64), 0)
                run.assert_not_called()

    def test_cli_rejects_empty_hyphen_and_unicode_ids(self):
        for value in ('', 'a-b', 'é'):
            args = Namespace(stream=True, replace_live=False, generation_id=value,
                             build_fingerprint='a' * 64)
            with self.subTest(value=value), patch.object(refresh, 'stream_to_arango') as stream:
                with self.assertRaises(SystemExit):
                    refresh._run_refresh(args, Path('/unused'), Mock())
                stream.assert_not_called()

    def test_ascii_and_boundary_ids_are_allowed(self):
        for value in ('a', '_', 'A0_b', 'x' * 32, 'decl_' + 'a' * 24):
            validate_generation_id(value)

    def test_receipt_fields_are_mandatory_and_strict(self):
        for field in ('declarationCount', 'emittedEdgeCount', 'validEdgeCount', 'removedOrphanCount'):
            for value in (None, True, False, -1, '1', 1.0):
                with self.subTest(field=field, value=value):
                    db, _ = self.fixture(**{field: value})
                    with self.assertRaises(ValueError):
                        resolve_decl_graph_generation(db, 'test')
            db, receipt = self.fixture()
            receipt.pop(field)
            with self.assertRaises(ValueError):
                resolve_decl_graph_generation(db, 'test')

    def test_edge_counts_must_agree_even_when_stored_matches_valid(self):
        for emitted in (0, 2):
            db, _ = self.fixture(emittedEdgeCount=emitted)
            with self.assertRaisesRegex(ValueError, 'count mismatch'):
                resolve_decl_graph_generation(db, 'test')

    def test_orphan_removal_and_empty_declarations_are_rejected(self):
        for changes in ({'removedOrphanCount': 1}, {'declarationCount': 0}):
            db, _ = self.fixture(**changes)
            with self.assertRaises(ValueError):
                resolve_decl_graph_generation(db, 'test')

    def test_zero_edge_discrete_graph_resolves(self):
        db, receipt = self.fixture(emittedEdgeCount=0, validEdgeCount=0)
        self.assertEqual(resolve_decl_graph_generation(db, 'test'), receipt)

    def test_metadata_is_required_but_not_a_build_certificate(self):
        for field, bad in (
            ('buildFingerprint', ''), ('buildFingerprint', 'opaque'),
            ('buildFingerprint', 'A' * 64), ('buildFingerprint', None),
            ('importRoot', ''), ('importRoot', 'InfoGeometry.All,'),
            ('namespace', ''), ('namespace', ' InfoGeometry'),
        ):
            db, _ = self.fixture(**{field: bad})
            with self.subTest(field=field, bad=bad), self.assertRaises(ValueError):
                resolve_decl_graph_generation(db, 'test')


class MemoryCollection:
    def __init__(self):
        self.rows = {}
        self.imports = []
        self.receipts = []
        self.count_delta = 0

    def import_bulk(self, rows, **options):
        self.imports.append((list(rows), options))
        for row in rows:
            self.rows[row['_key']] = dict(row)
        return {'errors': 0}

    def count(self):
        return len(self.rows) + self.count_delta

    def insert(self, receipt, **options):
        self.receipts.append(receipt)


class StreamIntegrityTests(unittest.TestCase):
    def run_stream(self, records, *, orphan_count=0, decl_delta=0, edge_delta=0):
        collections = {name: MemoryCollection() for name in
                       ('decls_g_test', 'edges_g_test', 'decl_graph_generations')}
        collections['decls_g_test'].count_delta = decl_delta
        collections['edges_g_test'].count_delta = edge_delta
        db = Mock()
        db.has_collection.return_value = False
        db.collection.side_effect = collections.__getitem__
        # Mock special item access with a real adapter (Mock lacks __getitem__).
        class Database:
            def __getitem__(self, name):
                return collections[name]
            def __getattr__(self, name):
                return getattr(db, name)
        db.aql.execute.return_value = [orphan_count]
        arango = Mock()
        arango.ArangoClient.return_value.db.return_value = Database()
        text = ''.join((row if isinstance(row, str) else json.dumps(row)) + '\n'
                       for row in records)
        proc = Mock(stdout=io.StringIO(text), returncode=0)
        proc.poll.return_value = 0
        with (
            patch.dict(sys.modules, {'arango': arango}),
            patch.object(refresh, 'load_repo_arango_env'),
            patch.object(refresh, 'arango_endpoint', return_value='http://unused'),
            patch.object(refresh, 'arango_username', return_value='unused'),
            patch.object(refresh, 'arango_password', return_value='unused'),
            patch.object(refresh.subprocess, 'run', return_value=Mock(stdout='/unused')),
            patch.object(refresh.subprocess, 'Popen', return_value=proc),
        ):
            code = refresh.stream_to_arango(Path('/unused'), 'InfoGeometry.All',
                                           'InfoGeometry', 'unused', 'run', 'test', 'a' * 64)
        return code, collections, db

    def assert_unpublished(self, records, **kwargs):
        code, collections, _ = self.run_stream(records, **kwargs)
        self.assertNotEqual(code, 0)
        self.assertEqual(collections['decl_graph_generations'].receipts, [])

    def test_malformed_and_ambiguous_records_fail_closed(self):
        for bad in ('{', 'null', '[]', '42', {}, {'name': ''}, {'name': 2},
                    {'src': 'A'}, {'dst': 'A', 'name': 'B'},
                    {'src': 'A', 'dst': 'B'},
                    {'src': 'A', 'dst': 'B', 'kind': 'unknown'},
                    {'name': 'A', 'key': 'wrong'},
                    {'name': 'A', '_key': 'wrong'},
                    {'src': 'A', 'dst': 'B', 'kind': 'type', '_key': 'wrong'}):
            with self.subTest(bad=bad):
                self.assert_unpublished([{'name': 'A'}, bad])

    def test_empty_declarations_fail_but_nonempty_zero_edge_graph_publishes(self):
        self.assert_unpublished([])
        code, collections, _ = self.run_stream([{'name': 'A'}, ''])
        self.assertEqual(code, 0)
        receipt = collections['decl_graph_generations'].receipts[0]
        self.assertEqual((receipt['declarationCount'], receipt['emittedEdgeCount'],
                          receipt['validEdgeCount'], receipt['removedOrphanCount']), (1, 0, 0, 0))

    def test_duplicate_declarations_within_and_across_batches(self):
        self.assert_unpublished([{'name': 'A'}, {'name': 'A'}])
        self.assert_unpublished([{'name': f'D{i}'} for i in range(5000)] + [{'name': 'D0'}])

    def test_duplicate_edges_within_and_across_batches(self):
        edge = {'src': 'A', 'dst': 'B', 'kind': 'type'}
        for count in (2, 5001):
            self.assert_unpublished([{'name': 'A'}, {'name': 'B'}] + [edge] * count)

    def test_count_loss_and_unexpected_extra_rows_fail_closed(self):
        for delta in (-1, 1):
            self.assert_unpublished([{'name': 'A'}, {'name': 'B'}], decl_delta=delta)
            self.assert_unpublished([{'name': 'A'}, {'name': 'B'},
                                     {'src': 'A', 'dst': 'B', 'kind': 'type'}], edge_delta=delta)

    def test_foreign_endpoints_cannot_be_hidden_by_normalization(self):
        self.assert_unpublished([{'name': 'A'}, {'name': 'B'},
                                 {'src': 'A', 'dst': 'B', 'kind': 'type',
                                  '_from': 'decls_g_old/a', '_to': 'decls_g_old/b'}])

    def test_endpoint_query_binds_exact_selected_collection(self):
        code, _, db = self.run_stream([{'name': 'A'}])
        self.assertEqual(code, 0)
        query = db.aql.execute.call_args.args[0]
        binds = db.aql.execute.call_args.kwargs['bind_vars']
        self.assertIn('IS_SAME_COLLECTION(@declCollection, e._from)', query)
        self.assertIn('IS_SAME_COLLECTION(@declCollection, e._to)', query)
        self.assertEqual(binds['declCollection'], 'decls_g_test')
        self.assert_unpublished([{'name': 'A'}], orphan_count=1)

    def test_forward_reference_is_retained_and_published(self):
        code, collections, _ = self.run_stream([
            {'name': 'A'}, {'src': 'A', 'dst': 'B', 'kind': 'type'}, {'name': 'B'}])
        self.assertEqual(code, 0)
        receipt = collections['decl_graph_generations'].receipts[0]
        self.assertEqual(receipt['emittedEdgeCount'], 1)
        self.assertEqual(receipt['validEdgeCount'], 1)


if __name__ == '__main__':
    unittest.main()
