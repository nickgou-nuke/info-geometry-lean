"""Prevent ontology imports from silently selecting partial graph snapshots."""

import unittest
from unittest.mock import Mock

from tools.infra.decl_graph_generation import resolve_decl_graph_generation


class DeclarationGenerationTests(unittest.TestCase):
    def setUp(self):
        self.receipt = {
            "schema": "info_geometry.decl_graph_generation.v1",
            "status": "complete",
            "buildFingerprint": "a" * 64,
            "importRoot": "InfoGeometry.All",
            "namespace": "InfoGeometry",
            "declCollection": "decls_g_example",
            "edgeCollection": "edges_g_example",
            "declarationCount": 3,
            "validEdgeCount": 2,
            "emittedEdgeCount": 2,
            "removedOrphanCount": 0,
        }
        self.db = Mock()
        self.db.aql.execute.return_value = [self.receipt]
        self.db.aql.execute.side_effect = lambda query, **kw: (
            self.db.aql.execute.return_value if "decl_graph_generations" in query else [])
        self.db.has_collection.return_value = True
        self.collections = {
            "decls_g_example": Mock(), "edges_g_example": Mock(),
        }
        self.collections["decls_g_example"].count.return_value = 3
        self.collections["edges_g_example"].count.return_value = 2
        self.db.collection.side_effect = self.collections.__getitem__

    def test_complete_matching_snapshot_resolves_without_writes(self):
        self.assertEqual(resolve_decl_graph_generation(self.db, "example"), self.receipt)
        self.assertEqual(
            self.db.aql.execute.call_args_list[0].kwargs["bind_vars"],
            {"generationId": "example"},
        )
        for collection in self.collections.values():
            self.assertEqual([call[0] for call in collection.mock_calls], ["count"])

    def test_count_preserving_endpoint_corruption_is_rejected(self):
        self.db.aql.execute.side_effect = [[self.receipt], ["corrupt-edge"]]
        with self.assertRaisesRegex(ValueError, "dangling or foreign"):
            resolve_decl_graph_generation(self.db, "example")
        query = self.db.aql.execute.call_args.args[0]
        self.assertIn("IS_SAME_COLLECTION(@decls, e._from)", query)
        self.assertIn("IS_SAME_COLLECTION(@decls, e._to)", query)
        self.assertIn("DOCUMENT(e._to)", query)

    def test_absent_or_ambiguous_receipt_is_rejected(self):
        for rows in ([], [self.receipt, self.receipt]):
            with self.subTest(rows=len(rows)):
                self.db.aql.execute.return_value = rows
                with self.assertRaisesRegex(ValueError, "absent or ambiguous"):
                    resolve_decl_graph_generation(self.db, "example")

    def test_invalid_receipts_are_rejected(self):
        for field, value in (
            ("schema", "unknown"), ("status", "streaming"),
            ("declCollection", "decls; REMOVE"), ("edgeCollection", None),
            ("declarationCount", True), ("declarationCount", 0),
            ("validEdgeCount", -1), ("validEdgeCount", "2"),
        ):
            with self.subTest(field=field, value=value):
                self.db.aql.execute.return_value = [{**self.receipt, field: value}]
                with self.assertRaises(ValueError):
                    resolve_decl_graph_generation(self.db, "example")

    def test_missing_collection_is_rejected(self):
        self.db.has_collection.side_effect = lambda name: name != "edges_g_example"
        with self.assertRaisesRegex(ValueError, "missing"):
            resolve_decl_graph_generation(self.db, "example")

    def test_each_collection_count_must_match_receipt(self):
        for name, expected in (("decls_g_example", 3), ("edges_g_example", 2)):
            with self.subTest(collection=name):
                self.collections[name].count.return_value = expected - 1
                with self.assertRaisesRegex(ValueError, "count mismatch"):
                    resolve_decl_graph_generation(self.db, "example")
                self.collections[name].count.return_value = expected


if __name__ == "__main__":
    unittest.main()
