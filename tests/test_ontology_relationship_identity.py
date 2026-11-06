"""Identity preflight must reject ambiguous or incomplete graph projections."""

import importlib.util
import contextlib
import io
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import Mock, patch

from tools.infra import decl_graph_generation


def load_importer():
    path = Path(__file__).resolve().parents[1] / "tools/infra/arango_to_ontology_relationships.py"
    spec = importlib.util.spec_from_file_location("relationship_importer_test", path)
    module = importlib.util.module_from_spec(spec)
    env = {key: "test" for key in (
        "ARANGO_ENDPOINT", "ARANGO_DATABASE", "ARANGO_USER", "ARANGO_PASS",
        "POSTGRES_USER", "POSTGRES_PASSWORD",
    )}
    with patch.dict(os.environ, env), patch.dict(sys.modules, {
        "psycopg": Mock(), "arango": Mock(),
        "decl_graph_generation": decl_graph_generation,
    }):
        spec.loader.exec_module(module)
    return module


class RelationshipIdentityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.importer = load_importer()

    def test_unique_term_identities_resolve(self):
        cur = Mock()
        cur.fetchall.return_value = [("term-a", "decl-a", "A", "semantic"),
                                    ("term-b", "decl-b", "B", "semantic")]
        self.assertEqual(self.importer.load_term_ids(cur, {"A": "decl-a", "B": "decl-b"}),
                         {"decl-a": "term-a", "decl-b": "term-b"})

    def test_generation_write_requires_explicit_legacy_acknowledgement(self):
        self.importer.psycopg.connect.reset_mock()
        error = io.StringIO()
        with patch.object(sys, "argv", ["importer", "--generation-id", "example"]), \
             patch.object(self.importer, "connect_arango") as connect, \
             contextlib.redirect_stderr(error):
            with self.assertRaises(SystemExit) as raised:
                self.importer.main()
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("Generation-pinned projection is not implemented", error.getvalue())
        connect.assert_not_called()
        self.importer.psycopg.connect.assert_not_called()

    def test_empty_generation_id_is_rejected_before_connection(self):
        with patch.object(sys, "argv", ["importer", "--generation-id", "", "--legacy-additive"]), \
             patch.object(self.importer, "connect_arango") as connect, \
             contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as raised:
                self.importer.main()
        self.assertEqual(raised.exception.code, 2)
        connect.assert_not_called()
        self.importer.psycopg.connect.assert_not_called()

    def test_empty_generation_relationship_set_is_valid(self):
        db = Mock()
        db.collection.return_value.count.return_value = 0
        db.aql.execute.side_effect = [[], [], []]
        conn = self.importer.psycopg.connect.return_value
        cur = conn.cursor.return_value
        cur.fetchall.return_value = []
        with patch.object(sys, "argv", ["importer", "--generation-id", "example",
                                        "--legacy-additive"]), \
             patch.object(self.importer, "connect_arango", return_value=db), \
             patch.object(self.importer, "resolve_decl_graph_generation", return_value={
                 "declCollection": "decls_example", "edgeCollection": "edges_example",
             }), \
             patch.object(self.importer, "ensure_term_term_table"):
            self.assertEqual(self.importer.main(), 0)
        conn.close.assert_called_once()

    def test_duplicate_imported_identity_is_not_arbitrarily_selected(self):
        cur = Mock()
        cur.fetchall.return_value = [("term-a", "decl-a", "A", "semantic"),
                                    ("term-b", "decl-a", "A", "semantic")]
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            self.importer.load_term_ids(cur, {"A": "decl-a"})

    def test_wrong_name_or_source_cannot_impersonate_selected_declaration(self):
        for name, source in (("B", "semantic"), ("A", "other")):
            with self.subTest(name=name, source=source):
                cur = Mock()
                cur.fetchall.return_value = [("term-a", "decl-a", name, source)]
                with self.assertRaisesRegex(ValueError, "inconsistent name/source"):
                    self.importer.load_term_ids(cur, {"A": "decl-a"})

    def test_duplicate_source_names_are_rejected(self):
        db = Mock()
        db.aql.execute.return_value = [
            {"name": "A.theorem", "key": "a"},
            {"name": "A.theorem", "key": "b"},
        ]
        with self.assertRaisesRegex(ValueError, "duplicate declaration"):
            self.importer.load_decl_keys(db, "decls_g_example")

    def test_missing_generation_terms_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "1 declarations.*term importer first"):
            self.importer.require_generation_terms({"A": "a", "B": "b"}, {"a": "term-a"})

    def test_malformed_declarations_are_not_silently_omitted(self):
        for row in ({"name": None, "key": "a"},
                    {"name": "", "key": "a"},
                    {"name": "A", "key": None},
                    {"name": 42, "key": "a"}):
            with self.subTest(row=row):
                db = Mock()
                db.aql.execute.return_value = [row]
                with self.assertRaisesRegex(ValueError, "missing declaration"):
                    self.importer.load_decl_keys(db, "decls_g_example")
                self.assertNotIn("FILTER d.name", db.aql.execute.call_args.args[0])

    def test_other_generations_do_not_prevent_complete_resolution(self):
        self.importer.require_generation_terms(
            {"A": "a"}, {"a": "term-a", "older-b": "term-b"})


if __name__ == "__main__":
    unittest.main()
