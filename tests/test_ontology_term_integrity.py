"""A malformed or partial projection must not be reported as an import success."""

import importlib.util
import contextlib
import io
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import MagicMock, Mock, patch

from tools.infra import decl_graph_generation


def load_importer():
    path = Path(__file__).resolve().parents[1] / "tools/infra/arango_to_ontology.py"
    spec = importlib.util.spec_from_file_location("term_integrity_importer", path)
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


class TermIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.importer = load_importer()

    def test_invalid_source_fails_before_postgres_connection(self):
        for responses in ((["bad-key"],), ([], ["Duplicate.name"])):
            with self.subTest(responses=responses):
                db = Mock()
                db.collection.return_value.count.return_value = 2
                db.aql.execute.side_effect = responses
                with patch.object(self.importer, "connect_arango", return_value=db), \
                     patch.object(sys, "argv", ["importer", "--decl-collection", "decls"]):
                    with self.assertRaises(SystemExit):
                        self.importer.main()
                self.importer.psycopg.connect.assert_not_called()

    def test_generation_write_requires_explicit_legacy_acknowledgement(self):
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

    def test_empty_generation_id_does_not_select_another_import_mode(self):
        with patch.object(sys, "argv", ["importer", "--generation-id", "", "--legacy-additive"]), \
             patch.object(self.importer, "connect_arango") as connect, \
             contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as raised:
                self.importer.main()
        self.assertEqual(raised.exception.code, 2)
        connect.assert_not_called()
        self.importer.psycopg.connect.assert_not_called()

    def test_upsert_requires_exact_returned_identity_set(self):
        terms = [{"name": "A", "description": "", "synonyms": [], "aokey": "a"}]
        for rows in ([], [("t", "b")], [("t", "a"), ("u", "a")], [(None, "a")]):
            with self.subTest(rows=rows):
                cur = MagicMock()
                cur.fetchall.return_value = rows
                with self.assertRaises(ValueError):
                    self.importer.copy_terms(cur, terms)

    def test_complete_upsert_returns_resolved_identity(self):
        cur = MagicMock()
        cur.fetchall.return_value = [("term-a", "a")]
        terms = [{"name": "A", "description": "", "synonyms": [], "aokey": "a"}]
        self.assertEqual(self.importer.copy_terms(cur, terms), {"a": "term-a"})


if __name__ == "__main__":
    unittest.main()
