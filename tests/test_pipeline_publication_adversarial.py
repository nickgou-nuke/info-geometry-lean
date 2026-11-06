"""Failure-injection regressions for declaration export and typed projection.

Subprocess/database fakes test failure boundaries, not live transactions.
The opt-in AQL case evaluates bound fixtures without writing database records.
"""

import importlib.util
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

from tools.infra import decl_graph_generation
from tools.infra import refresh_decl_graph as refresh


class Collection:
    def __init__(self, fail_import=False):
        self.rows = {}
        self.fail_import = fail_import
        self.inserts = []

    def import_bulk(self, rows, **kwargs):
        if self.fail_import:
            return {"errors": 1}
        for row in rows:
            self.rows[row["_key"]] = dict(row)
        return {"errors": 0}

    def count(self):
        return len(self.rows)

    def insert(self, row, **kwargs):
        self.inserts.append(dict(row))
        self.rows[row["_key"]] = dict(row)


class Database:
    def __init__(self, fail_import=False):
        self.collections = {}
        self.fail_import = fail_import
        self.aql = Mock()
        self.aql.execute.side_effect = self.orphan_query

    def has_collection(self, name):
        return name in self.collections

    def create_collection(self, name, **kwargs):
        self.collections[name] = Collection(self.fail_import)

    def collection(self, name):
        return self.collections[name]

    __getitem__ = collection

    def orphan_query(self, query, bind_vars):
        # Model DOCUMENT endpoint existence, without performing any AQL.
        edges = self.collections[bind_vars["@edgeCollection"]].rows.values()
        missing = 0
        for edge in edges:
            for endpoint in (edge["_from"], edge["_to"]):
                collection, key = endpoint.split("/", 1)
                if collection not in self.collections or key not in self.collections[collection].rows:
                    missing += 1
                    break
        return [missing]


class TrackingStream(io.StringIO):
    drained_at_close = False

    def close(self):
        if not self.closed:
            self.drained_at_close = self.tell() == len(self.getvalue())
        super().close()


class Process:
    def __init__(self, text, exit_code=0):
        self.stdout = TrackingStream(text)
        self.exit_code = exit_code
        self.returncode = None
        self.waited = 0
        self.drained_at_wait = False

    def wait(self):
        self.waited += 1
        self.drained_at_wait = (self.stdout.drained_at_close if self.stdout.closed
                                else self.stdout.tell() == len(self.stdout.getvalue()))
        self.returncode = self.exit_code
        return self.returncode

    def poll(self):
        return self.returncode


class PublicationTests(unittest.TestCase):
    def run_stream(self, records, *, exit_code=0, fail_import=False, **kwargs):
        text = "\n".join(record if isinstance(record, str) else json.dumps(record)
                         for record in records) + "\n"
        proc = Process(text, exit_code)
        db = Database(fail_import)
        arango = Mock()
        arango.ArangoClient.return_value.db.return_value = db
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            executable = root / ".lake/build/bin/dagIndexer"
            executable.parent.mkdir(parents=True)
            executable.touch()
            with (
                patch.object(refresh, "load_repo_arango_env"),
                patch.object(refresh.subprocess, "run", return_value=Mock(stdout="/dependency/lib")),
                patch.object(refresh.subprocess, "Popen", return_value=proc),
                patch.object(refresh, "arango_endpoint", return_value="http://unused"),
                patch.object(refresh, "arango_username", return_value="test"),
                patch.object(refresh, "arango_password", return_value="test"),
                patch.object(refresh, "compute_lean_source_hash", return_value="current-source"),
                patch.object(refresh, "compute_olean_content_hash", return_value="current-olean"),
                patch.dict(sys.modules, {"arango": arango}),
            ):
                result = refresh.stream_to_arango(
                    root, "InfoGeometry.All", "InfoGeometry", "test", "exe",
                    "qa_fixture", "a" * 64, **kwargs)
        self.assertTrue(proc.stdout.closed)
        self.assertGreaterEqual(proc.waited, 1)
        self.assertTrue(proc.drained_at_wait)
        return result, db

    def assert_unpublished(self, records, **kwargs):
        result, db = self.run_stream(records, **kwargs)
        self.assertNotEqual(result, 0)
        self.assertNotIn("decl_graph_generations", db.collections)
        return result, db

    def test_empty_stream_has_no_complete_receipt(self):
        self.assert_unpublished([])

    def test_malformed_record_drains_remaining_output_without_publication(self):
        for record in ("not-json", [], {}, {"name": None}, {"name": ""},
                       {"name": "A", "key": "not-the-canonical-key"},
                       {"src": "A", "dst": "B", "kind": "unknown"},
                       {"src": "", "dst": "B", "kind": "type"},
                       {"_from": "old/a", "_to": "old/b", "kind": "type"}):
            with self.subTest(record=record):
                self.assert_unpublished([record, {"name": "A"}, {"name": "B"}])

    def test_duplicate_declarations_cannot_publish_emitted_count(self):
        self.assert_unpublished([{"name": "A"}, {"name": "A"}])

    def test_duplicate_edges_cannot_publish_emitted_count(self):
        edge = {"src": "A", "dst": "B", "kind": "type"}
        self.assert_unpublished([{"name": "A"}, {"name": "B"}, edge, edge])

    def test_dangling_edge_has_no_complete_receipt(self):
        self.assert_unpublished([{"name": "A"}, {"src": "A", "dst": "missing", "kind": "type"}])

    def test_old_endpoint_metadata_is_rejected_before_publication(self):
        edge = {"src": "A", "dst": "B", "kind": "type",
                "_from": "old/a", "_to": "old/b"}
        self.assert_unpublished([edge, {"name": "A"}, {"name": "B"}])

    def test_valid_forward_edge_is_published_with_canonical_identity(self):
        edge = {"src": "A", "dst": "B", "kind": "type"}
        result, db = self.run_stream([edge, {"name": "A"}, {"name": "B"}])
        self.assertEqual(result, 0)
        rows = db.collection("edges_g_qa_fixture").rows
        self.assertEqual(list(rows), [refresh.edge_key("A", "type", "B")])
        stored = next(iter(rows.values()))
        self.assertEqual(stored["_from"], "decls_g_qa_fixture/" + refresh.decl_key("A"))
        self.assertEqual(stored["_to"], "decls_g_qa_fixture/" + refresh.decl_key("B"))
        receipt = db.collection("decl_graph_generations").inserts[0]
        self.assertEqual((receipt["declarationCount"], receipt["emittedEdgeCount"],
                          receipt["validEdgeCount"], receipt["removedOrphanCount"]), (2, 1, 1, 0))

    def test_failed_exporter_does_not_publish(self):
        result, _ = self.assert_unpublished([{"name": "A"}], exit_code=7)
        self.assertEqual(result, 7)

    def test_database_import_errors_do_not_publish_and_reap_child(self):
        self.assert_unpublished([{"name": "A"}], fail_import=True)

    def test_source_or_olean_drift_prevents_publication(self):
        for expectation in ({"expected_source_hash": "old-source"},
                            {"expected_olean_hash": "old-olean"}):
            with self.subTest(expectation=expectation):
                self.assert_unpublished([{"name": "A"}], **expectation)

    def test_repeated_stdout_read_failure_still_closes_and_reaps(self):
        class BrokenStream:
            closed = False

            def __iter__(self):
                return self

            def __next__(self):
                raise UnicodeError("unreadable exporter output")

            def close(self):
                self.closed = True

        proc = Mock()
        proc.stdout = BrokenStream()
        proc.poll.return_value = None
        db = Database()
        arango = Mock()
        arango.ArangoClient.return_value.db.return_value = db
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            executable = root / ".lake/build/bin/dagIndexer"
            executable.parent.mkdir(parents=True)
            executable.touch()
            with patch.object(refresh, "load_repo_arango_env"), \
                 patch.object(refresh.subprocess, "run", return_value=Mock(stdout="")), \
                 patch.object(refresh.subprocess, "Popen", return_value=proc), \
                 patch.object(refresh, "arango_endpoint", return_value="http://unused"), \
                 patch.object(refresh, "arango_username", return_value="test"), \
                 patch.object(refresh, "arango_password", return_value="test"), \
                 patch.dict(sys.modules, {"arango": arango}):
                with self.assertRaisesRegex(UnicodeError, "unreadable"):
                    refresh.stream_to_arango(root, "InfoGeometry.All", "InfoGeometry", "test",
                                             "exe", "qa_fixture", "a" * 64)
        self.assertTrue(proc.stdout.closed)
        proc.wait.assert_called_once()
        self.assertNotIn("decl_graph_generations", db.collections)


class ConnectionKeywordTests(unittest.TestCase):
    def test_password_delimiters_reach_psycopg_as_literal_keyword(self):
        root = Path(__file__).resolve().parents[1]
        password = "test:@/?#% password\\suffix"
        env = {key: "test" for key in (
            "ARANGO_ENDPOINT", "ARANGO_DATABASE", "ARANGO_USER", "ARANGO_PASS",
            "POSTGRES_USER")}
        env["POSTGRES_PASSWORD"] = password
        env["POSTGRES_PORT"] = "5433"
        env["POSTGRES_DATABASE"] = "fixture_ontology"
        for name, argv in (
            ("arango_to_ontology", ["--decl-collection", "fixture_decls"]),
            ("arango_to_ontology_relationships",
             ["--decl-collection", "fixture_decls", "--edge-collection", "fixture_edges"]),
        ):
            with self.subTest(importer=name):
                spec = importlib.util.spec_from_file_location(
                    "qa_" + name, root / "tools/infra" / (name + ".py"))
                module = importlib.util.module_from_spec(spec)
                psycopg = Mock()
                psycopg.connect.side_effect = RuntimeError("stop at connection boundary")
                arango = Mock()
                db = arango.ArangoClient.return_value.db.return_value
                db.collection.return_value.count.return_value = 1
                db.aql.execute.return_value = []
                with patch.dict(os.environ, env), patch.dict(sys.modules, {
                    "psycopg": psycopg, "arango": arango,
                    "decl_graph_generation": decl_graph_generation,
                }), patch.object(sys, "argv", [name, *argv]):
                    spec.loader.exec_module(module)
                    with self.assertRaisesRegex(RuntimeError, "stop at connection boundary"):
                        module.main()
                psycopg.connect.assert_called_once_with(**module.PG_CONNECT)
                self.assertEqual(psycopg.connect.call_args.kwargs["password"], password)
                self.assertEqual(psycopg.connect.call_args.kwargs["dbname"], "fixture_ontology")


def relationship_importer():
    root = Path(__file__).resolve().parents[1]
    spec = importlib.util.spec_from_file_location(
        "qa_relationship_importer", root / "tools/infra/arango_to_ontology_relationships.py")
    module = importlib.util.module_from_spec(spec)
    env = {key: "test" for key in (
        "ARANGO_ENDPOINT", "ARANGO_DATABASE", "ARANGO_USER", "ARANGO_PASS",
        "POSTGRES_USER", "POSTGRES_PASSWORD")}
    with patch.dict(os.environ, env), patch.dict(sys.modules, {
        "psycopg": Mock(), "arango": Mock(), "decl_graph_generation": decl_graph_generation,
    }):
        spec.loader.exec_module(module)
    return module


class ProjectionTests(unittest.TestCase):
    def test_short_edge_iterator_cannot_report_complete_generation(self):
        module = relationship_importer()
        db = Mock()
        db.collection.return_value.count.return_value = 2
        db.aql.execute.side_effect = [[], [{"name": "A", "key": "a"},
                                          {"name": "B", "key": "b"}],
                                     [{"src": "A", "dst": "B", "kind": "type"}]]
        cur = module.psycopg.connect.return_value.cursor.return_value
        cur.fetchall.return_value = [("ta", "a", "A", "semantic"),
                                     ("tb", "b", "B", "semantic")]
        with patch.object(sys, "argv", ["importer", "--generation-id", "fixture", "--legacy-additive"]), \
             patch.object(module, "connect_arango", return_value=db), \
             patch.object(module, "resolve_decl_graph_generation", return_value={
                 "declCollection": "fixture_decls", "edgeCollection": "fixture_edges"}), \
             patch.object(module, "copy_relationships"), \
             patch.object(module, "ensure_term_term_table"):
            with self.assertRaisesRegex(SystemExit, "processed 1 of 2"):
                module.main()
        # The importer must validate source cardinality before committing any
        # batch. A short cursor used to leave committed relationship rows.
        conn = module.psycopg.connect.return_value
        conn.commit.assert_not_called()
        conn.rollback.assert_called_once()

    def test_invalid_edge_preflight_stops_before_postgres_connection(self):
        module = relationship_importer()
        db = Mock()
        db.collection.return_value.count.return_value = 1
        db.aql.execute.return_value = ["invalid-edge"]
        with patch.object(sys, "argv", ["importer", "--decl-collection", "fixture_decls",
                                        "--edge-collection", "fixture_edges"]), \
             patch.object(module, "connect_arango", return_value=db):
            with self.assertRaisesRegex(ValueError, "invalid dependency edges"):
                module.main()
        module.psycopg.connect.assert_not_called()


@unittest.skipUnless(os.environ.get("ONTOLOGY_LIVE_TEST") == "1", "requires configured Arango")
class LivePreflightTests(unittest.TestCase):
    def test_edge_validation_predicate_with_bound_fixtures(self):
        # Preserve the production predicate; replace only collection/DOCUMENT
        # reads with bound in-memory records. This is read-only AQL, not DB I/O
        # integrity or a live-import transaction test.
        from tools.infra.arango_root_to_leaf_topology import arango_target, run_aql
        module = relationship_importer()
        db = Mock()
        db.aql.execute.return_value = []
        module.validate_dependency_edges(db, "fixture_edges", "fixture_decls")
        query = db.aql.execute.call_args.args[0]
        query = query.replace("FOR e IN @@edges", "FOR e IN @edges")
        query = query.replace("DOCUMENT(expectedFrom)", "@docs[expectedFrom]")
        query = query.replace("DOCUMENT(expectedTo)", "@docs[expectedTo]")
        source = "fixture_decls/" + refresh.decl_key("A")
        destination = "fixture_decls/" + refresh.decl_key("B")
        valid = {"_key": "fixture", "src": "A", "dst": "B", "kind": "type",
                 "_from": source, "_to": destination}
        docs = {source: {"name": "A"}, destination: {"name": "B"}}
        cases = [(valid, docs, []),
                 ({**valid, "kind": "foreign"}, docs, ["fixture"]),
                 ({**valid, "_from": "old_generation/a"}, docs, ["fixture"]),
                 ({**valid, "src": None}, docs, ["fixture"]),
                 (valid, {source: {"name": "A"}}, ["fixture"]),
                 (valid, {**docs, destination: {"name": "wrong"}}, ["fixture"])]
        target = arango_target(Path(__file__).resolve().parents[1])
        for edge, documents, expected in cases:
            with self.subTest(edge=edge, documents=documents):
                rows = run_aql(target, query, {"edges": [edge], "docs": documents,
                                              "decls": "fixture_decls"})
                self.assertEqual(rows, expected)


if __name__ == "__main__":
    unittest.main()
