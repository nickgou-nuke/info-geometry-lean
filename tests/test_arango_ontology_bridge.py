"""Unit and adversarial tests for the ArangoDB -> Auto-Ontology projection bridge.

These tests are fully offline: they exercise dry-run validation, lazy env
resolution, and the decl_projection logic with mocked connections.  No live
ArangoDB or PostgreSQL is required.
"""

from __future__ import annotations

import io
import json
import os
import sys
import tempfile
import unittest
from argparse import Namespace
from contextlib import redirect_stdout
from pathlib import Path
from types import ModuleType
from unittest.mock import Mock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
SRC = REPO_ROOT / "src"
TOOLS_INFRA = REPO_ROOT / "tools" / "infra"
for _p in (str(SRC), str(TOOLS_INFRA), str(REPO_ROOT)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

# ---------------------------------------------------------------------------
# Mock psycopg at sys.modules level BEFORE importing decl_projection so that
# collection succeeds without a live psycopg3 install.
# ---------------------------------------------------------------------------

_psycopg = ModuleType("psycopg")
_pq = ModuleType("psycopg.pq")
_pq.TransactionStatus = Mock(IDLE=0)
_jsonb_mod = ModuleType("psycopg.types.json")


class _Jsonb:
    def __init__(self, value):
        self.value = value


_jsonb_mod.Jsonb = _Jsonb
sys.modules["psycopg"] = _psycopg
sys.modules["psycopg.pq"] = _pq
sys.modules["psycopg.types"] = ModuleType("psycopg.types")
sys.modules["psycopg.types.json"] = _jsonb_mod

from ontology_bridge_common import get_arango_config, get_pg_connect  # noqa: E402
from arango_to_ontology import (  # noqa: E402
    _resolve_arango_env as resolve_arango,
    get_pg_connect as pg_connect_ontology,
    _run_offline_jsonl_dry_run as dry_run_decls,
)
from arango_to_ontology_relationships import (  # noqa: E402
    _resolve_arango_env as resolve_arango_rels,
    get_pg_connect as pg_connect_rels,
)
import decl_projection  # noqa: E402

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _make_args(**kwargs):
    defaults = {
        "arango_db": None,
        "decls_jsonl": None,
        "edges_jsonl": None,
        "generation_id": None,
        "deployment_uuid": None,
        "report_json": None,
    }
    defaults.update(kwargs)
    return Namespace(**defaults)


def _write_jsonl(path: Path, records: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        for rec in records:
            f.write(json.dumps(rec) + "\n")


def _run_and_capture(args, func):
    buf = io.StringIO()
    with redirect_stdout(buf):
        func(args)
    return json.loads(buf.getvalue())


# ---------------------------------------------------------------------------
# Lazy env resolution (NC-05: no import-time os.environ crashes)
# ---------------------------------------------------------------------------

class LazyEnvTests(unittest.TestCase):
    def test_get_pg_connect_returns_defaults_without_credentials(self):
        """get_pg_connect must return empty user/password, not raise KeyError."""
        for var in ("POSTGRES_USER", "POSTGRES_PASSWORD"):
            os.environ.pop(var, None)
        result = pg_connect_ontology()
        self.assertEqual(result["user"], "")
        self.assertEqual(result["password"], "")
        result2 = pg_connect_rels()
        self.assertEqual(result2["user"], "")
        self.assertEqual(result2["password"], "")

    def test_resolve_arango_env_does_not_crash_without_env(self):
        """_resolve_arango_env falls back to arango_env defaults without crashing."""
        for var in ("ARANGO_ENDPOINT", "ARANGO_DATABASE", "ARANGO_USER", "ARANGO_PASS"):
            os.environ.pop(var, None)
        # Should not raise KeyError; falls back to arango_env module defaults.
        endpoint, database, user, password = resolve_arango()
        self.assertIsInstance(endpoint, str)
        self.assertEqual(database, "infogeometry")
        endpoint2, database2, user2, password2 = resolve_arango_rels()
        self.assertIsInstance(endpoint2, str)
        self.assertEqual(database2, "infogeometry")

    def test_ontology_bridge_common_imports(self):
        """ontology_bridge_common provides lazy get_arango_config and get_pg_connect."""
        for var in ("POSTGRES_USER", "POSTGRES_PASSWORD"):
            os.environ.pop(var, None)
        with self.assertRaises(ValueError):
            get_pg_connect()
        for var in ("ARANGO_USER", "ARANGO_USERNAME", "ARANGO_PASS", "ARANGO_PASSWORD"):
            os.environ.pop(var, None)
        os.environ.pop("HIVE_ARANGO_ENV_FILE", None)
        with patch("ontology_bridge_common._REPO_ROOT", Path("/nonexistent")):
            with self.assertRaises(ValueError):
                get_arango_config()


# ---------------------------------------------------------------------------
# Dry-run validation (NC-05: offline --dry-run works)
# ---------------------------------------------------------------------------

class DryRunTests(unittest.TestCase):
    def test_dry_run_decls_validates_offline(self):
        """--dry-run with --decls-jsonl validates without PG/Arango."""
        tmp_dir = Path(tempfile.mkdtemp())
        try:
            records = [
                {"name": "InfoGeometry.TheoremA", "kind": "theorem", "doc": "doc A",
                 "module": "InfoGeometry", "relFile": "lean/InfoGeometry/A.lean",
                 "line": 10},
                {"name": "InfoGeometry.TheoremB", "kind": "lemma", "doc": "doc B",
                 "module": "InfoGeometry", "relFile": "lean/InfoGeometry/B.lean",
                 "line": 20},
            ]
            jsonl_path = tmp_dir / "decls.jsonl"
            _write_jsonl(jsonl_path, records)

            args = _make_args(decls_jsonl=jsonl_path)
            report = _run_and_capture(args, dry_run_decls)
            self.assertEqual(report["status"], "dry_run_ok")
            self.assertEqual(report["mode"], "offline_jsonl")
            self.assertEqual(report["expected_decl_count"], 2)
            self.assertEqual(report["loaded_decl_count"], 0)
            self.assertEqual(report["module_count"], 1)
            self.assertIsNotNone(report["source_digest"])
            self.assertEqual(len(report["source_digest"]), 64)
        finally:
            import shutil
            shutil.rmtree(tmp_dir, ignore_errors=True)

    def test_dry_run_edges_validates_offline(self):
        """--dry-run with --edges-jsonl validates without PG/Arango."""
        tmp_dir = Path(tempfile.mkdtemp())
        try:
            decl_records = [
                {"name": "InfoGeometry.A", "kind": "theorem", "doc": "doc A",
                 "module": "InfoGeometry"},
                {"name": "InfoGeometry.B", "kind": "theorem", "doc": "doc B",
                 "module": "InfoGeometry"},
            ]
            edge_records = [
                {"src": "InfoGeometry.A", "dst": "InfoGeometry.B", "kind": "type"},
            ]
            decl_path = tmp_dir / "decls.jsonl"
            edge_path = tmp_dir / "edges.jsonl"
            _write_jsonl(decl_path, decl_records)
            _write_jsonl(edge_path, edge_records)

            args = _make_args(decls_jsonl=decl_path, edges_jsonl=edge_path)
            report = _run_and_capture(args, dry_run_decls)
            self.assertEqual(report["status"], "dry_run_ok")
            self.assertEqual(report["expected_edge_count"], 1)
            self.assertEqual(report["loaded_edge_count"], 0)
        finally:
            import shutil
            shutil.rmtree(tmp_dir, ignore_errors=True)

    def test_dry_run_rejects_invalid_key(self):
        """Dry run rejects declaration records with mismatched _key."""
        tmp_dir = Path(tempfile.mkdtemp())
        try:
            records = [
                {"name": "InfoGeometry.A", "kind": "theorem", "doc": "doc",
                 "module": "InfoGeometry", "_key": "WRONG_KEY"},
            ]
            jsonl_path = tmp_dir / "decls.jsonl"
            _write_jsonl(jsonl_path, records)
            args = _make_args(decls_jsonl=jsonl_path)
            with self.assertRaises(SystemExit):
                _run_and_capture(args, dry_run_decls)
        finally:
            import shutil
            shutil.rmtree(tmp_dir, ignore_errors=True)


# ---------------------------------------------------------------------------
# decl_projection source_digest (deterministic, order-independent)
# ---------------------------------------------------------------------------

class DigestTests(unittest.TestCase):
    def test_source_digest_deterministic(self):
        """source_digest is deterministic and order-independent."""
        src = decl_projection.Source(
            deployment_uuid=decl_projection.UUID('00000000-0000-4000-8000-000000000001'),
            arango_database="infogeometry",
        )
        receipt = {"schema": "info_geometry.decl_graph_generation.v1"}
        # Keys must be in strictly increasing UTF-8 order.
        decls = [
            ("key_a", "NameA", "ModA", {"payload": "a"}),
            ("key_b", "NameB", "ModB", {"payload": "b"}),
        ]
        edges = []
        d1 = decl_projection.source_digest(src, receipt, decls, edges)
        # Same content, re-sorted after reversing, must produce same digest.
        d2 = decl_projection.source_digest(
            src, receipt, sorted(list(reversed(decls)), key=lambda r: r[0]), edges
        )
        self.assertEqual(d1, d2)
        self.assertEqual(len(d1), 64)  # SHA-256 hex

    def test_source_digest_rejects_unsorted_keys(self):
        """source_digest raises on non-strictly-increasing keys."""
        src = decl_projection.Source(
            deployment_uuid=decl_projection.UUID('00000000-0000-4000-8000-000000000001'),
            arango_database="infogeometry",
        )
        receipt = {"schema": "info_geometry.decl_graph_generation.v1"}
        decls = [("key_b", "B", "M", {}), ("key_a", "A", "M", {})]  # decreasing order
        with self.assertRaises(ValueError):
            decl_projection.source_digest(src, receipt, decls, [])


# ---------------------------------------------------------------------------
# SQL schema file
# ---------------------------------------------------------------------------

class SchemaTests(unittest.TestCase):
    def test_sql_schema_file_exists(self):
        """tools/infra/sql/001_decl_projection.sql exists and contains key constructs."""
        sql_path = REPO_ROOT / "tools" / "infra" / "sql" / "001_decl_projection.sql"
        self.assertTrue(sql_path.exists())
        text = sql_path.read_text(encoding="utf-8")
        self.assertIn("ig_decl_projection", text)
        self.assertIn("CREATE SCHEMA IF NOT EXISTS ig_decl_projection", text)
        # Immutability via triggers, not constraint trigger names.
        self.assertIn("reject_mutation", text)
        self.assertIn("generation_transition", text)
        self.assertIn("selection_guard", text)


# ---------------------------------------------------------------------------
# ProjectionStore atomic completion (mocked PG connection)
# ---------------------------------------------------------------------------

class ProjectionStoreTests(unittest.TestCase):
    def test_begin_generation_validates_receipt(self):
        """begin_generation rejects malformed receipts."""
        conn = Mock()
        conn.autocommit = False
        store = decl_projection.ProjectionStore(conn)
        source = decl_projection.Source(
            deployment_uuid=decl_projection.UUID('00000000-0000-4000-8000-000000000001'),
            arango_database="infogeometry",
        )
        bad_receipt = {"schema": "unknown", "status": "complete"}
        with self.assertRaises(ValueError):
            store.begin_generation(source, "gen-1", bad_receipt, "a" * 64)


if __name__ == "__main__":
    unittest.main()
