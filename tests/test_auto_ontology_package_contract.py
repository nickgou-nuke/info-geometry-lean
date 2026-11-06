"""Source-grounded contract and opt-in live tests for `external_refs/auto-ontology`.

Verifies that agent documentation and helper tooling match the real
`NVIDIA/auto-ontology` package in `external_refs/auto-ontology`:
1. The OpenAPI specification (`mcp/auto_ontology_mcp/auto-ontology-api.json`)
   exposes the exact documented REST routes and does NOT expose invented routes
   such as `/api/terms/relationships` or `GET /api/search`.
2. The MCP tool allow-list (`mcp/auto_ontology_mcp/tools.py`) defines the 7
   curated OpenAPI tools (plus `check_readiness` and `ask_question`).
3. Upstream `auto_ontology/dal/schema.py` defines `catalog_database`,
   `catalog_schema`, `catalog_table`, `term`, and `table__term`, and does not
   define `term__term` (which is a repository-local auxiliary table).
4. When `AUTO_ONTOLOGY_LIVE_TEST=1` is set, exercises the live FastAPI (`:3001`)
   and MCP (`:3003`) endpoints and verifies their exact response keys.
"""

from __future__ import annotations

import json
import os
import unittest
import urllib.request
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
AUTO_ONTOLOGY_ROOT = REPO_ROOT / "external_refs" / "auto-ontology"
OPENAPI_SPEC_PATH = (
    AUTO_ONTOLOGY_ROOT / "mcp" / "auto_ontology_mcp" / "auto-ontology-api.json"
)
TOOLS_PY_PATH = AUTO_ONTOLOGY_ROOT / "mcp" / "auto_ontology_mcp" / "tools.py"
SCHEMA_PY_PATH = AUTO_ONTOLOGY_ROOT / "auto_ontology" / "dal" / "schema.py"


class TestAutoOntologyPackageStaticContract(unittest.TestCase):
    """Verify the checked-out `external_refs/auto-ontology` source contract."""

    @classmethod
    def setUpClass(cls) -> None:
        if not OPENAPI_SPEC_PATH.is_file():
            raise unittest.SkipTest(
                f"external_refs/auto-ontology OpenAPI spec not present: {OPENAPI_SPEC_PATH}"
            )
        cls.openapi = json.loads(OPENAPI_SPEC_PATH.read_text(encoding="utf-8"))
        cls.paths = cls.openapi.get("paths", {})

    def test_documented_rest_routes_exist_in_openapi_spec(self) -> None:
        expected_routes = [
            ("get", "/api/health"),
            ("get", "/api/semantic-compilation/status"),
            ("get", "/api/terms"),
            ("get", "/api/terms/{term_id}"),
            ("patch", "/api/terms/{term_id}"),
            ("get", "/api/terms/{term_id}/column-attributes"),
            ("get", "/api/terms/{term_id}/sql-attributes"),
            ("get", "/api/sql-attributes/{attr_id}"),
            ("get", "/api/exploration/graph"),
            ("get", "/api/exploration/semantic-graph"),
            ("get", "/api/exploration/tables/{table_id}/details"),
            ("get", "/api/exploration/terms/{term_id}/details"),
            ("get", "/api/exploration/terms/{term_id}/path/{other_term_id}"),
            ("get", "/api/exploration/nodes/{node_id}/relationships"),
            ("post", "/api/search/global-search"),
            ("post", "/api/search/global-search/count"),
            ("post", "/api/question-entity-coverage"),
            ("post", "/api/chat/completions"),
            ("post", "/api/model/export"),
            ("post", "/api/model/import"),
        ]
        for method, route in expected_routes:
            with self.subTest(method=method, route=route):
                self.assertIn(route, self.paths, f"Missing route {route} in OpenAPI spec")
                self.assertIn(
                    method,
                    self.paths[route],
                    f"Missing method {method.upper()} on route {route}",
                )

    def test_invented_routes_absent_from_openapi_spec(self) -> None:
        """Guard against hallucinated routes in prompts or docs."""
        self.assertNotIn("/api/terms/relationships", self.paths)
        self.assertNotIn("/api/search", self.paths)

    def test_curated_mcp_tools_match_openapi_spec(self) -> None:
        tools_src = TOOLS_PY_PATH.read_text(encoding="utf-8")
        expected_curated = {
            "search_terms": ("GET", "/api/terms"),
            "get_term": ("GET", "/api/terms/{term_id}"),
            "get_term_columns": ("GET", "/api/terms/{term_id}/column-attributes"),
            "get_term_sql_attributes": ("GET", "/api/terms/{term_id}/sql-attributes"),
            "get_sql_attribute": ("GET", "/api/sql-attributes/{attr_id}"),
            "describe_table": ("GET", "/api/exploration/tables/{table_id}/details"),
            "check_answerable": ("POST", "/api/question-entity-coverage"),
        }
        for tool_name, (method, route) in expected_curated.items():
            with self.subTest(tool=tool_name):
                self.assertIn(f'name="{tool_name}"', tools_src)
                self.assertIn(f'path="{route}"', tools_src)
                self.assertIn(method.lower(), self.paths.get(route, {}))

    def test_upstream_schema_tables_vs_auxiliary_term_relationships(self) -> None:
        schema_src = SCHEMA_PY_PATH.read_text(encoding="utf-8")
        for upstream_table in (
            "catalog_database",
            "catalog_schema",
            "catalog_table",
            "catalog_column",
            "term",
            "table__term",
            "column_attribute",
            "column_attribute__term",
            "sql_attribute",
            "sql_attribute__term",
        ):
            self.assertIn(f'"{upstream_table}"', schema_src)
        # Upstream Auto-Ontology computes related_terms via shared table__term,
        # not a term__term table.
        self.assertNotIn('"term__term"', schema_src)


@unittest.skipUnless(
    os.environ.get("AUTO_ONTOLOGY_LIVE_TEST") == "1",
    "Set AUTO_ONTOLOGY_LIVE_TEST=1 to run live Auto-Ontology endpoint checks",
)
class TestAutoOntologyLiveEndpoints(unittest.TestCase):
    """Opt-in live tests against local Auto-Ontology (:3001 REST, :3003 MCP)."""

    BASE_URL = os.environ.get("AUTO_ONTOLOGY_REST_URL", "http://127.0.0.1:3001")
    MCP_URL = os.environ.get("AUTO_ONTOLOGY_MCP_BASE_URL", "http://127.0.0.1:3003")
    SENTINEL_QUERY = "drazin_epistemic_solve_et_coagula_master_synthesis"

    def _get_json(self, url: str) -> tuple[int, dict]:
        with urllib.request.urlopen(url, timeout=15) as resp:
            return resp.status, json.loads(resp.read().decode("utf-8"))

    def _post_json(self, url: str, payload: dict) -> tuple[int, dict]:
        req = urllib.request.Request(
            url,
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=15) as resp:
            return resp.status, json.loads(resp.read().decode("utf-8"))

    def test_live_rest_and_mcp_routes(self) -> None:
        status, health = self._get_json(f"{self.BASE_URL}/api/health")
        self.assertEqual(status, 200)
        self.assertEqual(health.get("status"), "ok")

        status, comp = self._get_json(
            f"{self.BASE_URL}/api/semantic-compilation/status"
        )
        self.assertEqual(status, 200)
        self.assertIn("calculated", comp)

        status, terms_page = self._get_json(
            f"{self.BASE_URL}/api/terms?query={self.SENTINEL_QUERY}&skip=0&limit=5"
        )
        self.assertEqual(status, 200)
        self.assertIn("terms", terms_page)
        self.assertIn("total", terms_page)
        self.assertGreaterEqual(terms_page["total"], 1)
        term = terms_page["terms"][0]
        term_id = term["id"]

        status, term_detail = self._get_json(f"{self.BASE_URL}/api/terms/{term_id}")
        self.assertEqual(status, 200)
        self.assertIn("related_terms", term_detail["data"])

        status, term_exp = self._get_json(
            f"{self.BASE_URL}/api/exploration/terms/{term_id}/details?skip=0&limit=5"
        )
        self.assertEqual(status, 200)
        tables = term_exp["data"].get("tables", [])
        self.assertGreaterEqual(len(tables), 1)
        table_id = tables[0]["id"]

        status, table_exp = self._get_json(
            f"{self.BASE_URL}/api/exploration/tables/{table_id}/details?skip=0&limit=5"
        )
        self.assertEqual(status, 200)
        self.assertIn("terms", table_exp["data"])
        self.assertIn("terms_total", table_exp["data"])

        status, rel_nodes = self._get_json(
            f"{self.BASE_URL}/api/exploration/nodes/{term_id}/relationships?layer=semantic&skip=0&limit=5"
        )
        self.assertEqual(status, 200)
        self.assertIn("nodes", rel_nodes["data"])
        self.assertIn("total", rel_nodes["data"])

        status, gs = self._post_json(
            f"{self.BASE_URL}/api/search/global-search",
            {
                "search_term": "DrazinEpistemicSolveEtCoagula",
                "filters": {"description": True, "synonyms": True},
            },
        )
        self.assertEqual(status, 200)
        self.assertIn("data", gs)
        self.assertGreaterEqual(gs.get("count", 0), 1)

        status, mcp_meta = self._get_json(
            f"{self.MCP_URL}/.well-known/oauth-protected-resource/mcp"
        )
        self.assertEqual(status, 200)
        self.assertEqual(mcp_meta.get("resource_name"), "Auto Ontology")


if __name__ == "__main__":
    unittest.main()
