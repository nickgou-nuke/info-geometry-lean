"""Regression coverage for generation-pinned declaration path queries."""

import unittest
from tools.infra.query_unification_path import find_path


class FakeGenerationClient:
    def __init__(self, *, ambiguous_source=False, disconnected=False, source_sentinel=False):
        self.receipt = {
            "schema": "info_geometry.decl_graph_generation.v1",
            "status": "complete",
            "buildFingerprint": "a" * 64,
            "importRoot": "InfoGeometry.All",
            "namespace": "InfoGeometry",
            "declCollection": "decls_g_example",
            "edgeCollection": "edges_g_example",
            "declarationCount": 2,
            "emittedEdgeCount": 1,
            "validEdgeCount": 1,
            "removedOrphanCount": 0,
        }
        self.ambiguous_source = ambiguous_source
        self.disconnected = disconnected
        self.source_sentinel = source_sentinel
        self.calls = []

    def collection_exists(self, name):
        return name in {"decls_g_example", "edges_g_example"}

    def execute_aql(self, query, bind_vars=None, **kwargs):
        self.calls.append((query, bind_vars or {}))
        if "decl_graph_generations" in query:
            return {"result": [self.receipt]}
        if "RETURN LENGTH(@@collection)" in query:
            count = 2 if "decls_g_example" in (bind_vars or {}).get("@collection") else 1
            return {"result": [count]}
        if "DOCUMENT(e._from)" in query:
            return {"result": []}
        if "LET exact" in query:
            needle = (bind_vars or {})["selector"]
            if needle == "source" and self.ambiguous_source:
                matches = [
                    {"id": "decls_g_example/a", "key": "a", "name": "Source.One"},
                    {"id": "decls_g_example/b", "key": "b", "name": "Source.Two"},
                ]
            else:
                name = "Source" if needle == "source" else "Target"
                key = "a" if needle == "source" else "b"
                matches = [{"id": f"decls_g_example/{key}", "key": key, "name": name}]
            return {"result": [matches]}
        if "ANY SHORTEST_PATH" in query:
            if self.disconnected:
                return {"result": []}
            rows = [{
                "declaration": {
                    "id": "decls_g_example/b",
                    "key": "b",
                    "name": "Target",
                    "module": "InfoGeometry.Target",
                },
                "via": {
                    "from": "decls_g_example/a",
                    "to": "decls_g_example/b",
                    "kind": "value",
                },
            }]
            if self.source_sentinel:
                rows.insert(0, {
                    "declaration": {
                        "id": "decls_g_example/a",
                        "key": "a",
                        "name": "Source",
                    },
                    "via": {"from": None, "to": None, "kind": None},
                })
            return {"result": rows}
        raise AssertionError(f"unexpected AQL: {query}")


class QueryUnificationPathTests(unittest.TestCase):
    def test_path_is_generation_pinned_and_preserves_edge_direction_and_kind(self):
        client = FakeGenerationClient()
        result = find_path(client, "example", "source", "target")
        self.assertEqual(result["generation"]["id"], "example")
        self.assertEqual([row["declaration"]["name"] for row in result["path"]],
                         ["Source", "Target"])
        self.assertEqual(result["path"][1]["via"], {
            "from": "decls_g_example/a",
            "to": "decls_g_example/b",
            "kind": "value",
        })
        path_query, path_binds = next(
            (query, binds) for query, binds in client.calls if "ANY SHORTEST_PATH" in query
        )
        self.assertIn("@@edges", path_query)
        self.assertEqual(path_binds["@edges"], "edges_g_example")

    def test_arango_start_vertex_sentinel_is_not_exported_as_an_edge(self):
        result = find_path(
            FakeGenerationClient(source_sentinel=True), "example", "source", "target"
        )
        self.assertEqual(len(result["path"]), 2)
        self.assertIsNone(result["path"][0]["via"])
        self.assertEqual(result["path"][1]["via"]["kind"], "value")

    def test_ambiguous_substring_fails_instead_of_selecting_arbitrary_node(self):
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            find_path(FakeGenerationClient(ambiguous_source=True), "example", "source", "target")

    def test_missing_path_is_explicit_failure(self):
        with self.assertRaisesRegex(ValueError, "no type/value dependency path"):
            find_path(FakeGenerationClient(disconnected=True), "example", "source", "target")

    def test_generation_validation_rejects_bad_receipt_before_node_lookup(self):
        client = FakeGenerationClient()
        client.receipt["validEdgeCount"] = 2
        with self.assertRaisesRegex(ValueError, "count mismatch"):
            find_path(client, "example", "source", "target")
        self.assertFalse(any("LET exact" in query for query, _ in client.calls))


if __name__ == "__main__":
    unittest.main()
