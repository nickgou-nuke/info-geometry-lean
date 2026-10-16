from __future__ import annotations

import unittest
import json
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from tools.infra import arango_causal_chiral_cone_prompt as cones
from tools.infra import opengauss_cli


class DirectionalConeCrossSectionTests(unittest.TestCase):
    def test_separates_shared_from_common_nodes(self):
        apex_a = {"_id": "decls/a", "name": "A"}
        apex_b = {"_id": "decls/b", "name": "B"}
        shared = {"_id": "decls/shared", "name": "Shared"}
        partial = {"_id": "decls/partial", "name": "Partial"}
        rows = [
            {"seed": "decls/a", "component": shared},
            {"seed": "decls/b", "component": shared},
            {"seed": "decls/a", "component": partial},
        ]

        nodes, cross_section, common = cones.directional_cross_section(
            [apex_a, apex_b], ["decls/a", "decls/b"], rows
        )

        self.assertEqual(nodes["decls/shared"], shared)
        self.assertEqual(
            {row["node"]["_id"] for row in cross_section}, {"decls/shared"}
        )
        self.assertEqual([row["node"]["_id"] for row in common], ["decls/shared"])

    def test_cross_sections_are_kept_separate_by_direction(self):
        apexes = [{"_id": "decls/a"}, {"_id": "decls/b"}]
        seeds = ["decls/a", "decls/b"]
        prerequisite = {"_id": "decls/p"}
        consequence = {"_id": "decls/c"}

        _, backward_shared, _ = cones.directional_cross_section(
            apexes,
            seeds,
            [
                {"seed": "decls/a", "component": prerequisite},
                {"seed": "decls/b", "component": prerequisite},
            ],
        )
        _, forward_shared, _ = cones.directional_cross_section(
            apexes,
            seeds,
            [
                {"seed": "decls/a", "component": consequence},
                {"seed": "decls/b", "component": consequence},
            ],
        )

        self.assertEqual([row["node"]["_id"] for row in backward_shared], ["decls/p"])
        self.assertEqual([row["node"]["_id"] for row in forward_shared], ["decls/c"])

    def test_multi_cone_query_uses_requested_direction_and_preserves_seed(self):
        captured = {}

        def fake_run_aql(target, query, bind_vars):
            captured["query"] = query
            captured["bind_vars"] = bind_vars
            return []

        original = cones.run_aql
        cones.run_aql = fake_run_aql
        try:
            result = cones.traverse_multi_decl_cone(
                object(),
                seed_ids=["decls/a", "decls/b"],
                edge_collection="edges",
                direction="OUTBOUND",
                depth=3,
                limit=20,
            )
        finally:
            cones.run_aql = original

        self.assertEqual(result, [])
        self.assertIn("OUTBOUND seed", captured["query"])
        self.assertIn("FOR seed IN @seeds", captured["query"])
        self.assertIn("seed: seed", captured["query"])
        self.assertEqual(
            captured["bind_vars"],
            {
                "@edges": "edges",
                "seeds": ["decls/a", "decls/b"],
                "depth": 3,
                "limit": 20,
            },
        )

    def test_invalid_direction_rejected_before_database_call(self):
        def unexpected_run_aql(*_args, **_kwargs):
            raise AssertionError("invalid direction must be rejected before querying Arango")

        original = cones.run_aql
        cones.run_aql = unexpected_run_aql
        try:
            with self.assertRaisesRegex(ValueError, "invalid traversal direction"):
                cones.traverse_multi_decl_cone(
                    object(),
                    seed_ids=["decls/a"],
                    edge_collection="edges",
                    direction="ANY",
                    depth=1,
                    limit=10,
                )
        finally:
            cones.run_aql = original

    def test_discover_dag_context_requests_exact_multi_apexes(self):
        packet = {
            "status": "ok",
            "graph_provenance": {"generation_id": "g1", "freshness": "unknown"},
        }
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed) as run:
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"],
                repo_root=Path("/repo"),
                generation_id="g1",
                backward_depth=4,
                forward_depth=2,
                cone_limit=30,
            )

        command = run.call_args.args[0]
        self.assertIn("--decl-multi", command)
        self.assertIn("Owner.left,Owner.right", command)
        self.assertIn("--backward-depth", command)
        self.assertEqual(result["authority"], "navigation_only")
        self.assertFalse(result["graph_is_proof_authority"])
        self.assertEqual(result["graph_provenance"]["freshness"], "unknown")

    def test_failed_requested_dag_context_is_not_reported_as_empty(self):
        completed = SimpleNamespace(returncode=1, stdout="", stderr="Arango unavailable")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.target"], repo_root=Path("/repo")
            )
        self.assertEqual(result["status"], "unavailable")
        self.assertNotIn("empty", result)


if __name__ == "__main__":
    unittest.main()
