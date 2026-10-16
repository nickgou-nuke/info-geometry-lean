from __future__ import annotations

import unittest
import json
import subprocess
import tempfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from tools.infra import arango_causal_chiral_cone_prompt as cones
from tools.infra import opengauss_cli
from tools.quality.proof_proxy_staged_gate import checker_index_mismatches


def valid_multi_apex_packet(
    *, backward_depth: int = 6, forward_depth: int = 6, cone_limit: int = 250
) -> dict:
    seed_a = "decls/a"
    seed_b = "decls/b"
    shared = {"_id": "decls/shared", "name": "Shared"}
    backward = [
        {"seed": seed_a, "depth": 1, "component": shared},
        {"seed": seed_b, "depth": 1, "component": shared},
    ]
    forward = [{"seed": seed_a, "depth": 2, "component": {"_id": "decls/user"}}]
    shared_prerequisites = [
        {"node": shared, "seed_count": 2, "seeds": [seed_a, seed_b]}
    ]
    shared_consequences = []
    return {
        "schema": "info_geometry.causal_chiral_cone_prompt.v2",
        "status": "ok",
        "mode": "multi-apex-multi-cone",
        "apices": [
            {"name": "Owner.left", "node": {"_id": seed_a, "name": "Owner.left"}},
            {"name": "Owner.right", "node": {"_id": seed_b, "name": "Owner.right"}},
        ],
        "seeds": [seed_a, seed_b],
        "backward_cone": backward,
        "forward_cone": forward,
        "cone": [
            {**row, "direction": "backward_prerequisite"} for row in backward
        ] + [
            {**row, "direction": "forward_consequence"} for row in forward
        ],
        "shared_prerequisites": shared_prerequisites,
        "common_prerequisites": shared_prerequisites,
        "shared_consequences": shared_consequences,
        "common_consequences": [],
        "shared_nodes": [
            {**row, "direction": "backward_prerequisite"}
            for row in shared_prerequisites
        ],
        "shared_node_count": 1,
        "parameters": {
            "backward_depth": backward_depth,
            "forward_depth": forward_depth,
            "per_apex_direction_result_limit": cone_limit,
            "backward_limit_reached": cone_limit <= 1,
            "forward_limit_reached": cone_limit <= 1,
        },
        "graph_provenance": {"generation_id": "g1", "freshness": "unknown"},
    }


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

    def test_multi_packet_queries_both_directions_and_keeps_intersections_separate(self):
        apices = [
            {"_id": "decls/a", "name": "Owner.a"},
            {"_id": "decls/b", "name": "Owner.b"},
        ]
        shared_prerequisite = {"_id": "decls/common-prereq", "name": "CommonPrereq"}
        shared_consequence = {"_id": "decls/common-user", "name": "CommonUser"}
        calls = []

        def traverse(_target, *, seed_ids, edge_collection, direction, depth, limit):
            calls.append((direction, depth, tuple(seed_ids), edge_collection, limit))
            shared = shared_prerequisite if direction == "OUTBOUND" else shared_consequence
            return [
                {"seed": seed_id, "depth": 1, "component": shared}
                for seed_id in seed_ids
            ]

        args = SimpleNamespace(
            repo_root=Path("/repo"), generation_id=None,
            decls_collection="decls", raw_nodes_collection="raw",
            overlay_nodes_collection="overlay_nodes", overlay_edges_collection="overlay_edges",
            syntax_decls_collection="syntax_decls", edges_collection="edges",
            backward_depth=2, forward_depth=4, cone_limit=10,
            source_radius=0, max_source_excerpts=0,
        )
        with (
            patch.object(cones, "arango_target", return_value=object()),
            patch.object(cones, "resolve_authoritative_decls", return_value=apices),
            patch.object(cones, "traverse_multi_decl_cone", side_effect=traverse),
            patch.object(cones, "add_source_excerpts", return_value=[]),
        ):
            packet = cones.build_multi_packet(args, ["Owner.a", "Owner.b"])

        self.assertEqual(
            [(direction, depth) for direction, depth, *_ in calls],
            [("OUTBOUND", 2), ("INBOUND", 4)],
        )
        self.assertEqual(
            [row["node"] for row in packet["common_prerequisites"]],
            [shared_prerequisite],
        )
        self.assertEqual(
            [row["node"] for row in packet["common_consequences"]],
            [shared_consequence],
        )
        self.assertEqual(packet["graph_provenance"]["freshness"], "unknown")
        self.assertTrue(packet["graph_is_navigation_not_proof"])

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
        packet = valid_multi_apex_packet(
            backward_depth=4, forward_depth=2, cone_limit=30
        )
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
        self.assertTrue(result["graph_is_navigation_not_proof"])
        self.assertEqual(result["graph_provenance"]["freshness"], "unknown")

    def test_discover_dag_context_replaces_forged_orientation_metadata(self):
        packet = valid_multi_apex_packet()
        packet["parameters"].update({
            "edge_orientation": "forged reverse orientation",
            "backward_direction": "forward users",
            "forward_direction": "backward prerequisites",
            "cross_sections_are_bounded_query_results": False,
        })
        packet["orientation"] = {
            "edge_orientation": "forged",
            "backward_cone": "forged",
            "forward_cone": "forged",
            "graph_is_navigation_not_proof": False,
        }
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"], repo_root=Path("/repo")
            )
        self.assertEqual(
            result["parameters"]["edge_orientation"], "declaration -> dependency"
        )
        self.assertEqual(
            result["parameters"]["backward_direction"],
            "OUTBOUND prerequisites/dependencies from each apex",
        )
        self.assertEqual(
            result["parameters"]["forward_direction"],
            "INBOUND users/consequences into each apex",
        )
        self.assertTrue(result["parameters"]["cross_sections_are_bounded_query_results"])
        self.assertTrue(result["orientation"]["graph_is_navigation_not_proof"])
        self.assertTrue(result["graph_is_navigation_not_proof"])

    def test_discover_dag_context_rejects_unknown_cone_seed(self):
        packet = valid_multi_apex_packet()
        packet["backward_cone"][0]["seed"] = "decls/forged"
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"], repo_root=Path("/repo")
            )
        self.assertEqual(result["status"], "invalid_packet")
        self.assertEqual(result["validation_error"], "invalid_backward_cone_row")

    def test_discover_dag_context_recomputes_claimed_cross_sections(self):
        packet = valid_multi_apex_packet()
        packet["common_prerequisites"] = []
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"], repo_root=Path("/repo")
            )
        self.assertEqual(result["status"], "invalid_packet")
        self.assertEqual(
            result["validation_error"], "common_prerequisites_do_not_match_cone"
        )

    def test_discover_dag_context_rejects_apex_label_for_different_node(self):
        packet = valid_multi_apex_packet()
        packet["apices"][0]["node"] = {
            "_id": "decls/other",
            "name": "Owner.impostor",
        }
        packet["seeds"][0] = "decls/other"
        packet["backward_cone"][0]["seed"] = "decls/other"
        packet["cone"][0]["seed"] = "decls/other"
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"], repo_root=Path("/repo")
            )
        self.assertEqual(result["status"], "invalid_packet")
        self.assertEqual(result["validation_error"], "invalid_apex_node_id")

    def test_discover_dag_context_rejects_packet_depths_not_requested(self):
        packet = valid_multi_apex_packet(
            backward_depth=6, forward_depth=6, cone_limit=250
        )
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"],
                repo_root=Path("/repo"),
                backward_depth=1,
                forward_depth=1,
                cone_limit=10,
            )
        self.assertEqual(result["status"], "invalid_packet")
        self.assertEqual(
            result["validation_error"], "requested_cone_parameters_mismatch"
        )

    def test_discover_dag_context_recomputes_limit_reached_flags(self):
        packet = valid_multi_apex_packet(
            backward_depth=6, forward_depth=6, cone_limit=1
        )
        packet["parameters"]["backward_limit_reached"] = False
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"],
                repo_root=Path("/repo"),
                cone_limit=1,
            )
        self.assertEqual(result["status"], "invalid_packet")
        self.assertEqual(
            result["validation_error"], "cone_limit_flags_do_not_match_rows"
        )

    def test_discover_dag_context_rejects_boolean_shared_count(self):
        packet = valid_multi_apex_packet()
        packet["shared_node_count"] = True
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"], repo_root=Path("/repo")
            )
        self.assertEqual(result["status"], "invalid_packet")
        self.assertEqual(result["validation_error"], "shared_node_count_mismatch")

    def test_discover_dag_context_does_not_promote_packet_freshness(self):
        packet = valid_multi_apex_packet()
        packet["graph_provenance"]["freshness"] = "fresh"
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"], repo_root=Path("/repo")
            )
        self.assertEqual(result["graph_provenance"]["freshness"], "unknown")

    def test_failed_requested_dag_context_is_not_reported_as_empty(self):
        completed = SimpleNamespace(returncode=1, stdout="", stderr="Arango unavailable")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.target"], repo_root=Path("/repo")
            )
        self.assertEqual(result["status"], "unavailable")
        self.assertNotIn("empty", result)

    def test_dag_context_rejects_packet_with_wrong_generation(self):
        packet = {
            "schema": "info_geometry.causal_chiral_cone_prompt.v2",
            "status": "ok",
            "mode": "multi-apex-multi-cone",
            "apices": [{"name": "Owner.left"}, {"name": "Owner.right"}],
            "graph_provenance": {"generation_id": "other-generation"},
        }
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"],
                repo_root=Path("/repo"),
                generation_id="requested-generation",
            )
        self.assertEqual(result["status"], "invalid_packet")
        self.assertEqual(result["validation_error"], "requested_generation_mismatch")

    def test_dag_context_rejects_mismatched_apices(self):
        packet = {
            "schema": "info_geometry.causal_chiral_cone_prompt.v2",
            "status": "ok",
            "mode": "multi-apex-multi-cone",
            "apices": [{"name": "Owner.other"}, {"name": "Owner.right"}],
            "graph_provenance": {"generation_id": None},
        }
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"], repo_root=Path("/repo")
            )
        self.assertEqual(result["status"], "invalid_packet")
        self.assertEqual(result["validation_error"], "requested_apices_mismatch")

    def test_dag_context_rejects_duplicate_apices(self):
        with self.assertRaisesRegex(ValueError, "duplicate exact declaration apices"):
            opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.left"], repo_root=Path("/repo")
            )

    def test_local_preflight_is_navigation_only_and_marks_freshness_unknown(self):
        packet = {
            "ok": True,
            "target": "local",
            "output": {
                "schema": "info_geometry.local_dag_attention.v1",
                "query": "group inverse",
                "artifacts": {"dag": {}},
                "local_search": [],
            },
        }
        completed = SimpleNamespace(returncode=0, stdout=json.dumps(packet), stderr="")
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed) as run:
            result = opengauss_cli.discover_local_dag_context(
                "group inverse", repo_root=Path("/repo"), depth=2, limit=5
            )
        command = run.call_args.args[0]
        self.assertIn("local-preflight", command)
        self.assertEqual(result["status"], "ok")
        self.assertEqual(result["authority"], "navigation_only")
        self.assertFalse(result["graph_is_proof_authority"])
        self.assertEqual(result["freshness"], "unknown")

    def test_local_preflight_rejects_wrong_schema(self):
        completed = SimpleNamespace(
            returncode=0,
            stdout=json.dumps({
                "ok": True,
                "target": "local",
                "output": {"schema": "wrong", "artifacts": {}, "local_search": []},
            }),
            stderr="",
        )
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_local_dag_context(
                "group inverse", repo_root=Path("/repo")
            )
        self.assertEqual(result["status"], "invalid_packet")
        self.assertEqual(result["validation_error"], "unexpected_schema")

    def test_dag_context_rejects_wrong_packet_mode_or_status(self):
        for field, value, expected_error in (
            ("mode", "unexpected-mode", "unexpected_mode"),
            ("status", "error", "unexpected_status"),
        ):
            packet = {
                "schema": "info_geometry.causal_chiral_cone_prompt.v2",
                "status": "ok",
                "mode": "multi-apex-multi-cone",
                "apices": [{"name": "Owner.left"}, {"name": "Owner.right"}],
                "graph_provenance": {"generation_id": None},
            }
            packet[field] = value
            completed = SimpleNamespace(
                returncode=0, stdout=json.dumps(packet), stderr=""
            )
            with patch.object(
                opengauss_cli.subprocess, "run", return_value=completed
            ):
                result = opengauss_cli.discover_dag_context(
                    ["Owner.left", "Owner.right"], repo_root=Path("/repo")
                )
            self.assertEqual(result["status"], "invalid_packet")
            self.assertEqual(result["validation_error"], expected_error)

    def test_unindexed_multi_apex_diagnostic_is_preserved(self):
        packet = {
            "schema": "info_geometry.causal_chiral_cone_prompt.v2",
            "mode": "multi-apex-resolution-diagnostic",
            "status": "unindexed",
            "requested_names": ["Owner.left", "Owner.right"],
            "graph_provenance": {"generation_id": None},
        }
        completed = SimpleNamespace(
            returncode=0, stdout=json.dumps(packet), stderr=""
        )
        with patch.object(opengauss_cli.subprocess, "run", return_value=completed):
            result = opengauss_cli.discover_dag_context(
                ["Owner.left", "Owner.right"], repo_root=Path("/repo")
            )
        self.assertEqual(result["status"], "unindexed")
        self.assertEqual(result["mode"], "multi-apex-resolution-diagnostic")
        self.assertEqual(result["authority"], "navigation_only")

    def test_hook_checker_snapshot_mismatch_is_detected(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)

            def git(*args):
                return subprocess.run(
                    ["git", *args], cwd=root, check=True,
                    capture_output=True, text=True,
                ).stdout

            git("init", "-q")
            git("config", "user.email", "hook-test@example.invalid")
            git("config", "user.name", "Hook Test")
            gate = root / "tools/quality/proof_proxy_staged_gate.py"
            screener = root / "tools/infra/opengauss_screener.py"
            gate.parent.mkdir(parents=True)
            screener.parent.mkdir(parents=True)
            gate.write_text("checker version 1\n")
            screener.write_text("screener version 1\n")
            git("add", "tools")
            git("commit", "-qm", "baseline gate")

            gate.write_text("checker staged version\n")
            git("add", "tools/quality/proof_proxy_staged_gate.py")
            gate.write_text("checker unstaged version\n")
            self.assertEqual(
                checker_index_mismatches(root),
                ["tools/quality/proof_proxy_staged_gate.py"],
            )

            git("add", "tools/quality/proof_proxy_staged_gate.py")
            self.assertEqual(checker_index_mismatches(root), [])


if __name__ == "__main__":
    unittest.main()
