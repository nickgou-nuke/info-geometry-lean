import json
import tempfile
import unittest
from pathlib import Path

from tools.infra.decl_graph_support import load_decl_graph, weak_graph_evidence


class DeclGraphSupportTests(unittest.TestCase):
    def test_load_decl_graph_populates_extended_profile_fields(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "artifacts/dag/index").mkdir(parents=True, exist_ok=True)
            (root / "reports/dag").mkdir(parents=True, exist_ok=True)

            decls = [
                {
                    "name": "InfoGeometry.A",
                    "kind": "theorem",
                    "module": "InfoGeometry",
                    "file": str(root / "lean/InfoGeometry/A.lean"),
                    "line": 10,
                    "attrs": ["rep_layer:L3", "rep_depth_nat:3"],
                },
                {
                    "name": "InfoGeometry.B",
                    "kind": "theorem",
                    "module": "InfoGeometry",
                    "file": str(root / "lean/InfoGeometry/B.lean"),
                    "line": 20,
                    "attrs": [],
                },
                {
                    "name": "InfoGeometry.C",
                    "kind": "def",
                    "module": "InfoGeometry",
                    "file": str(root / "lean/InfoGeometry/C.lean"),
                    "line": 30,
                    "attrs": [],
                },
            ]
            edges = [
                {"src": "InfoGeometry.B", "dst": "InfoGeometry.A", "kind": "value"},
                {"src": "InfoGeometry.C", "dst": "InfoGeometry.A", "kind": "type"},
            ]

            (root / "artifacts/dag/index/decls.jsonl").write_text(
                "\n".join(json.dumps(row) for row in decls) + "\n",
                encoding="utf-8",
            )
            (root / "artifacts/dag/index/edges.jsonl").write_text(
                "\n".join(json.dumps(row) for row in edges) + "\n",
                encoding="utf-8",
            )
            (root / "reports/theorem-significance.json").write_text(
                json.dumps(
                    [
                        {
                            "name": "InfoGeometry.A",
                            "reverse_public_fan_in": 0,
                            "descendant_mass": 2,
                            "transitive_reverse_reach": 3,
                            "depth": 1,
                            "scc_size": 1,
                            "is_sink": True,
                        }
                    ]
                ),
                encoding="utf-8",
            )

            key_map, profiles = load_decl_graph(root)
            a = profiles["InfoGeometry.A"]

            self.assertEqual(key_map[("lean/InfoGeometry/A.lean", 10, "A")], "InfoGeometry.A")
            self.assertEqual(a.reverse_value_users, 1)
            self.assertEqual(a.reverse_type_users, 1)
            self.assertEqual(a.reverse_theorem_users, 1)
            self.assertEqual(a.reverse_public_fan_in, 0)
            self.assertEqual(a.descendant_mass, 2)
            self.assertEqual(a.transitive_reverse_reach, 3)
            self.assertEqual(a.depth, 1)
            self.assertEqual(a.scc_size, 1)
            self.assertTrue(a.is_sink)
            self.assertTrue(a.significance_present)

    def test_weak_graph_evidence_tracks_structural_role(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "artifacts/dag/index").mkdir(parents=True, exist_ok=True)
            (root / "artifacts/dag/index/decls.jsonl").write_text(
                json.dumps(
                    {
                        "name": "InfoGeometry.A",
                        "kind": "theorem",
                        "module": "InfoGeometry",
                        "file": "lean/InfoGeometry/A.lean",
                        "line": 10,
                        "attrs": [],
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            (root / "artifacts/dag/index/edges.jsonl").write_text("", encoding="utf-8")

            _, profiles = load_decl_graph(root)
            self.assertTrue(weak_graph_evidence(profiles["InfoGeometry.A"]))


if __name__ == "__main__":
    unittest.main()
