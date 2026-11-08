"""Offline unit tests for darwin_phylogeny_dashboard.py (repo-phylogeny/v2, labels, edges & tooltip)."""
from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest

from tools.infra import darwin_phylogeny_dashboard as dashboard
from tools.infra.evolution_taxonomy import iter_labels


class DarwinPhylogenyDashboardTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.sha_root = "1" * 40
        self.sha_leaf = "2" * 40
        self.phylogeny_path = self.root / "phylogeny.json"
        self.phylogeny_payload = {
            "schema": "repo-phylogeny/v2",
            "repository": "https://github.com/example/fixture",
            "commits": [
                {
                    "sha": self.sha_root,
                    "parents": [],
                    "tree_hash": "a" * 40,
                    "author_time": 1769990400,
                    "committer_time": 1769990400,
                    "time": 1769990400,
                    "subject": "Initial formal owner",
                },
                {
                    "sha": self.sha_leaf,
                    "parents": [self.sha_root],
                    "tree_hash": "b" * 40,
                    "author_time": 1770076800,
                    "committer_time": 1770076800,
                    "time": 1770076800,
                    "subject": "Fix and refactor taxonomy bridge",
                },
            ],
            "declaration_links": {
                "carrier": "CommitDeclEdge",
                "edge_kind": "touches",
                "non_transitive_cohabitation_note": "InfoGeometry.Graph.shared_path_not_equivalence",
                "by_commit": {
                    self.sha_leaf: {
                        "exact_count": 1,
                        "cohabitation_count": 1,
                        "edges": [
                            {
                                "declKey": "d_1",
                                "declName": "InfoGeometry.Graph.ChangeCategory",
                                "path": "lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean",
                                "edgeKind": "touches",
                                "resolution": "exact_declaration",
                                "exact_match": True,
                                "candidateFingerprints": {"canonicalTypeHash": "999"},
                            },
                            {
                                "declKey": "d_2",
                                "declName": "InfoGeometry.Graph.shared_path_not_equivalence",
                                "path": "lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean",
                                "edgeKind": "touches",
                                "resolution": "habitat_cohabitation",
                                "exact_match": False,
                            },
                        ],
                    }
                },
            },
        }
        self.phylogeny_path.write_text(json.dumps(self.phylogeny_payload), encoding="utf-8")

    def test_consumes_phylogeny_v2_without_labels_or_edges(self) -> None:
        bare_path = self.root / "bare_phylogeny.json"
        bare_payload = dict(self.phylogeny_payload)
        bare_payload.pop("declaration_links", None)
        bare_path.write_text(json.dumps(bare_payload), encoding="utf-8")

        out_html = self.root / "out_bare.html"
        rc = dashboard.main([
            "--phylogeny-json", str(bare_path),
            "--out", str(out_html),
        ])
        self.assertEqual(rc, 0)
        html = out_html.read_text(encoding="utf-8")
        self.assertIn("Commit archetypes", html)
        self.assertIn("habitat cohabitation (non-transitive):", html)
        self.assertIn(self.sha_leaf[:10], html)

    def test_renders_labels_archetypes_and_exact_vs_cohabitation_counts(self) -> None:
        labels_path = self.root / "labels.jsonl"
        label_rows = list(iter_labels([
            {
                "type": "commit",
                "sha": self.sha_root,
                "subject": "Initial formal owner",
                "body": "",
                "paths": ["lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean"],
            },
            {
                "type": "commit",
                "sha": self.sha_leaf,
                "subject": "Fix and refactor taxonomy bridge",
                "body": "",
                "paths": ["tests/test_evolution_taxonomy.py"],
            },
        ]))
        labels_path.write_text(
            "\n".join(json.dumps(r) for r in label_rows) + "\n",
            encoding="utf-8",
        )

        out_html = self.root / "out_full.html"
        rc = dashboard.main([
            "--phylogeny-json", str(self.phylogeny_path),
            "--labels", str(labels_path),
            "--out", str(out_html),
        ])
        self.assertEqual(rc, 0)
        html = out_html.read_text(encoding="utf-8")
        self.assertIn('"Bug Fix"', html)
        self.assertIn('"Refactor/Restructure"', html)
        self.assertIn('"Test Evolution"', html)
        self.assertIn('"exact":1,"cohabitation":1', html)
        self.assertIn("Labels: ${lbls}", html)
        self.assertIn("exact: ${n.exact} · habitat cohabitation (non-transitive): ${n.cohabitation}", html)


if __name__ == "__main__":
    unittest.main()
