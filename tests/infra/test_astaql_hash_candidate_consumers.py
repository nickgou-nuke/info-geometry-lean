from __future__ import annotations

import unittest
from unittest.mock import patch

from tools.infra import audit_conductive_wires_vacuous_nodes as audit
from tools.infra import collapse_mathless_conductive_wires as collapse
from tools.infra.hash_owner_map import _owner_scan_needles


class ASTAQLHashCandidateConsumerTests(unittest.TestCase):
    def test_owner_scan_does_not_alias_colliding_short_names(self) -> None:
        qualified, unambiguous = _owner_scan_needles(
            [
                "InfoGeometry.First.shared",
                "InfoGeometry.Second.shared",
                "InfoGeometry.Unique.owner",
            ]
        )

        self.assertEqual(
            qualified,
            {
                "InfoGeometry.First.shared": "InfoGeometry.First.shared",
                "InfoGeometry.Second.shared": "InfoGeometry.Second.shared",
                "InfoGeometry.Unique.owner": "InfoGeometry.Unique.owner",
            },
        )
        self.assertNotIn("shared", unambiguous)
        self.assertEqual(unambiguous["owner"], "InfoGeometry.Unique.owner")

    def test_collapse_plan_uses_versioned_canonical_value_hash(self) -> None:
        queries: list[str] = []
        responses = iter(
            [
                [
                    {
                        "name": "Candidate.node",
                        "canonicalValueHash": "0",
                        "callers": ["decls/caller"],
                        "targets": ["decls/target"],
                    }
                ],
                [],
            ]
        )

        def fake_run_aql(_target, query: str):
            queries.append(query)
            return next(responses)

        with patch.object(collapse, "run_aql", fake_run_aql):
            report = collapse.scan_and_collapse_conductive_wires(object())

        self.assertIn('algorithmVersion == "lean-expr-structural-v3"', queries[0])
        self.assertEqual(
            report["shortcut_collapse_plan"],
            [
                {
                    "bypassed_mathless_node": "Candidate.node",
                    "direct_source": "decls/caller",
                    "direct_target": "decls/target",
                    "bypassed_canonical_value_hash": "0",
                }
            ],
        )

    def test_conductive_audit_consumes_canonical_value_hash(self) -> None:
        queries: list[str] = []

        def fake_run_aql(_target, query: str):
            queries.append(query)
            return [
                {
                    "name": "Candidate.alias",
                    "kind": "abbrev",
                    "module": "Candidate",
                    "canonicalValueHash": "18446744073709551615",
                    "callerCount": 1,
                    "targetCount": 1,
                    "callers": ["Candidate.consumer"],
                    "targets": ["Candidate.base"],
                }
            ]

        with patch.object(audit, "run_aql", fake_run_aql):
            report = audit.audit_astaql_conductive_wires(object())

        self.assertIn('algorithmVersion == "lean-expr-structural-v3"', queries[0])
        self.assertEqual(
            report["conductiveWires"][0]["canonicalValueHash"],
            "18446744073709551615",
        )


if __name__ == "__main__":
    unittest.main()
