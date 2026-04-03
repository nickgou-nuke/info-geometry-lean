import json
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import theorem_significance as sig


def _decl(
    name: str,
    *,
    file: str,
    kind: str = "theorem",
    module: str | None = None,
    line: int = 0,
    attrs: list[str] | None = None,
) -> sig.DeclInfo:
    return sig.DeclInfo(
        name=name,
        kind=kind,
        file=file,
        module=module,
        line=line,
        attrs=[] if attrs is None else attrs,
    )


class TheoremSignificanceTests(unittest.TestCase):
    def test_exact_forward_requires_single_value_edge(self):
        decls = {
            "A": _decl(name="A", file="lean/InfoGeometry/Canonical/A.lean"),
            "B": _decl(name="B", file="lean/InfoGeometry/Canonical/B.lean"),
            "helper": _decl(name="helper", file="lean/InfoGeometry/Canonical/H.lean", kind="def"),
        }
        forward = {
            "A": [("B", "value")],
            "C": [("B", "value"), ("helper", "value")],
        }

        exact = sig.build_proof_shape("A", forward, decls)
        mixed = sig.build_proof_shape("C", forward, decls)

        self.assertTrue(exact.is_exact_forward)
        self.assertEqual(exact.exact_forward_target, "B")
        self.assertFalse(mixed.is_exact_forward)
        self.assertIsNone(mixed.exact_forward_target)

    def test_score_all_does_not_mark_mixed_forward_as_wrapper(self):
        decls = {
            "Wrapperish": _decl(
                name="Wrapperish",
                file="lean/InfoGeometry/Canonical/SymmetricLie.lean",
            ),
            "Owner": _decl(name="Owner", file="lean/InfoGeometry/Canonical/Owner.lean"),
            "helper": _decl(
                name="helper",
                file="lean/InfoGeometry/Canonical/Helper.lean",
                kind="def",
            ),
        }
        forward = {"Wrapperish": [("Owner", "value"), ("helper", "value")]}
        reverse = {"Owner": [("Wrapperish", "value")], "helper": [("Wrapperish", "value")]}

        scored = sig.score_all(
            decls,
            forward,
            reverse,
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
        )
        wrapperish = next(s for s in scored if s.name == "Wrapperish")

        self.assertNotIn("wrapper-candidate", wrapperish.tags)
        codes = {code for _, code in wrapperish.violations}
        self.assertNotIn("V1/public-wrapper-inflation", codes)

    def test_bridge_policy_uses_file_stem_not_directory_name(self):
        decls = {
            "A": _decl(name="A", file="lean/InfoGeometry/Canonical/SymmetricLie.lean"),
            "B": _decl(name="B", file="lean/InfoGeometry/Canonical/Owner.lean"),
            "Consumer": _decl(name="Consumer", file="lean/InfoGeometry/Canonical/Consumer.lean"),
        }
        forward = {"A": [("B", "value")]}
        reverse = {
            "A": [("Consumer", "type")],
            "B": [("A", "value")],
        }

        scored = sig.score_all(
            decls,
            forward,
            reverse,
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
        )
        entry = next(s for s in scored if s.name == "A")

        self.assertIn("wrapper-candidate", entry.tags)
        self.assertIn(("warning", "V1/public-wrapper-inflation"), entry.violations)
        self.assertNotIn(("error", "V1/public-wrapper-inflation"), entry.violations)

    def test_explicit_bridge_file_gets_bridge_severity(self):
        decls = {
            "A": _decl(name="A", file="lean/InfoGeometry/Canonical/AttentionBridge.lean"),
            "B": _decl(name="B", file="lean/InfoGeometry/Canonical/Owner.lean"),
            "Consumer": _decl(name="Consumer", file="lean/InfoGeometry/Canonical/Consumer.lean"),
        }
        forward = {"A": [("B", "value")]}
        reverse = {
            "A": [("Consumer", "type")],
            "B": [("A", "value")],
        }

        scored = sig.score_all(
            decls,
            forward,
            reverse,
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
        )
        entry = next(s for s in scored if s.name == "A")

        self.assertIn(("error", "V1/public-wrapper-inflation"), entry.violations)
        self.assertIn(("warning", "V4/bridge-infrastructure-promoted"), entry.violations)

    def test_dead_theorem_in_strict_path_is_error(self):
        decls = {
            "Dead": _decl(name="Dead", file="lean/InfoGeometry/Canonical/Dead.lean"),
        }
        scored = sig.score_all(
            decls,
            {},
            {},
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
        )
        entry = scored[0]

        self.assertIn("dead-candidate", entry.tags)
        self.assertIn(("error", "V2/dead-public-theorem"), entry.violations)

    def test_generated_and_attr_exempt_theorems_do_not_emit_violations(self):
        decls = {
            "Foo.rec": _decl(name="Foo.rec", file="lean/InfoGeometry/Canonical/Foo.lean"),
            "Bar": _decl(
                name="Bar",
                file="lean/InfoGeometry/Canonical/Bar.lean",
                attrs=["terminal"],
            ),
        }
        scored = sig.score_all(
            decls,
            {},
            {},
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
        )

        generated = next(s for s in scored if s.name == "Foo.rec")
        terminal = next(s for s in scored if s.name == "Bar")

        self.assertIn("auto-generated", generated.tags)
        self.assertEqual(generated.violations, [])
        self.assertIn("role-exempt", terminal.tags)
        self.assertEqual(terminal.violations, [])

    def test_structural_metrics_capture_transitive_and_scc_signals(self):
        decls = {
            "A": _decl(name="A", file="lean/InfoGeometry/Canonical/A.lean"),
            "B": _decl(name="B", file="lean/InfoGeometry/Canonical/B.lean"),
            "C": _decl(name="C", file="lean/InfoGeometry/Canonical/C.lean"),
            "T": _decl(name="T", file="lean/InfoGeometry/Canonical/T.lean"),
            "D": _decl(name="D", file="lean/InfoGeometry/Canonical/D.lean"),
            "E": _decl(name="E", file="lean/InfoGeometry/Canonical/E.lean"),
        }

        # C -> B -> A (value), T -> A (type), and a cycle D <-> E.
        forward = {
            "B": [("A", "value")],
            "C": [("B", "value")],
            "T": [("A", "type")],
            "D": [("E", "value")],
            "E": [("D", "value")],
        }
        reverse = {
            "A": [("B", "value"), ("T", "type")],
            "B": [("C", "value")],
            "D": [("E", "value")],
            "E": [("D", "value")],
        }

        scored = sig.score_all(
            decls,
            forward,
            reverse,
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
        )

        a = next(s for s in scored if s.name == "A")
        c = next(s for s in scored if s.name == "C")
        d = next(s for s in scored if s.name == "D")

        self.assertEqual(a.graph.transitive_reverse_reach, 3)  # B, C, T
        self.assertEqual(a.graph.reverse_public_fan_in, 1)     # T
        self.assertEqual(a.graph.reverse_proof_only_reuse, 1)  # B
        self.assertEqual(a.graph.depth, 2)                     # C -> B -> A

        self.assertEqual(c.graph.descendant_mass, 2)           # B, A

        self.assertEqual(d.graph.scc_size, 2)
        self.assertEqual(d.graph.scc_role, "cycle-island")

    def test_vacuity_suspicion_prefers_shallow_exact_wrapper(self):
        decls = {
            "Wrapper": _decl(name="Wrapper", file="lean/InfoGeometry/Canonical/WrapperBridge.lean"),
            "Target": _decl(name="Target", file="lean/InfoGeometry/Canonical/Target.lean"),
            "Rich": _decl(name="Rich", file="lean/InfoGeometry/Canonical/Rich.lean"),
            "Consumer1": _decl(name="Consumer1", file="lean/InfoGeometry/Canonical/C1.lean"),
            "Consumer2": _decl(name="Consumer2", file="lean/InfoGeometry/Canonical/C2.lean"),
            "Consumer3": _decl(name="Consumer3", file="lean/InfoGeometry/Canonical/C3.lean"),
            "Leaf": _decl(name="Leaf", file="lean/InfoGeometry/Canonical/Leaf.lean"),
        }
        forward = {
            "Wrapper": [("Target", "value")],
            "Rich": [("Leaf", "value")],
            "Consumer1": [("Rich", "type")],
            "Consumer2": [("Rich", "type")],
            "Consumer3": [("Rich", "type")],
        }
        reverse = {
            "Target": [("Wrapper", "value")],
            "Rich": [("Consumer1", "type"), ("Consumer2", "type"), ("Consumer3", "type")],
            "Leaf": [("Rich", "value")],
        }

        scored = sig.score_all(
            decls,
            forward,
            reverse,
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
        )

        wrapper = next(s for s in scored if s.name == "Wrapper")
        rich = next(s for s in scored if s.name == "Rich")

        self.assertGreater(wrapper.vacuity_suspicion_score, rich.vacuity_suspicion_score)
        self.assertGreater(wrapper.vacuity_suspicion_confidence, 0.0)
        self.assertTrue(any(f["signal"] == "shape.exact-forward" for f in wrapper.vacuity_suspicion_factors))

    def test_vacuity_suspicion_is_suppressed_for_exemptions(self):
        decls = {
            "Auto.rec": _decl(name="Auto.rec", file="lean/InfoGeometry/Canonical/Auto.lean"),
            "TerminalThm": _decl(
                name="TerminalThm",
                file="lean/InfoGeometry/Canonical/Terminal.lean",
                attrs=["terminal"],
            ),
        }

        scored = sig.score_all(
            decls,
            {},
            {},
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
        )

        auto = next(s for s in scored if s.name == "Auto.rec")
        terminal = next(s for s in scored if s.name == "TerminalThm")

        self.assertLessEqual(auto.vacuity_suspicion_score, 0.1)
        self.assertLessEqual(terminal.vacuity_suspicion_score, 0.1)
        self.assertTrue(any(f["signal"] == "policy.auto-generated-exempt" for f in auto.vacuity_suspicion_factors))
        self.assertTrue(any(f["signal"] == "policy.role-exempt" for f in terminal.vacuity_suspicion_factors))

    def test_bridge_evidence_channel_influences_suspicion_ranking(self):
        decls = {
            "BridgeCand": _decl(name="BridgeCand", file="lean/InfoGeometry/Canonical/BridgeCand.lean"),
            "Target": _decl(name="Target", file="lean/InfoGeometry/Canonical/Target.lean"),
        }
        forward = {"BridgeCand": [("Target", "value")]}
        reverse = {"Target": [("BridgeCand", "value")]}

        baseline = sig.score_all(
            decls,
            forward,
            reverse,
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
        )
        baseline_entry = next(s for s in baseline if s.name == "BridgeCand")

        with_bridge = sig.score_all(
            decls,
            forward,
            reverse,
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
            bridge_evidence_by_file={
                "lean/InfoGeometry/Canonical/BridgeCand.lean": sig.BridgeEvidence(
                    semantic_expr_count=3,
                    fingerprint_match_count=2,
                    provenance_counts=sig.Counter({"leanTag": 2, "bridgeRule": 1}),
                )
            },
        )
        bridge_entry = next(s for s in with_bridge if s.name == "BridgeCand")

        self.assertGreater(bridge_entry.vacuity_suspicion_score, baseline_entry.vacuity_suspicion_score)
        self.assertGreater(bridge_entry.bridge_semantic_evidence_count, 0)
        self.assertGreater(bridge_entry.bridge_fingerprint_match_count, 0)
        self.assertTrue(any(f["signal"] == "bridge.semantic-expr-evidence" for f in bridge_entry.vacuity_suspicion_factors))

    def test_score_all_prefers_declaration_bridge_evidence_over_file_level(self):
        shared_file = "lean/InfoGeometry/Canonical/Shared.lean"
        decls = {
            "A": _decl(name="A", file=shared_file),
            "B": _decl(name="B", file=shared_file),
            "Target": _decl(name="Target", file="lean/InfoGeometry/Canonical/Target.lean"),
        }
        forward = {
            "A": [("Target", "value")],
            "B": [("Target", "value")],
        }
        reverse = {"Target": [("A", "value"), ("B", "value")]}

        scored = sig.score_all(
            decls,
            forward,
            reverse,
            sig.BRIDGE_HINTS_DEFAULT,
            sig.STRICT_PATHS_DEFAULT,
            REPO_ROOT,
            bridge_evidence_by_decl={
                "A": sig.BridgeEvidence(
                    semantic_expr_count=4,
                    fingerprint_match_count=2,
                    provenance_counts=sig.Counter({"leanTag": 2}),
                )
            },
            bridge_evidence_by_file={
                shared_file: sig.BridgeEvidence(
                    semantic_expr_count=1,
                    fingerprint_match_count=1,
                    provenance_counts=sig.Counter({"bridgeRule": 1}),
                )
            },
        )

        a = next(s for s in scored if s.name == "A")
        b = next(s for s in scored if s.name == "B")

        self.assertEqual(a.bridge_semantic_evidence_count, 4)
        self.assertEqual(a.bridge_fingerprint_match_count, 2)
        self.assertEqual(b.bridge_semantic_evidence_count, 1)
        self.assertEqual(b.bridge_fingerprint_match_count, 1)

    def test_bridge_evidence_index_maps_payload_by_declaration_location(self):
        shared_file = "lean/InfoGeometry/Canonical/Shared.lean"
        module = "InfoGeometry.Canonical.Shared"
        source_uri = (REPO_ROOT / shared_file).resolve().as_uri()
        decls = {
            "A": _decl(name="A", file=shared_file, module=module, line=100),
            "B": _decl(name="B", file=shared_file, module=module, line=220),
        }

        payload = {
            "responseMeta": {"sessionId": {"value": source_uri}},
            "request": {
                "file": source_uri,
                "module": module,
                "line": 150,
            },
            "diagnostics": [{"classificationProvenance": "leanTag"}],
            "goals": [
                {
                    "targetExprFingerprint": {
                        "fingerprintSource": "exprSemantic",
                        "fingerprintV1": "shape/v1/head:const:eq",
                    },
                    "locals": [],
                }
            ],
            "theoremTypeExprFingerprint": {
                "fingerprintSource": "exprSemantic",
                "fingerprintV1": "shape/v1/head:const:eq",
            },
        }

        with tempfile.TemporaryDirectory() as tmpdir:
            payload_path = Path(tmpdir) / "bridge-payload.json"
            payload_path.write_text(json.dumps(payload), encoding="utf-8")
            by_decl, by_file = sig.load_bridge_evidence_index([payload_path], REPO_ROOT, decls)

        self.assertIn("A", by_decl)
        self.assertNotIn("B", by_decl)
        self.assertIn(shared_file, by_file)
        self.assertGreater(by_decl["A"].semantic_expr_count, 0)
        self.assertGreater(by_decl["A"].fingerprint_match_count, 0)


if __name__ == "__main__":
    unittest.main()
