import sys
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
    attrs: list[str] | None = None,
) -> sig.DeclInfo:
    return sig.DeclInfo(
        name=name,
        kind=kind,
        file=file,
        module=None,
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


if __name__ == "__main__":
    unittest.main()
