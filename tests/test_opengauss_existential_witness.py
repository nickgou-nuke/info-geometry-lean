"""Bounded T16 parser regressions, separate from Lean kernel verification.

Synthetic Lean strings test classification only. The integration fixture is
read from the same checkout and is proved in the focused Lean build.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import unittest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCREENER_PATH = REPO_ROOT / "tools/infra/opengauss_screener.py"
spec = importlib.util.spec_from_file_location("existential_witness_screener", SCREENER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"Cannot load screener at {SCREENER_PATH}")
screener = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = screener
spec.loader.exec_module(screener)


class ExistentialMatrixWitnessTests(unittest.TestCase):
    matrix = "Matrix (Fin 2) (Fin 2) ℝ"
    carrier = {("2", "2", "ℝ")}
    result = "∃ X Y : Matrix (Fin 2) (Fin 2) ℝ, X * Y ≠ Y * X"

    def closed(self, result, *, prefix="", binders="", proof="by exact checkedPair",
               required_carriers=None):
        source = prefix + f"\ntheorem witness {binders} : {result} := {proof}\n"
        return screener._has_closed_noncommutativity_witness(
            source, required_carriers=required_carriers,
        )

    def matched(self, result, *, prefix="", carrier=None):
        return screener._witness_matches_matrix_carriers(
            prefix, "theorem witness", result,
            self.carrier if carrier is None else carrier,
        )

    def test_typeclass_numeric_ascription_is_not_a_term_premise(self):
        for binder in [
            "[Invertible (2 : K)]",
            "[h : Invertible (2 : K)]",
            "[Invertible ((2 : K) * (2 : K))]",
        ]:
            with self.subTest(binder=binder):
                self.assertTrue(screener._witness_has_only_typeclass_binders(
                    f"theorem witness {{K : Type}} [Ring K] {binder} (n : ℕ)"
                ))

    def test_forbidden_classes_and_ordinary_premises_remain_rejected(self):
        for binder in [
            "[IsEmpty (Fin 2)]", "[Subsingleton K]", "[False]",
            "[Nonempty (Matrix (Fin 2) (Fin 2) K)]",
            "[Inhabited (Matrix (Fin 2) (Fin 2) K)]",
            "[Fact (X * Y ≠ Y * X)]", "[Wrapper [False]]",
            "(h : False)", "(h : X * Y ≠ Y * X)", "(x : K)",
        ]:
            with self.subTest(binder=binder):
                self.assertFalse(screener._witness_has_only_typeclass_binders(
                    f"theorem witness {{K : Type}} [Ring K] [Invertible (2 : K)] {binder}"
                ))

    def test_malformed_binder_boundaries_fail_closed(self):
        for binder in [
            "[Invertible (2 : K)", "[Invertible (2 : K]) ]",
            "[Invertible (2 : K)] )", "[Invertible (2 : K))]",
        ]:
            with self.subTest(binder=binder):
                self.assertFalse(screener._witness_has_only_typeclass_binders(
                    "theorem witness {K : Type} " + binder
                ))

    def test_supplied_target_class_checks_run_before_class_masking(self):
        source = "class Provider (n : Nat) where\n  value : Target\n"
        self.assertFalse(screener._witness_has_only_typeclass_binders(
            "theorem witness [hp : Provider (2 : Nat)]",
            target_type_name="Target", source=source,
        ))

    def test_native_existential_accepts_only_its_own_exact_carrier(self):
        for result in [self.result, self.result + " ∧ X ≠ 0 ∧ Y ≠ 0"]:
            with self.subTest(result=result):
                self.assertTrue(self.matched(result))
                self.assertTrue(self.closed(result))
                self.assertTrue(self.closed(result, required_carriers=self.carrier))
        for carrier in [{("3", "3", "ℝ")}, {("2", "2", "ℂ")},
                        {("2", "2", "ZMod 2")}, set()]:
            with self.subTest(carrier=carrier):
                self.assertFalse(self.matched(self.result, carrier=carrier))
        self.assertTrue(self.matched(
            "∃ a b : Matrix (Fin 2) (Fin 2) (Stage K n), a * b ≠ b * a",
            carrier={("2", "2", "Stage K n")},
        ))

    def test_existential_does_not_infer_unjustified_scalar_specializations(self):
        result = "∃ X Y : Matrix (Fin 2) (Fin 2) R, X * Y ≠ Y * X"
        self.assertFalse(screener._witness_matches_matrix_carriers(
            "", "theorem witness {R : Type} [Ring R] [Nontrivial R] [Invertible (2 : R)]",
            result, self.carrier,
        ))

    def test_weaker_logical_forms_fail_with_or_without_requested_carrier(self):
        bodies = [
            "X * Y ≠ Y * X ∨ True", "True ∨ X * Y ≠ Y * X",
            "X * Y ≠ Y * X → True", "True → X * Y ≠ Y * X",
            "X * Y ≠ Y * X ∧ True → True",
            "X * Y ≠ Y * X ∧ (True → True)",
            "X * Y ≠ Y * X ∧ (True ∨ False)",
            "¬ (X * Y ≠ Y * X)", "(X * Y ≠ Y * X) ∨ True",
            "True ∧ X * Y ≠ Y * X", "X * Y ≠ Y * X ∧",
            "X * Y != Y * X",
        ]
        results = [f"∃ X Y : {self.matrix}, {body}" for body in bodies]
        results.extend(["True → " + self.result, "True ∨ (" + self.result + ")",
                        "¬ (" + self.result + ")"])
        for result in results:
            with self.subTest(result=result):
                self.assertFalse(self.matched(result))
                self.assertFalse(self.closed(result))
                self.assertFalse(self.closed(result, required_carriers=self.carrier))

    def test_embedded_existentials_cannot_fall_back_to_global_carriers(self):
        prefix = f"def X : {self.matrix} := 0\ndef Y : {self.matrix} := 0\n"
        for result in ["True → " + self.result, "True ∨ " + self.result,
                       "True ∨ (" + self.result + ")"]:
            with self.subTest(result=result):
                self.assertFalse(self.matched(result, prefix=prefix))
                self.assertFalse(self.closed(result, prefix=prefix))
                self.assertFalse(self.closed(result, prefix=prefix,
                                             required_carriers=self.carrier))

    def test_matrix_occurrence_inside_another_binder_type_is_not_a_carrier(self):
        for bound_type in [self.matrix + " → ℝ", self.matrix + " × ℝ",
                           "List (" + self.matrix + ")", "ℝ", "Mat2"]:
            result = f"∃ X Y : {bound_type}, X * Y ≠ Y * X"
            with self.subTest(bound_type=bound_type):
                self.assertFalse(self.matched(result))
                self.assertFalse(self.closed(result))

    def test_bound_names_cannot_borrow_global_carriers_or_ascriptions(self):
        prefix = f"def X : {self.matrix} := 0\ndef Y : {self.matrix} := 0\n"
        for result in [
            "∃ X Y : ℝ, X * Y ≠ Y * X",
            "∃ X Y : Matrix (Fin 3) (Fin 3) ℝ, X * Y ≠ Y * X",
            f"∃ X Y : {self.matrix} → ℝ, X * Y ≠ Y * X",
            f"∃ X Y : {self.matrix}, (X : Quaternion ℝ) * Y ≠ Y * X",
            f"∃ X X : {self.matrix}, X * X ≠ X * X",
            f"∃ a b : {self.matrix}, X * Y ≠ Y * X",
            f"∃ X Y : {self.matrix}, X * Y ≠ X * Y",
        ]:
            with self.subTest(result=result):
                self.assertFalse(self.matched(result, prefix=prefix))
                self.assertFalse(self.closed(result, prefix=prefix,
                                             required_carriers=self.carrier))

    def test_witness_and_false_assumptions_remain_rejected(self):
        for binders, prefix, proof in [
            (f"(h : {self.result})", "", "h"),
            ("(h : False)", "", "False.elim h"),
            ("", f"variable (h : {self.result})\n", "h"),
            (f"[h : Fact ({self.result})]", "", "h.out"),
        ]:
            with self.subTest(binders=binders, prefix=prefix):
                self.assertFalse(self.closed(self.result, binders=binders,
                                             prefix=prefix, proof=proof))

    def test_nested_class_arguments_do_not_hide_a_supplied_witness(self):
        provider = f"class Provider (n : Nat) where\n  witness : {self.result}\n"
        for binder, proof in [
            ("[Provider (2 : Nat)]", "Provider.witness"),
            ("[hp : Provider (2 : Nat)]", "hp.witness"),
        ]:
            for ambient in [False, True]:
                with self.subTest(binder=binder, ambient=ambient):
                    prefix = provider + (f"variable {binder}\n" if ambient else "")
                    self.assertFalse(self.closed(
                        self.result, prefix=prefix, binders="" if ambient else binder,
                        proof=proof, required_carriers=self.carrier,
                    ))

    def test_axioms_holes_opaque_forwarding_and_unsafe_declarations_stay_rejected(self):
        for prefix, proof in [
            (f"axiom supplied : {self.result}\n", "supplied"),
            (f"@[simp] axiom supplied : {self.result}\n", "supplied"),
            (f"opaque supplied : {self.result}\n", "supplied"),
            (f"def supplied : {self.result} := by sorry\n", "supplied"),
            ("", "by sorry"), ("", "by admit"),
        ]:
            with self.subTest(prefix=prefix, proof=proof):
                self.assertFalse(self.closed(self.result, prefix=prefix, proof=proof))
        for modifier in ["unsafe", "partial"]:
            source = f"{modifier} theorem witness : {self.result} := by exact checkedPair\n"
            self.assertFalse(screener._has_closed_noncommutativity_witness(
                source, required_carriers=self.carrier,
            ))

    def test_native_syntax_shadowing_cannot_certify_the_existential(self):
        for prefix in [
            "def Matrix := ℝ\n", "def Fin := ℕ\n", "def Exists := True\n",
            'local notation "X" => (0 : ℝ)\n',
            'local infix:70 " * " => Nat.add\n',
        ]:
            with self.subTest(prefix=prefix):
                self.assertFalse(self.matched(self.result, prefix=prefix))

    def test_checked_normalized_trace_owner_supplies_its_shell_witness(self):
        owner = (REPO_ROOT / "lean/InfoGeometry/Canonical/DyadicMatrixTraceColimit.lean").read_text()
        self.assertTrue(screener._has_closed_noncommutativity_witness(
            owner, exported_only=True, required_carriers={("2", "2", "Stage K n")},
        ))


if __name__ == "__main__":
    unittest.main()
