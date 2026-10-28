"""Focused source-screen regressions for native matrix noncommutativity.

The positive integration cases read existing Lean owner files. Synthetic Lean
snippets below are lexical screener inputs, including deliberately invalid or
unproved negative cases; they are not claimed as kernel-checked mathematics.

The standard library is sufficient. Integration fixtures are read from this
checkout so the tests and reviewed source have the same repository binding.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import unittest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCREENER_PATH = REPO_ROOT / "tools/infra/opengauss_screener.py"
spec = importlib.util.spec_from_file_location("native_matrix_witness_screener", SCREENER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"Cannot load screener at {SCREENER_PATH}")
screener = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = screener
spec.loader.exec_module(screener)


class NativeMatrixWitnessTests(unittest.TestCase):
    carrier = {("3", "3", "ℂ")}

    @classmethod
    def setUpClass(cls):
        cls.owner_path = (
            REPO_ROOT / "lean/InfoGeometry/OperatorAlgebra/OperatorExtensionExamples.lean"
        )
        cls.owner = cls.owner_path.read_text(encoding="utf-8")
        cls.before_witness = cls.owner.split("theorem P_Q_not_commute", 1)[0]
        cls.through_witness = cls.owner.split("theorem oddPart_P_Q", 1)[0]

    def closed(self, source, *, carrier=None, exported_only=True):
        return screener._has_closed_noncommutativity_witness(
            source,
            required_carriers=self.carrier if carrier is None else carrier,
            exported_only=exported_only,
        )

    def missing_witness(self, source):
        return [
            violation for violation in screener.screen_lean_content(
                source, filename="NativeMatrixConsumer.lean", import_root=REPO_ROOT
            )
            if violation.trap_id == "T16" and "Witness" in violation.trap_name
        ]

    def test_existing_checked_owner_provides_native_witness(self):
        self.assertTrue(self.closed(self.owner))

    def test_same_file_screen_retains_notation_metadata(self):
        self.assertEqual(self.missing_witness(self.owner), [])

    def test_direct_import_uses_existing_checked_owner(self):
        consumer = """
import InfoGeometry.OperatorAlgebra.OperatorExtensionExamples
def operatorProduct (A B : Matrix (Fin 3) (Fin 3) ℂ) := A * B
"""
        self.assertEqual(self.missing_witness(consumer), [])

    def test_existing_witness_does_not_certify_unrelated_carriers(self):
        for target in [
            ("2", "2", "ℂ"), ("4", "4", "ℂ"), ("3", "2", "ℂ"),
            ("3", "3", "ℝ"), ("3", "3", "ℚ"), ("3", "3", "ZMod 2"),
        ]:
            with self.subTest(target=target):
                self.assertFalse(self.closed(self.owner, carrier={target}))

    def test_imported_witness_does_not_certify_wrong_dimension_or_scalar(self):
        for dimension, scalar in [(2, "ℂ"), (3, "ℝ"), (3, "ZMod 2")]:
            with self.subTest(dimension=dimension, scalar=scalar):
                consumer = (
                    "import InfoGeometry.OperatorAlgebra.OperatorExtensionExamples\n"
                    f"def operatorProduct (A B : Matrix (Fin {dimension}) "
                    f"(Fin {dimension}) ({scalar})) := A * B\n"
                )
                self.assertTrue(self.missing_witness(consumer))

    def test_imported_witness_must_cover_each_used_matrix_carrier(self):
        consumer = """
import InfoGeometry.OperatorAlgebra.OperatorExtensionExamples
def product3 (A B : Matrix (Fin 3) (Fin 3) ℂ) := A * B
def product2 (A B : Matrix (Fin 2) (Fin 2) ℂ) := A * B
"""
        self.assertTrue(self.missing_witness(consumer))

    def test_native_predicate_requires_equal_operand_carriers(self):
        source = """
def P : Matrix (Fin 3) (Fin 3) ℂ := 0
def Q : Matrix (Fin 2) (Fin 2) ℂ := 0
"""
        self.assertFalse(screener._witness_matches_matrix_carriers(
            source, "theorem witness", "¬ Commute P Q",
            {("3", "3", "ℂ"), ("2", "2", "ℂ")},
        ))

    def test_native_predicate_must_be_the_entire_result(self):
        for result in [
            "¬ Commute P Q ∨ True", "True ∨ ¬ Commute P Q",
            "(¬ Commute P Q) → True", "True → ¬ Commute P Q",
            "¬ Commute P Q ∧ True", "¬ Commute P P", "¬ Commute P missing",
        ]:
            with self.subTest(result=result):
                self.assertFalse(screener._witness_matches_matrix_carriers(
                    self.before_witness, "theorem witness", result, self.carrier
                ))

    def test_native_witness_cannot_be_an_assumption(self):
        for declaration in [
            "theorem fake (h : ¬ Commute P Q) : ¬ Commute P Q := h\n",
            "variable (h : ¬ Commute P Q)\n"
            "theorem fake : ¬ Commute P Q := h\n",
            "theorem fake (h : False) : ¬ Commute P Q := False.elim h\n",
            "theorem fake [h : Fact (¬ Commute P Q)] : ¬ Commute P Q := h.out\n",
        ]:
            with self.subTest(declaration=declaration):
                self.assertFalse(self.closed(self.before_witness + declaration))

    def test_axiom_or_axiom_forwarding_is_not_a_closed_witness(self):
        for declaration in [
            "axiom fake : ¬ Commute P Q\n",
            "axiom supplied : ¬ Commute P Q\n"
            "theorem fake : ¬ Commute P Q := supplied\n",
            "opaque supplied : ¬ Commute P Q\n"
            "theorem fake : ¬ Commute P Q := supplied\n",
        ]:
            with self.subTest(declaration=declaration):
                self.assertFalse(self.closed(self.before_witness + declaration))

    def test_holes_and_hole_forwarding_are_not_closed_witnesses(self):
        for declaration in [
            "theorem fake : ¬ Commute P Q := by sorry\n",
            "theorem fake : ¬ Commute P Q := by admit\n",
            "theorem supplied : ¬ Commute P Q := by sorry\n"
            "theorem fake : ¬ Commute P Q := supplied\n",
        ]:
            with self.subTest(declaration=declaration):
                self.assertFalse(self.closed(self.before_witness + declaration))

    def test_private_native_witness_is_not_exported(self):
        private_owner = self.through_witness.replace(
            "theorem P_Q_not_commute", "private theorem P_Q_not_commute", 1
        )
        self.assertFalse(self.closed(private_owner))

    def test_witness_syntax_inside_comments_or_strings_is_ignored(self):
        escaped = self.through_witness.replace("\\", "\\\\").replace('"', '\\"')
        for source in [
            "/- " + self.through_witness + " -/\n",
            'def payload : String := "' + escaped + '"\n',
        ]:
            with self.subTest(source=source[:50]):
                self.assertFalse(self.closed(source))

    def test_notation_names_cannot_come_from_comments_or_strings(self):
        declarations = "\ndef P : Mat := 0\ndef Q : Mat := 0\n"
        for fake_notation in [
            '/- local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ -/\n',
            '-- local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ\n',
            'def payload : String := "local notation \\"Mat\\" => '
            'Matrix (Fin 3) (Fin 3) ℂ"\n',
        ]:
            with self.subTest(fake_notation=fake_notation):
                carriers = screener._source_def_carrier_map(fake_notation + declarations)
                self.assertNotIn("P", carriers)
                self.assertNotIn("Q", carriers)

    def test_notation_must_precede_the_definition_and_remain_in_scope(self):
        for source in [
            'def P : Mat := 0\nlocal notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ\n',
            'section\nlocal notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ\n'
            'end\ndef P : Mat := 0\n',
            'namespace Closed\nlocal notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ\n'
            'end Closed\ndef P : Mat := 0\n',
        ]:
            with self.subTest(source=source):
                self.assertNotIn("P", screener._source_def_carrier_map(source))

    def test_repeated_or_shadowed_notation_is_not_guessed(self):
        first = 'local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ\n'
        for shadow in [
            'local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ\n',
            'local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ\n',
            'local notation "Mat" => ℝ\n',
            'section\nlocal notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ\n',
        ]:
            with self.subTest(shadow=shadow):
                source = first + shadow + 'def P : Mat := 0\n'
                self.assertNotIn("P", screener._source_def_carrier_map(source))

    def test_notation_collision_with_named_type_alias_is_rejected(self):
        source = """
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ
def P : Mat := 0
"""
        self.assertNotIn("P", screener._source_def_carrier_map(source))

    def test_only_primitive_nullary_matrix_notation_is_resolved(self):
        for notation in [
            'local notation "Mat" => False → Matrix (Fin 3) (Fin 3) ℂ\n',
            'local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ × ℝ\n',
            'local notation "Mat" => (Matrix (Fin 3) (Fin 3) ℂ)\n',
            'notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ\n',
            'local notation:max "Mat" => Matrix (Fin 3) (Fin 3) ℂ\n',
        ]:
            with self.subTest(notation=notation):
                self.assertNotIn("P", screener._source_def_carrier_map(
                    notation + 'def P : Mat := 0\n'
                ))

    def test_locally_redefined_commute_is_not_the_native_predicate(self):
        source = self.before_witness + "def Commute (x y : Mat) : Prop := False\n"
        self.assertFalse(screener._witness_matches_matrix_carriers(
            source, "theorem witness", "¬ Commute P Q", self.carrier
        ))

    def test_local_commute_notation_is_not_the_native_predicate(self):
        source = self.before_witness + (
            'local notation "Commute" => (fun (_ _ : Mat) => False)\n'
        )
        self.assertFalse(screener._witness_matches_matrix_carriers(
            source, "theorem witness", "¬ Commute P Q", self.carrier
        ))

    def test_duplicate_operand_names_cannot_reuse_an_earlier_carrier(self):
        source = """
namespace Earlier
def P : Matrix (Fin 3) (Fin 3) ℂ := 0
def Q : Matrix (Fin 3) (Fin 3) ℂ := 0
end Earlier
namespace Later
def P : ℝ := 0
def Q : ℝ := 0
"""
        self.assertFalse(screener._witness_matches_matrix_carriers(
            source, "theorem witness", "¬ Commute P Q", self.carrier
        ))

    def test_raw_source_does_not_make_string_definitions_into_carriers(self):
        source = '''def payload : String := "
def P : Matrix (Fin 3) (Fin 3) ℂ := 0
def Q : Matrix (Fin 3) (Fin 3) ℂ := 0
"
'''
        carriers = screener._source_def_carrier_map(source)
        self.assertNotIn("P", carriers)
        self.assertNotIn("Q", carriers)

    def test_existing_product_inequality_owner_remains_supported(self):
        existing = (
            REPO_ROOT / "lean/InfoGeometry/OperatorAlgebra/FiniteMatrixNoncommutativeWitness.lean"
        ).read_text(encoding="utf-8")
        self.assertTrue(self.closed(existing, carrier={("2", "2", "ℝ")}))

    def test_attributed_qualified_and_quoted_predicates_are_not_native(self):
        for declaration in [
            "@[simp] def Commute (_ _ : Mat) : Prop := False\n",
            "@[simp]\ndef Commute (_ _ : Mat) : Prop := False\n",
            "@[simp] def Other.Commute (_ _ : Mat) : Prop := False\n",
            "def «Commute» (_ _ : Mat) : Prop := False\n",
            "@[simp] def Other.«Commute» (_ _ : Mat) : Prop := False\n",
        ]:
            with self.subTest(declaration=declaration):
                self.assertFalse(screener._witness_matches_matrix_carriers(
                    self.before_witness + declaration,
                    "theorem witness", "¬ Commute P Q", self.carrier,
                ))

    def test_attributed_qualified_and_quoted_operand_redeclarations_are_rejected(self):
        for name in ["P", "Q"]:
            for declaration in [
                f"@[simp] def {name} : ℝ := 0\n",
                f"@[simp] abbrev {name} : ℝ := 0\n",
                f"def Other.{name} : ℝ := 0\n",
                f"def «{name}» : ℝ := 0\n",
                f"@[simp] def Other.«{name}» : ℝ := 0\n",
                f"def _root_.Other.{name} : ℝ := 0\n",
            ]:
                with self.subTest(name=name, declaration=declaration):
                    self.assertFalse(screener._witness_matches_matrix_carriers(
                        self.before_witness + "namespace Later\n" + declaration,
                        "theorem witness", "¬ Commute P Q", self.carrier,
                    ))

    def test_matrix_binders_do_not_make_nonmatrix_or_parameterized_constants(self):
        for header in [
            "(x : Matrix (Fin 3) (Fin 3) ℂ) : Quaternion ℝ",
            "\n    (x : Matrix (Fin 3) (Fin 3) ℂ)\n    : Quaternion ℝ",
            "(x : Quaternion ℝ) : Matrix (Fin 3) (Fin 3) ℂ",
            "{x : Quaternion ℝ} : Matrix (Fin 3) (Fin 3) ℂ",
            "[h : Ring ℝ] : Matrix (Fin 3) (Fin 3) ℂ",
        ]:
            with self.subTest(header=header):
                source = f"def P {header} := 0\ndef Q {header} := 0\n"
                self.assertFalse(screener._witness_matches_matrix_carriers(
                    source, "theorem witness", "¬ Commute P Q", self.carrier,
                ))

    def test_matrix_function_domains_and_product_results_are_not_matrix_carriers(self):
        matrix = "Matrix (Fin 3) (Fin 3) ℂ"
        for result_type in [
            matrix + " → Quaternion ℝ",
            matrix + " × Quaternion ℝ",
            "Quaternion ℝ × " + matrix,
            matrix + " ⊕ Quaternion ℝ",
            "List (" + matrix + ")",
            "(" + matrix + ") → (" + matrix + ")",
        ]:
            with self.subTest(result_type=result_type):
                source = (
                    f"def P : {result_type} := 0\n"
                    f"def Q : {result_type} := 0\n"
                )
                self.assertFalse(screener._witness_matches_matrix_carriers(
                    source, "theorem witness", "¬ Commute P Q", self.carrier,
                ))

    def test_alias_expansion_cannot_supply_a_matrix_occurrence_inside_a_result(self):
        for result_type in [
            "Matrix (Fin 3) (Fin 3) ℂ → Quaternion ℝ",
            "Matrix (Fin 3) (Fin 3) ℂ × Quaternion ℝ",
        ]:
            with self.subTest(result_type=result_type):
                source = (
                    f"abbrev Result := {result_type}\n"
                    "def P : Result := 0\ndef Q : Result := 0\n"
                )
                self.assertFalse(screener._witness_matches_matrix_carriers(
                    source, "theorem witness", "¬ Commute P Q", self.carrier,
                ))

    def test_whitespace_commute_notation_fails_closed(self):
        for token in ["Commute ", " Commute", "  Commute  ", "Commute\t"]:
            with self.subTest(token=token):
                source = self.before_witness + (
                    f'local notation "{token}" => (fun (_ _ : Mat) => False)\n'
                )
                self.assertFalse(screener._witness_matches_matrix_carriers(
                    source, "theorem witness", "¬ Commute P Q", self.carrier,
                ))

    def test_attributed_axiom_or_opaque_forwarding_is_rejected(self):
        for declaration in [
            "@[simp] axiom supplied : ¬ Commute P Q\n",
            "@[simp] opaque supplied : ¬ Commute P Q\n",
            "@[simp] axiom Other.«supplied» : ¬ Commute P Q\n",
        ]:
            with self.subTest(declaration=declaration):
                self.assertFalse(self.closed(
                    self.before_witness + declaration
                    + "theorem fake : ¬ Commute P Q := supplied\n"
                ))

    def test_attributed_hole_forwarding_is_rejected(self):
        for declaration in [
            "@[simp] theorem supplied : ¬ Commute P Q := by sorry\n",
            "@[simp] def supplied : ¬ Commute P Q := by admit\n",
            "@[simp] theorem Other.«supplied» : ¬ Commute P Q := by sorry\n",
        ]:
            with self.subTest(declaration=declaration):
                self.assertFalse(self.closed(
                    self.before_witness + declaration
                    + "theorem fake : ¬ Commute P Q := supplied\n"
                ))

    def test_native_recognizer_does_not_erase_operand_type_ascriptions(self):
        for result in [
            "¬ Commute (P : Quaternion ℝ) Q",
            "¬ Commute P (Q : Quaternion ℝ)",
            "¬ Commute P Q (R := ℝ)",
        ]:
            with self.subTest(result=result):
                self.assertFalse(screener._witness_matches_matrix_carriers(
                    self.before_witness, "theorem witness", result, self.carrier,
                ))

    def test_ambient_parameters_are_not_presumed_to_give_nullary_constants(self):
        source = """
section
variable (x : Quaternion ℝ)
def P : Matrix (Fin 3) (Fin 3) ℂ := 0
def Q : Matrix (Fin 3) (Fin 3) ℂ := 0
end
"""
        self.assertFalse(screener._witness_matches_matrix_carriers(
            source, "theorem witness", "¬ Commute P Q", self.carrier,
        ))

    def test_operand_notation_cannot_reuse_a_constant_carrier(self):
        for name in ["P", "Q"]:
            with self.subTest(name=name):
                source = self.before_witness + f'local notation "{name}" => (0 : ℝ)\n'
                self.assertFalse(screener._witness_matches_matrix_carriers(
                    source, "theorem witness", "¬ Commute P Q", self.carrier,
                ))

    def test_shadow_and_taint_markers_in_comments_or_strings_are_ignored(self):
        for harmless in [
            "/- @[simp] axiom supplied : False; def Commute := False -/\n",
            '-- local notation "Commute " => False\n',
            'def payload : String := "axiom supplied : False; def Commute := False; '
            'local notation \\"Commute \\" => False; sorry"\n',
        ]:
            with self.subTest(harmless=harmless):
                self.assertTrue(screener._witness_matches_matrix_carriers(
                    self.before_witness + harmless,
                    "theorem witness", "¬ Commute P Q", self.carrier,
                ))


    def test_global_stripper_still_blanks_strings_and_preserves_offsets(self):
        source = 'local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ\n'
        clean = screener._strip_lean_comments_and_strings(source)
        self.assertEqual(len(clean), len(source))
        self.assertEqual(clean.count("\n"), source.count("\n"))
        self.assertNotIn('"Mat"', clean)
        self.assertEqual(clean.index("Matrix"), source.index("Matrix"))


if __name__ == "__main__":
    unittest.main()
