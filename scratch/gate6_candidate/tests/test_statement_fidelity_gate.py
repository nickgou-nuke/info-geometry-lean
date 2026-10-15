import json
import subprocess
import sys
import unittest
from pathlib import Path

from tools.quality.statement_fidelity_gate import (
    FidelityDefect,
    FidelityReport,
    evaluate_file_fidelity,
    evaluate_statement_fidelity,
    parse_lean_declarations,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
BIRKHOFF_LEAN = REPO_ROOT / "proofs" / "BirkhoffPosetOperatorProjector.lean"
SPEC_JSON = REPO_ROOT / "tools" / "quality" / "statement_fidelity_birkhoff_spec.json"


# -----------------------------------------------------------------------------
# Genuine Theorems Evaluation Tests
# -----------------------------------------------------------------------------

def test_genuine_birkhoff_theorems_score_perfect():
    """Verify that all genuine theorems in BirkhoffPosetOperatorProjector.lean score 1.0."""
    reports = evaluate_file_fidelity(BIRKHOFF_LEAN, SPEC_JSON)
    assert len(reports) == 4
    for th_name, rep in reports.items():
        assert rep.passed is True, f"Theorem {th_name} failed: {rep.defects}"
        assert rep.fidelity_score == 1.0, f"Theorem {th_name} scored {rep.fidelity_score}, expected 1.0"
        assert len(rep.defects) == 0


def test_genuine_birkhoff_2x2_decomposition_isolated():
    """Test evaluate_statement_fidelity directly on birkhoff_2x2_decomposition text."""
    spec_data = json.loads(SPEC_JSON.read_text(encoding="utf-8"))
    th_spec = spec_data["theorems"]["birkhoff_2x2_decomposition"]

    code = """
structure DoublyStochastic2 where
  mat : Matrix (Fin 2) (Fin 2) ℝ
  nonneg : ∀ i j, 0 ≤ mat i j
  row_sum : ∀ i, mat i 0 + mat i 1 = 1
  col_sum : ∀ j, mat 0 j + mat 1 j = 1

theorem birkhoff_2x2_decomposition (D : DoublyStochastic2) :
    let θ := D.mat 0 0
    D.mat = θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 - θ) • matPerm12 := by sorry
"""
    rep = evaluate_statement_fidelity(code, th_spec)
    assert rep.passed is True
    assert rep.fidelity_score == 1.0
    assert "Matrix (Fin 2) (Fin 2) ℝ" in rep.carrier_detected
    assert len(rep.defects) == 0


def test_genuine_matrix_two_noncommutative():
    """Test evaluate_statement_fidelity on matrix_two_noncommutative."""
    spec_data = json.loads(SPEC_JSON.read_text(encoding="utf-8"))
    th_spec = spec_data["theorems"]["matrix_two_noncommutative"]

    code = """
def nullPlus : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![0, 1], ![0, 0]]
def nullMinus : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![0, 0], ![1, 0]]

theorem matrix_two_noncommutative : nullPlus (R := ℝ) * nullMinus ≠ nullMinus * nullPlus := by sorry
"""
    rep = evaluate_statement_fidelity(code, th_spec)
    assert rep.passed is True
    assert rep.fidelity_score == 1.0
    assert any("Matrix" in c for c in rep.carrier_detected)
    assert len(rep.defects) == 0


def test_missing_requested_declaration_does_not_fall_back_to_first():
    rep = evaluate_statement_fidelity(
        "theorem unrelated (x : Nat) : x + 0 = x := by sorry",
        {"theorem_name": "requested", "target_relation": {"pattern": "A = A"}},
    )
    assert not rep.passed
    assert rep.fidelity_score == 0.0
    assert rep.defects[0].defect_type == "TARGET_DECLARATION_NOT_FOUND"


def test_target_symbol_alias_selects_requested_declaration_not_first():
    code = """
theorem unrelated (x : Nat) : x = x := by rfl
theorem requested (x : Nat) : x + 0 = x := by simp
"""
    report = evaluate_statement_fidelity(
        code,
        {"target_symbol": "requested", "target_relation": {"pattern": r"x \+ 0 = x"}},
    )
    assert report.theorem_name == "requested"
    assert report.conclusion_detected == "x + 0 = x"
    assert report.passed


def test_conflicting_target_aliases_fail_closed():
    code = "theorem first : True := by trivial\ntheorem second : True := by trivial"
    report = evaluate_statement_fidelity(
        code, {"theorem_name": "first", "target_symbol": "second"}
    )
    assert not report.passed
    assert report.fidelity_score == 0.0
    assert report.defects[0].defect_type == "TARGET_DECLARATION_AMBIGUOUS"


def test_unqualified_target_collision_is_ambiguous_not_source_ordered():
    code = "namespace A\ntheorem target : True := by trivial\nend A\nnamespace B\ntheorem target : True := by trivial\nend B"
    report = evaluate_statement_fidelity(code, {"decl": "target"})
    assert not report.passed
    assert report.defects[0].defect_type == "TARGET_DECLARATION_AMBIGUOUS"


def test_missing_target_requires_explicit_first_declaration_opt_in():
    code = "theorem only_decl : True := by trivial"
    rejected = evaluate_statement_fidelity(code, {})
    accepted = evaluate_statement_fidelity(code, {"allow_first_declaration": True})
    assert not rejected.passed
    assert rejected.defects[0].defect_type == "TARGET_DECLARATION_REQUIRED"
    assert accepted.theorem_name == "only_decl"


def test_cli_unknown_suite_target_fails_instead_of_returning_empty_success(tmp_path: Path):
    lean_path = tmp_path / "Candidate.lean"
    spec_path = tmp_path / "spec.json"
    lean_path.write_text("theorem existing : 2 + 2 = 4 := by norm_num", encoding="utf-8")
    spec_path.write_text(json.dumps({"theorems": {"existing": {"target_relation": {"pattern": "2 \\+ 2 = 4"}}}}), encoding="utf-8")
    cmd = [
        sys.executable,
        str(REPO_ROOT / "tools" / "quality" / "statement_fidelity_gate.py"),
        "evaluate", "--lean", str(lean_path), "--spec", str(spec_path),
        "--decl", "missing", "--json",
    ]
    result = subprocess.run(cmd, capture_output=True, text=True)
    assert result.returncode != 0
    data = json.loads(result.stdout)
    assert data["all_passed"] is False
    assert data["reports"]["missing"]["defects"][0]["defect_type"] == "TARGET_DECLARATION_NOT_FOUND"


def test_single_spec_cli_target_conflict_is_not_silently_overridden(tmp_path: Path):
    lean_path = tmp_path / "Candidate.lean"
    spec_path = tmp_path / "spec.json"
    lean_path.write_text(
        "theorem intended (n : Nat) : n + 0 = n := by simp\n"
        "theorem other (n : Nat) : n + 1 = n + 1 := by simp",
        encoding="utf-8",
    )
    spec_path.write_text(json.dumps({"theorem_name": "intended", "target_relation": {"pattern": "n \\+ 0 = n"}}), encoding="utf-8")
    reports = evaluate_file_fidelity(lean_path, spec_path, target_decl="other")
    report = next(iter(reports.values()))
    assert not report.passed
    assert report.defects[0].defect_type == "TARGET_DECLARATION_AMBIGUOUS"


def test_unrelated_structure_fields_are_not_counted_as_hypotheses():
    code = """
structure Unused where
  row_sum : ∀ i : Nat, i = i

theorem target (A B : Matrix (Fin 2) (Fin 2) ℝ) (h : A = B) :
    A * B = B * A := by sorry
"""
    spec = {
        "theorem_name": "target",
        "required_hypotheses": [{"name": "row_sum", "pattern": r"row_sum"}],
        "target_relation": {"pattern": r"A \* B = B \* A"},
    }
    report = evaluate_statement_fidelity(code, spec)
    assert not report.passed
    assert any(d.defect_type == "DROPPED_HYPOTHESIS" for d in report.defects)


def test_variable_binders_from_closed_scope_do_not_leak():
    code = """
namespace Earlier
variable (required_property : Nat = Nat)
theorem earlier : True := by trivial
end Earlier

theorem target (n : Nat) : n + 0 = n := by sorry
"""
    report = evaluate_statement_fidelity(
        code,
        {
            "theorem_name": "target",
            "required_hypotheses": ["required_property"],
            "target_relation": {"pattern": r"n \+ 0 = n"},
        },
    )
    assert not report.passed
    assert any(d.defect_type == "DROPPED_HYPOTHESIS" for d in report.defects)
    assert not any("required_property" in item for item in report.hypotheses_detected)


# -----------------------------------------------------------------------------
# Intentional Mutants Tests (Fidelity Defect Penalties)
# -----------------------------------------------------------------------------

def test_mutant_dropped_hypotheses():
    """Mutant 1: Essential hypotheses (row_sum, col_sum) are dropped."""
    spec_data = json.loads(SPEC_JSON.read_text(encoding="utf-8"))
    th_spec = spec_data["theorems"]["birkhoff_2x2_decomposition"]

    # Omits DoublyStochastic2 and only assumes nonneg; row_sum and col_sum are dropped
    mutant_code = """
theorem birkhoff_2x2_decomposition (mat : Matrix (Fin 2) (Fin 2) ℝ) (h_nonneg : ∀ i j, 0 ≤ mat i j) :
    let θ := mat 0 0
    mat = θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 - θ) • matPerm12 := by sorry
"""
    rep = evaluate_statement_fidelity(mutant_code, th_spec)
    assert rep.passed is False
    assert rep.fidelity_score < 0.95
    defect_types = [d.defect_type for d in rep.defects]
    assert defect_types.count("DROPPED_HYPOTHESIS") >= 2
    dropped_contexts = [d.context for d in rep.defects if d.defect_type == "DROPPED_HYPOTHESIS"]
    assert "row_sum" in dropped_contexts
    assert "col_sum" in dropped_contexts


def test_mutant_carrier_demotion_scalar_proxy():
    """Mutant 2: Non-commutative matrix algebra collapsed to scalar proxy (Trap T16)."""
    spec_data = json.loads(SPEC_JSON.read_text(encoding="utf-8"))
    th_spec = spec_data["theorems"]["birkhoff_2x2_decomposition"]

    mutant_code = """
structure ScalarBirkhoffProxy where
  mat : ℝ
  nonneg : 0 ≤ mat
  row_sum : mat = 1
  col_sum : mat = 1

theorem birkhoff_2x2_decomposition (D : ScalarBirkhoffProxy) :
    let θ := D.mat
    D.mat = θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 - θ) • matPerm12 := by sorry
"""
    rep = evaluate_statement_fidelity(mutant_code, th_spec)
    assert rep.passed is False
    assert rep.fidelity_score < 0.95
    assert any(d.defect_type == "CARRIER_DEMOTION_T16" for d in rep.defects)


def test_mutant_t6_hypothesis_packaging():
    """Mutant 3: T6 Packaging - hypothesis is definitionally identical to the conclusion."""
    spec_data = json.loads(SPEC_JSON.read_text(encoding="utf-8"))
    th_spec = spec_data["theorems"]["birkhoff_2x2_decomposition"]

    target_conc = "let θ := D.mat 0 0; D.mat = θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 - θ) • matPerm12"
    mutant_code = f"""
structure DoublyStochastic2 where
  mat : Matrix (Fin 2) (Fin 2) ℝ
  nonneg : ∀ i j, 0 ≤ mat i j
  row_sum : ∀ i, mat i 0 + mat i 1 = 1
  col_sum : ∀ j, mat 0 j + mat 1 j = 1

theorem birkhoff_2x2_decomposition (D : DoublyStochastic2) (h_packaged : {target_conc}) :
    {target_conc} := by exact h_packaged
"""
    rep = evaluate_statement_fidelity(mutant_code, th_spec)
    assert rep.passed is False
    assert rep.fidelity_score == 0.0  # FATAL defect
    assert any(d.defect_type == "T6_HYPOTHESIS_PACKAGING" for d in rep.defects)
    assert any(d.severity == "FATAL" for d in rep.defects)


def test_mutant_vacuous_conclusion_true():
    """Mutant 4a: Vacuous conclusion (True)."""
    spec_data = json.loads(SPEC_JSON.read_text(encoding="utf-8"))
    th_spec = spec_data["theorems"]["birkhoff_2x2_decomposition"]

    mutant_code = """
structure DoublyStochastic2 where
  mat : Matrix (Fin 2) (Fin 2) ℝ
  nonneg : ∀ i j, 0 ≤ mat i j
  row_sum : ∀ i, mat i 0 + mat i 1 = 1
  col_sum : ∀ j, mat 0 j + mat 1 j = 1

theorem birkhoff_2x2_decomposition (D : DoublyStochastic2) : True := by trivial
"""
    rep = evaluate_statement_fidelity(mutant_code, th_spec)
    assert rep.passed is False
    assert rep.fidelity_score == 0.0
    assert any(d.defect_type == "VACUOUS_CONCLUSION" for d in rep.defects)


def test_mutant_vacuous_conclusion_zero_eq_zero():
    """Mutant 4b: Vacuous conclusion (0 = 0)."""
    spec_data = json.loads(SPEC_JSON.read_text(encoding="utf-8"))
    th_spec = spec_data["theorems"]["birkhoff_2x2_decomposition"]

    mutant_code = """
structure DoublyStochastic2 where
  mat : Matrix (Fin 2) (Fin 2) ℝ
  nonneg : ∀ i j, 0 ≤ mat i j
  row_sum : ∀ i, mat i 0 + mat i 1 = 1
  col_sum : ∀ j, mat 0 j + mat 1 j = 1

theorem birkhoff_2x2_decomposition (D : DoublyStochastic2) : 0 = 0 := by rfl
"""
    rep = evaluate_statement_fidelity(mutant_code, th_spec)
    assert rep.passed is False
    assert rep.fidelity_score == 0.0
    assert any(d.defect_type == "VACUOUS_CONCLUSION" for d in rep.defects)


def test_mutant_relation_mismatch_commutative_collapse():
    """Mutant 5: Strict non-commutativity witness demoted to commutative equality."""
    spec_data = json.loads(SPEC_JSON.read_text(encoding="utf-8"))
    th_spec = spec_data["theorems"]["matrix_two_noncommutative"]

    mutant_code = """
def nullPlus : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![0, 1], ![0, 0]]
def nullMinus : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![0, 0], ![1, 0]]

theorem matrix_two_noncommutative : nullPlus (R := ℝ) * nullMinus = nullMinus * nullPlus := by sorry
"""
    rep = evaluate_statement_fidelity(mutant_code, th_spec)
    assert rep.passed is False
    assert rep.fidelity_score < 0.95
    assert any(d.defect_type == "RELATION_MISMATCH" for d in rep.defects)


# -----------------------------------------------------------------------------
# AST JSON Input Testing
# -----------------------------------------------------------------------------

def test_ast_json_input():
    """Test evaluate_statement_fidelity with AST JSON input."""
    spec_data = json.loads(SPEC_JSON.read_text(encoding="utf-8"))
    th_spec = spec_data["theorems"]["matrix_two_noncommutative"]

    ast_data = {
        "declarations": [
            {
                "name": "matrix_two_noncommutative",
                "kind": "theorem",
                "binders": [],
                "conclusion": "nullPlus (R := ℝ) * nullMinus ≠ nullMinus * nullPlus",
                "bundled_structures": {
                    "Matrix": {"dim": "Fin 2"}
                }
            }
        ]
    }
    rep = evaluate_statement_fidelity(ast_data, th_spec)
    assert rep.passed is True
    assert rep.fidelity_score == 1.0


# -----------------------------------------------------------------------------
# CLI Testing
# -----------------------------------------------------------------------------

def test_cli_evaluate_genuine_file():
    """Test CLI evaluation on genuine proofs/BirkhoffPosetOperatorProjector.lean."""
    cmd = [
        sys.executable,
        str(REPO_ROOT / "tools" / "quality" / "statement_fidelity_gate.py"),
        "evaluate",
        "--lean",
        str(BIRKHOFF_LEAN),
        "--spec",
        str(SPEC_JSON),
    ]
    res = subprocess.run(cmd, capture_output=True, text=True)
    assert res.returncode == 0, f"CLI failed:\nSTDOUT:\n{res.stdout}\nSTDERR:\n{res.stderr}"
    assert "[RESULT] ALL THEOREMS PASSED FIDELITY GATE" in res.stdout


def test_cli_evaluate_json_output():
    """Test CLI evaluation with --json flag."""
    cmd = [
        sys.executable,
        str(REPO_ROOT / "tools" / "quality" / "statement_fidelity_gate.py"),
        "evaluate",
        "--lean",
        str(BIRKHOFF_LEAN),
        "--spec",
        str(SPEC_JSON),
        "--json",
    ]
    res = subprocess.run(cmd, capture_output=True, text=True)
    assert res.returncode == 0
    data = json.loads(res.stdout)
    assert data["all_passed"] is True
    assert "birkhoff_2x2_decomposition" in data["reports"]
    assert data["reports"]["birkhoff_2x2_decomposition"]["fidelity_score"] == 1.0


def test_cli_decl_filter():
    """Test CLI evaluation with --decl filter."""
    cmd = [
        sys.executable,
        str(REPO_ROOT / "tools" / "quality" / "statement_fidelity_gate.py"),
        "evaluate",
        "--lean",
        str(BIRKHOFF_LEAN),
        "--spec",
        str(SPEC_JSON),
        "--decl",
        "peirce_diff_sq",
        "--json",
    ]
    res = subprocess.run(cmd, capture_output=True, text=True)
    assert res.returncode == 0
    data = json.loads(res.stdout)
    assert len(data["reports"]) == 1
    assert "peirce_diff_sq" in data["reports"]


class StatementFidelityGateTestCase(unittest.TestCase):
    def test_genuine_birkhoff_theorems_score_perfect(self):
        test_genuine_birkhoff_theorems_score_perfect()

    def test_genuine_birkhoff_2x2_decomposition_isolated(self):
        test_genuine_birkhoff_2x2_decomposition_isolated()

    def test_genuine_matrix_two_noncommutative(self):
        test_genuine_matrix_two_noncommutative()

    def test_mutant_dropped_hypotheses(self):
        test_mutant_dropped_hypotheses()

    def test_mutant_carrier_demotion_scalar_proxy(self):
        test_mutant_carrier_demotion_scalar_proxy()

    def test_mutant_t6_hypothesis_packaging(self):
        test_mutant_t6_hypothesis_packaging()

    def test_mutant_vacuous_conclusion_true(self):
        test_mutant_vacuous_conclusion_true()

    def test_mutant_vacuous_conclusion_zero_eq_zero(self):
        test_mutant_vacuous_conclusion_zero_eq_zero()

    def test_mutant_relation_mismatch_commutative_collapse(self):
        test_mutant_relation_mismatch_commutative_collapse()

    def test_ast_json_input(self):
        test_ast_json_input()

    def test_cli_evaluate_genuine_file(self):
        test_cli_evaluate_genuine_file()

    def test_cli_evaluate_json_output(self):
        test_cli_evaluate_json_output()

    def test_cli_decl_filter(self):
        test_cli_decl_filter()


if __name__ == "__main__":
    unittest.main()

