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

