import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace ZornCayleyDickson

/-- 2x2 Symplectic Adjugate (Conjugation) Matrix for M₂ (ℂ). -/
def adjugate2x2 (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![M 1 1, -M 0 1;
    -M 1 0,  M 0 0]

/-- **Theorem**: 2x2 Adjugate Trace Identity: Tr(adj(M)) = Tr(M). -/
theorem adjugate_trace_eq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (adjugate2x2 M) = trace M := by
  dsimp [adjugate2x2, trace]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  dsimp
  ring

/-- **Theorem**: Cayley-Dickson Adjugate Product Generates 3D Cross Product Term:
    (D * adj(B))₀₀ = D₀₀ B₁₁ - D₀₁ B₁₀. -/
theorem cd_adjugate_generates_cross_product (B D : Matrix (Fin 2) (Fin 2) ℂ) :
    (D * adjugate2x2 B) 0 0 = D 0 0 * B 1 1 - D 0 1 * B 1 0 := by
  dsimp [adjugate2x2, mul_apply]
  rw [Fin.sum_univ_two]
  dsimp
  ring

/-- **Theorem**: 2x2 Matrix Times Its Adjugate Equals Determinant Times Identity:
    M * adj(M) = det(M) • 1. -/
theorem matrix_mul_adjugate_eq_det (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * adjugate2x2 M = (M 0 0 * M 1 1 - M 0 1 * M 1 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [adjugate2x2, mul_apply, smul_apply, one_apply]
    rw [Fin.sum_univ_two]
    dsimp
    ring
  · dsimp [adjugate2x2, mul_apply, smul_apply, one_apply]
    rw [Fin.sum_univ_two]
    dsimp
    ring
  · dsimp [adjugate2x2, mul_apply, smul_apply, one_apply]
    rw [Fin.sum_univ_two]
    dsimp
    ring
  · dsimp [adjugate2x2, mul_apply, smul_apply, one_apply]
    rw [Fin.sum_univ_two]
    dsimp
    ring

/-- **Theorem**: Trace of Matrix Times Its Adjugate Equals 2 * det(M). -/
theorem trace_mul_adjugate_eq_two_det (M : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (M * adjugate2x2 M) = 2 * (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
  rw [matrix_mul_adjugate_eq_det, trace_smul, trace_one, Fintype.card_fin]
  dsimp [nsmul_eq_mul]
  ring

end ZornCayleyDickson
