import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.ZornOctonionAnyonGellMannBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex ZornOctonionAnyon

namespace SplitQuaternionZorn

/-- Cayley-Dickson Doubling Map: Pair of 2x2 Split Quaternion Matrices (q₁, q₂) → Zorn Split Octonion Cell. -/
def pairToZorn (q1 q2 : Matrix (Fin 2) (Fin 2) ℂ) : ZornCell where
  a := q1 0 0
  u := fun i => match i with
    | 0 => q1 1 0
    | 1 => q2 1 0
    | 2 => q2 1 1
  v := fun i => match i with
    | 0 => q1 0 1
    | 1 => q2 0 0
    | 2 => q2 0 1
  b := q1 1 1

/-- **Theorem**: Zorn Diagonal Trace equals first Split Quaternion Matrix Trace:
    Tr_Zorn(Z(q₁, q₂)) = q₁(0,0) + q₁(1,1) = Tr(q₁). -/
theorem zorn_trace_eq_q1_trace (q1 q2 : Matrix (Fin 2) (Fin 2) ℂ) :
    (pairToZorn q1 q2).a + (pairToZorn q1 q2).b = trace q1 := by
  dsimp [pairToZorn, trace]
  rw [Fin.sum_univ_two]

/-- **Theorem**: Zorn Off-Diagonal Color Vectors for (q₁, q₂):
    v = (q₁₀₁, q₂₀₀, q₂₀₁), w = (q₁₁₀, q₂₁₀, q₂₁₁). -/
theorem zorn_color_vectors (q1 q2 : Matrix (Fin 2) (Fin 2) ℂ) :
    ZornCell.colorDot (pairToZorn q1 q2).u (pairToZorn q1 q2).v =
    q1 0 1 * q1 1 0 + q2 0 0 * q2 1 0 + q2 0 1 * q2 1 1 := by
  simp [pairToZorn, ZornCell.colorDot,
    InfoGeometry.Physics.SplitOctonionBraidSU3.dot3,
    mul_comm, add_comm]

/-- **Theorem**: Zorn Split Octonion Determinant in terms of Matrix Elements:
    det(Z(q₁, q₂)) = q₁₀₀ * q₁₁₁ - (q₁₀₁ q₁₁₀ + q₂₀₀ q₂₁₀ + q₂₀₁ q₂₁₁). -/
theorem zorn_det_expansion (q1 q2 : Matrix (Fin 2) (Fin 2) ℂ) :
    ZornCell.detZ (pairToZorn q1 q2) =
    q1 0 0 * q1 1 1 - (q1 0 1 * q1 1 0 + q2 0 0 * q2 1 0 + q2 0 1 * q2 1 1) := by
  change
    q1 0 0 * q1 1 1 -
        (q1 1 0 * q1 0 1 + q2 1 0 * q2 0 0 + q2 1 1 * q2 0 1) =
      q1 0 0 * q1 1 1 -
        (q1 0 1 * q1 1 0 + q2 0 0 * q2 1 0 + q2 0 1 * q2 1 1)
  ring

/-- **Theorem**: Pure Chiral Off-Diagonal Pair (q₁₀₀ = 0, q₁₁₁ = 0):
    det(Z(q₁, q₂)) = - (q₁₀₁ q₁₁₀ + q₂₀₀ q₂₁₀ + q₂₀₁ q₂₁₁). -/
theorem zorn_det_chiral_null (q1 q2 : Matrix (Fin 2) (Fin 2) ℂ)
    (h1 : q1 0 0 = 0) (h2 : q1 1 1 = 0) :
    ZornCell.detZ (pairToZorn q1 q2) =
    - (q1 0 1 * q1 1 0 + q2 0 0 * q2 1 0 + q2 0 1 * q2 1 1) := by
  rw [zorn_det_expansion, h1, h2, zero_mul, zero_sub]

end SplitQuaternionZorn
