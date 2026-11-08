/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceBoundaryMetric
import InfoGeometry.OperatorAlgebra.PeirceBoundaryDynamics
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Full real matrix tests of the exact identities and rejected shortcuts -/

namespace InfoGeometry.OperatorAlgebra.PeirceBoundaryWitness

open Matrix InfoGeometry.OperatorAlgebra.LieJordan
open InfoGeometry.Core.PeirceDecomposition

noncomputable section

/-- Nondiagonal rank-two orthogonal support. -/
def p : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/2, 1/2, 0, 0; 1/2, 1/2, 0, 0; 0, 0, 1/2, 1/2; 0, 0, 1/2, 1/2]

/-- Every entry is nonzero; the two internal modes are coupled. -/
def q : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, -1, 2, -2; 1, -1, 2, -2; 3, -3, 4, -4; 3, -3, 4, -4]

def r : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 3, 3; -1, -1, -3, -3; 2, 2, 4, 4; -2, -2, -4, -4]

theorem p_idempotent : p * p = p := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, mul_apply, Fin.sum_univ_succ]

theorem p_selfadjoint : pᴴ = p := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p, conjTranspose_apply]

theorem q_square_zero : q * q = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [q, mul_apply, Fin.sum_univ_succ]

theorem r_transpose : r = qᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [q, r, conjTranspose_apply]

theorem q_supported : component10 p q = q := by
  have hleft : p * q = q := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [p, q, mul_apply, Fin.sum_univ_succ]
  have hright : q * p = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [p, q, mul_apply, Fin.sum_univ_succ]
  simp only [component10, complementIdempotent, hleft, mul_sub, mul_one, hright, sub_zero]

theorem arrows_noncommute : q * r ≠ r * q := by
  intro h
  have h00 := congrArg (fun m : Matrix (Fin 4) (Fin 4) ℝ => m 0 0) h
  norm_num [q, r, mul_apply, Fin.sum_univ_succ] at h00

/-- A square-zero generator need not induce a square-zero Jordan action. -/
theorem jordan_square_not_zero : jordanOp ℝ q * jordanOp ℝ q ≠ 0 := by
  intro h
  have h00 := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 4) (Fin 4) ℝ) => f r 0 0) h
  change jordanOp ℝ q (jordanOp ℝ q r) 0 0 = 0 at h00
  norm_num [jordanOp_apply, q, r, mul_apply, Fin.sum_univ_succ] at h00

theorem ordinary_lie_square_not_zero : lieOp ℝ q * lieOp ℝ q ≠ 0 := by
  intro h
  have h00 := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 4) (Fin 4) ℝ) => f r 0 0) h
  change lieOp ℝ q (lieOp ℝ q r) 0 0 = 0 at h00
  norm_num [lieOp_apply, q, r, mul_apply, Fin.sum_univ_succ] at h00

/-- The erroneous cross-swapped formula fails on a genuine Peirce pair. -/
theorem mixed_difference_not_jordan :
    lieOp ℝ q * jordanOp ℝ r - lieOp ℝ r * jordanOp ℝ q ≠
      jordanOp ℝ (q * r - r * q) := by
  intro h
  have h00 := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 4) (Fin 4) ℝ) => f p 0 0) h
  change (lieOp ℝ q (jordanOp ℝ r p) - lieOp ℝ r (jordanOp ℝ q p)) 0 0 =
    jordanOp ℝ (q * r - r * q) p 0 0 at h00
  norm_num [lieOp_apply, jordanOp_apply, p, q, r, mul_apply, Fin.sum_univ_succ] at h00

theorem q_odd : peirceTwist ℝ p p_idempotent q = -q := by
  have h := peirceTwist_forward ℝ p p_idempotent q
  simpa only [q_supported] using h

/-- Unlike either ungraded action, the global graded differential squares to zero. -/
theorem genuine_differential_square_zero :
    twistedInner ℝ (peirceTwist ℝ p p_idempotent).toAlgHom q *
      twistedInner ℝ (peirceTwist ℝ p p_idempotent).toAlgHom q = 0 :=
  twistedInner_square_zero ℝ _ (peirceTwist_involutive ℝ p p_idempotent)
    q_odd q_square_zero

/-- The differential is not a zero-map proxy. -/
theorem genuine_differential_nonzero :
    twistedInner ℝ (peirceTwist ℝ p p_idempotent).toAlgHom q ≠ 0 := by
  intro h
  have hr : (peirceTwist ℝ p p_idempotent).toAlgHom r = -r := by
    rw [r_transpose]
    exact peirce_odd_transpose p_idempotent p_selfadjoint q_odd
  have h00 := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 4) (Fin 4) ℝ) => f r 0 0) h
  change twistedInner ℝ (peirceTwist ℝ p p_idempotent).toAlgHom q r 0 0 = 0 at h00
  rw [twistedInner_apply, hr] at h00
  norm_num [q, r, mul_apply, Fin.sum_univ_succ] at h00

/-- Independent opposite directions need not define a positive map. -/
theorem negative_transport_not_positive :
    ¬ (crossTransport ℝ q (-r) 1).PosSemidef := by
  intro h
  have h00 := h.diag_nonneg (i := 0)
  simp only [crossTransport_apply, mul_one, mul_neg, neg_mul] at h00
  norm_num [q, r, mul_apply, Fin.sum_univ_succ] at h00

end
end InfoGeometry.OperatorAlgebra.PeirceBoundaryWitness
