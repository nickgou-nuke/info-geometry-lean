/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixSquareNegOne
import InfoGeometry.Algebra.MatrixAmplification
import InfoGeometry.Canonical.Sandbox.NativeQuaternionPauli

/-!
# Native quaternion matrix roots and noncommuting scalar matrices

The three existing real quaternion axes give the literal mixed diagonal
`diag(i, j, k)`. Its square is minus the identity without a pairwise commutation
assumption. Scalar amplification also retains the noncommutation of `i` and `j`;
being a scalar matrix over a noncommutative ring does not make it central.

These are concrete constructions in `Matrix n n (Quaternion ℝ)`. No quaternion
matrix conjugacy classification is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra.QuaternionMatrixSquareNegOne

open InfoGeometry.Canonical.Sandbox.NativeQuaternionPauli
open InfoGeometry.Algebra.MatrixSquareNegOne

/-- The mixed diagonal of the existing native quaternion axes. -/
def mixedDiagonal : Matrix (Fin 3) (Fin 3) (Quaternion ℝ) :=
  Matrix.diagonal ![qI, qJ, qK]

theorem mixedDiagonal_square_eq_neg_one : mixedDiagonal * mixedDiagonal = -1 := by
  unfold mixedDiagonal
  apply (diagonal_square_eq_neg_one_iff _).2
  intro i
  fin_cases i <;> simp

/-- A nonempty scalar amplification preserves the actual quaternion noncommutation. -/
theorem scalar_qI_not_commute_scalar_qJ
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    ¬ Commute (Matrix.scalar n qI) (Matrix.scalar n qJ) := by
  intro h
  have hq : Commute qI qJ :=
    (InfoGeometry.Algebra.MatrixAmplification.scalar_commute_iff (n := n) qI qJ).mp h
  have hk := congrArg (fun q : Quaternion ℝ => q.imK) hq.eq
  norm_num [qI_mul_qJ, qJ_mul_qI, qK] at hk

/-- The actual three-by-three quaternion ring contains two noncommuting
roots of minus one, obtained from the existing native quaternion axes. -/
theorem exists_noncommuting_three_roots :
    ∃ A B : Matrix (Fin 3) (Fin 3) (Quaternion ℝ),
      A * B ≠ B * A ∧ A * A = -1 ∧ B * B = -1 := by
  refine ⟨Matrix.scalar (Fin 3) qI, Matrix.scalar (Fin 3) qJ, ?_,
    scalar_square_eq_neg_one qI qI_sq, scalar_square_eq_neg_one qJ qJ_sq⟩
  intro h
  exact scalar_qI_not_commute_scalar_qJ h

end InfoGeometry.Algebra.QuaternionMatrixSquareNegOne
