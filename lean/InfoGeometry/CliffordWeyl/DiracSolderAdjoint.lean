/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! # Ground-truth contract: Dirac adjunction of matrix ket–bras

For the existing `solder η l r = l (star r) η`, Hermitian involutive η gives
`η * (solder η l r).conjTranspose * η = solder η r l`.
This theorem is metric-twisted adjunction, not ordinary conjugate transpose.
The existing native metric `2 • FiniteSpin.J_zero` supplies signature (1,1).
Its ket–bras on the two coordinate vectors are `-J_plus` and `J_minus`:
noncommuting off-diagonal operators. Ordinary conjugate transpose fails to
exchange them. No positive inner product, Zorn star, minimality, or
identification with right octonionic multiplication is inferred.
-/
namespace InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open Matrix

section MatrixDirac
variable {Scalar Index : Type*} [CommRing Scalar] [StarRing Scalar]
variable [Fintype Index]

theorem solder_eq_vecMulVec_mul (η : Matrix Index Index Scalar) (l r : Index → Scalar) :
    solder η l r = vecMulVec l (star r) * η := by
  rw [Matrix.vecMulVec_mul]
  rfl

variable [DecidableEq Index]

/-- Matrix Dirac adjunction exchanges the two spinors of a metric ket–bra. -/
theorem solder_metric_adjoint (η : Matrix Index Index Scalar)
    (hHermitian : η.conjTranspose = η) (hInvolution : η * η = 1)
    (l r : Index → Scalar) :
    η * (solder η l r).conjTranspose * η = solder η r l := by
  rw [solder_eq_vecMulVec_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_vecMulVec, hHermitian, star_star,
    solder_eq_vecMulVec_mul]
  rw [← mul_assoc, hInvolution, one_mul]

/-- Compatibility with the already existing algebraic Dirac-adjoint API. -/
theorem diracAdjoint_solder
    (K : InfoGeometry.Physics.KasparovKreinData (Matrix Index Index Scalar))
    (l r : Index → Scalar) :
    K.diracAdjoint (solder K.eta l r) = solder K.eta r l := by
  change K.eta * (solder K.eta l r).conjTranspose * K.eta = _
  exact solder_metric_adjoint K.eta K.2.2.1 K.2.1 l r

end MatrixDirac

section Counterexample
open InfoGeometry.Algebra.FiniteSpin

/-- Native finite-spin metric is an involution with one positive and one negative diagonal entry. -/
theorem finiteSpin_metric_involution :
    ((2 : ℂ) • J_zero) * ((2 : ℂ) • J_zero) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J_zero, Matrix.mul_apply, Fin.sum_univ_two]

theorem finiteSpin_metric_hermitian :
    ((2 : ℂ) • J_zero).conjTranspose = (2 : ℂ) • J_zero := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J_zero, Matrix.conjTranspose_apply]

theorem finiteSpin_solder_forward :
    solder ((2 : ℂ) • J_zero) ![1, 0] ![0, 1] = -J_plus := by
  have hs : star (![0, 1] : Fin 2 → ℂ) = ![0, 1] := by
    ext i; fin_cases i <;> simp
  unfold solder diracRow
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [solder, diracRow, J_zero, J_plus, Matrix.vecMulVec_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem finiteSpin_solder_reverse :
    solder ((2 : ℂ) • J_zero) ![0, 1] ![1, 0] = J_minus := by
  have hs : star (![1, 0] : Fin 2 → ℂ) = ![1, 0] := by
    ext i; fin_cases i <;> simp
  unfold solder diracRow
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [solder, diracRow, J_zero, J_minus, Matrix.vecMulVec_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Ordinary conjugate transpose does not exchange these Dirac ket–bras. -/
theorem ordinary_adjoint_not_dirac_solder_exchange :
    (solder ((2 : ℂ) • J_zero) ![1, 0] ![0, 1]).conjTranspose ≠
      solder ((2 : ℂ) • J_zero) ![0, 1] ![1, 0] := by
  rw [finiteSpin_solder_forward, finiteSpin_solder_reverse]
  intro h
  have hentry := congrArg (fun M : Mat2C => M 1 0) h
  norm_num [J_plus, J_minus, Matrix.conjTranspose_apply] at hentry

/-- The counterexample uses noncommuting off-diagonal operators. -/
theorem dirac_solder_pair_not_commute :
    ¬ Commute (solder ((2 : ℂ) • J_zero) ![1, 0] ![0, 1])
      (solder ((2 : ℂ) • J_zero) ![0, 1] ![1, 0]) := by
  rw [finiteSpin_solder_forward, finiteSpin_solder_reverse]
  intro h
  have hentry := congrArg (fun M : Mat2C => M 0 0) h.eq
  norm_num [J_plus, J_minus, Matrix.mul_apply, Fin.sum_univ_two] at hentry

end Counterexample
end InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
