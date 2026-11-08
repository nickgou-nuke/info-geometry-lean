/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorChiralDeterminantDefect

/-! Exact scalar-channel factorization over noncommutative coefficient rings.
The diagonal commutators need only agree; neither must vanish separately. -/

namespace InfoGeometry.Canonical.OperatorChiralDeterminantDefect

variable {A : Type*} [Ring A]

theorem chiralBlock_mul_adjugate_eq_scalar_iff (p m r l : A) :
    chiralBlock p m r l * chiralAdjugate p m r l =
      scalarChiralBlock (leftQuadraticReadout p m r l) ↔
    Commute r p ∧ Commute l m ∧
      operatorCommutator p m = operatorCommutator r l := by
  rw [chiralBlock_mul_adjugate]
  constructor
  · intro h
    have h01 := congrArg (fun M : ChiralBlock A => M 0 1) h
    have h10 := congrArg (fun M : ChiralBlock A => M 1 0) h
    have h11 := congrArg (fun M : ChiralBlock A => M 1 1) h
    simp [scalarChiralBlock] at h01 h10 h11
    refine ⟨sub_eq_zero.mp h01, sub_eq_zero.mp h10, ?_⟩
    apply sub_eq_zero.mp
    rw [← left_sub_right_eq_commutator_defect, h11, sub_self]
  · rintro ⟨hrp, hlm, hdiag⟩
    have hd : rightQuadraticReadout p m r l = leftQuadraticReadout p m r l := by
      apply Eq.symm
      apply sub_eq_zero.mp
      rw [left_sub_right_eq_commutator_defect, hdiag, sub_self]
    have h01 : operatorCommutator r p = 0 := sub_eq_zero.mpr hrp.eq
    have h10 : operatorCommutator l m = 0 := sub_eq_zero.mpr hlm.eq
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarChiralBlock, h01, h10, hd]

/-- Readback on the existing associative operator-Zorn carrier. -/
theorem operatorZorn_scalar_factorization_iff [StarRing A]
    (M : InfoGeometry.Physics.OperatorZornMatrix A) :
    InfoGeometry.Physics.OperatorZornMatrix.toMatrix M * operatorZornAdjugateMatrix M =
      scalarChiralBlock (leftQuadraticReadout M.n_plus_op M.n_minus_op
        M.sigma_plus_op M.sigma_minus_op) ↔
    Commute M.sigma_plus_op M.n_plus_op ∧
      Commute M.sigma_minus_op M.n_minus_op ∧
      operatorCommutator M.n_plus_op M.n_minus_op =
        operatorCommutator M.sigma_plus_op M.sigma_minus_op := by
  simpa [InfoGeometry.Physics.OperatorZornMatrix.toMatrix,
    operatorZornAdjugateMatrix, chiralBlock] using
    chiralBlock_mul_adjugate_eq_scalar_iff M.n_plus_op M.n_minus_op
      M.sigma_plus_op M.sigma_minus_op

end InfoGeometry.Canonical.OperatorChiralDeterminantDefect
