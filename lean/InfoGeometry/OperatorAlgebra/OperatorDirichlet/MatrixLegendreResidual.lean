/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.MatrixLegendre
import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
import Mathlib.Tactic.Abel

/-!
# Quadratic Fenchel residual with a supplied inverse

The established square-completion theorem gives the residual for arbitrary
finite real matrices `G` and `GInv`. The hypotheses are symmetry of `GInv` and
`G * GInv = 1`; symmetry of `G` need not be assumed separately. Positivity is
used only for nonnegativity and the attained maximum. The last theorem states
the actual supremum of the paired quadratic objective, with its bound and
attaining point established by `IsGreatest`.

This is finite-dimensional convex algebra. No derivative, Bregman divergence,
or para-Kähler manifold is asserted.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorDirichlet

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The gap between the paired quadratic potentials and their dual pairing. -/
def quadraticFenchelGap (G GInv : Matrix n n ℝ) (x y : n → ℝ) : ℝ :=
  (1 / 2) * quadForm G x + (1 / 2) * quadForm GInv y - x ⬝ᵥ y

/-- The gap is the inverse quadratic form of the Legendre residual.
This identity does not require positivity. -/
theorem quadraticFenchelGap_eq_residual {G GInv : Matrix n n ℝ}
    (hSymInv : GInvᵀ = GInv) (hInv : G * GInv = 1) (x y : n → ℝ) :
    quadraticFenchelGap G GInv x y =
      (1 / 2) * quadForm GInv (G *ᵥ x - y) := by
  have h := legendre_complete_square hSymInv
    (Matrix.isUnit_det_of_left_inverse hInv) y x
  rw [Matrix.inv_eq_left_inv hInv, dotProduct_comm y x] at h
  have hneg : quadForm GInv (y - G *ᵥ x) = quadForm GInv (G *ᵥ x - y) := by
    rw [show y - G *ᵥ x = -(G *ᵥ x - y) by abel]
    simp [quadForm]
  rw [hneg] at h
  unfold quadraticFenchelGap
  calc
    (1 / 2) * quadForm G x + (1 / 2) * quadForm GInv y - x ⬝ᵥ y =
        (1 / 2) * quadForm G x - (x ⬝ᵥ y - (1 / 2) * quadForm GInv y) := by abel
    _ = (1 / 2) * quadForm G x -
        ((1 / 2) * quadForm G x - (1 / 2) * quadForm GInv (G *ᵥ x - y)) := by rw [h]
    _ = (1 / 2) * quadForm GInv (G *ᵥ x - y) := sub_sub_cancel _ _

/-- Positive semidefiniteness of the supplied inverse makes the gap nonnegative. -/
theorem quadraticFenchelGap_nonneg {G GInv : Matrix n n ℝ}
    (hSymInv : GInvᵀ = GInv) (hInv : G * GInv = 1)
    (hPSD : ∀ z : n → ℝ, 0 ≤ quadForm GInv z) (x y : n → ℝ) :
    0 ≤ quadraticFenchelGap G GInv x y := by
  rw [quadraticFenchelGap_eq_residual hSymInv hInv]
  exact mul_nonneg (by norm_num) (hPSD _)

/-- The gap vanishes on the Legendre graph without a positivity assumption. -/
theorem quadraticFenchelGap_eq_zero_of_eq_mulVec {G GInv : Matrix n n ℝ}
    (hSymInv : GInvᵀ = GInv) (hInv : G * GInv = 1)
    (x y : n → ℝ) (hy : y = G *ᵥ x) :
    quadraticFenchelGap G GInv x y = 0 := by
  rw [quadraticFenchelGap_eq_residual hSymInv hInv, hy, sub_self]
  simp [quadForm]

/-- The dual quadratic is a greatest objective value, attained at `GInv *ᵥ y`.
This proves boundedness and attainment from the supplied inverse and PSD law. -/
theorem supplied_inverse_legendre_isGreatest {G GInv : Matrix n n ℝ}
    (hSymInv : GInvᵀ = GInv) (hInv : G * GInv = 1)
    (hPSD : ∀ z : n → ℝ, 0 ≤ quadForm GInv z) (y : n → ℝ) :
    IsGreatest (Set.range fun x : n → ℝ => x ⬝ᵥ y - (1 / 2) * quadForm G x)
      ((1 / 2) * quadForm GInv y) := by
  have hpoint : y = G *ᵥ (GInv *ᵥ y) := by
    rw [mulVec_mulVec, hInv, one_mulVec]
  refine ⟨⟨GInv *ᵥ y, ?_⟩, ?_⟩
  · have hgap := quadraticFenchelGap_eq_zero_of_eq_mulVec hSymInv hInv
      (GInv *ᵥ y) y hpoint
    unfold quadraticFenchelGap at hgap
    apply sub_eq_iff_eq_add.mpr
    exact (sub_eq_zero.mp hgap).symm.trans (add_comm _ _)
  · rintro _ ⟨x, rfl⟩
    have hgap := quadraticFenchelGap_nonneg hSymInv hInv hPSD x y
    unfold quadraticFenchelGap at hgap
    apply sub_le_iff_le_add.mpr
    simpa only [add_comm] using sub_nonneg.mp hgap

/-- The real-valued Fenchel supremum is the supplied inverse quadratic potential. -/
theorem supplied_inverse_legendre_csSup {G GInv : Matrix n n ℝ}
    (hSymInv : GInvᵀ = GInv) (hInv : G * GInv = 1)
    (hPSD : ∀ z : n → ℝ, 0 ≤ quadForm GInv z) (y : n → ℝ) :
    sSup (Set.range fun x : n → ℝ => x ⬝ᵥ y - (1 / 2) * quadForm G x) =
      (1 / 2) * quadForm GInv y :=
  (supplied_inverse_legendre_isGreatest hSymInv hInv hPSD y).csSup_eq

end InfoGeometry.OperatorAlgebra.OperatorDirichlet
