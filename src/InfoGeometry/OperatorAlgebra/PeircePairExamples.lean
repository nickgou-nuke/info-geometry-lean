/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.OperatorExtensionExamples
import InfoGeometry.OperatorAlgebra.PeircePairPositivity

/-!
# Noncommuting witnesses for opposite-corner geometry

All operators act on the full three-dimensional complex space. The existing
nondiagonal star projections give a nonzero nonscalar bracket and a nontrivial
joint kernel. Changing the sign of the reverse input preserves noncommutation
but makes the mixed square fail positive semidefiniteness.
-/

namespace InfoGeometry.OperatorAlgebra.PeircePairExamples

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.IdempotentCartan
open PeirceChiralGeometry PeircePairGeometry PeircePairPositivity OperatorExtensionExamples
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ

/-- The directed constituents themselves fail to commute. -/
theorem opposite_corners_not_commute :
    ¬ Commute (component10 P Q) (component01 P Q) := by
  apply (pair_jordan_ne_zero_iff_not_commute P_isStarProjection.isIdempotentElem Q Q).mp
  rw [← odd_square_eq_cross_products P_isStarProjection.isIdempotentElem Q]
  exact chiral_square_ne_zero

/-- A nonzero off-diagonal entry of the bracket, proved by exact matrix arithmetic. -/
theorem pair_lie_off_diagonal_ne_zero :
    (⁅component10 P Q, component01 P Q⁆ : Mat) 0 1 ≠ 0 := by
  rw [← reflection_mul_pair_jordan P_isStarProjection.isIdempotentElem Q Q,
    ← odd_square_eq_cross_products P_isStarProjection.isIdempotentElem Q,
    chiral_square_matrix]
  norm_num [reflection, two_nsmul, P, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

theorem pair_lie_not_scalar (z : ℂ) :
    (⁅component10 P Q, component01 P Q⁆ : Mat) ≠ z • (1 : Mat) := by
  intro h
  apply pair_lie_off_diagonal_ne_zero
  have he := congrArg (fun A : Mat => A 0 1) h
  simpa using he

/-- The same noncommuting projections yield a nonzero common kernel for both corner actions. -/
theorem positive_pair_joint_kernel :
    component10 P Q *ᵥ (![2, 2, -3] : Fin 3 → ℂ) = 0 ∧
      star (component10 P Q) *ᵥ (![2, 2, -3] : Fin 3 → ℂ) = 0 := by
  apply (adjoint_pair_mulVec_eq_zero_iff P_isStarProjection Q _).mp
  rw [Q_isStarProjection.isSelfAdjoint.star_eq,
    ← odd_square_eq_cross_products P_isStarProjection.isIdempotentElem Q]
  exact chiral_square_kernel

/-- Without adjoint pairing, the mixed square can be the negative of a nonzero Gram sum. -/
theorem negative_pair_square :
    (component10 P Q + component01 P (-Q)) *
        (component10 P Q + component01 P (-Q)) =
      -(oddPart P Q * oddPart P Q) := by
  rw [pair_square P_isStarProjection.isIdempotentElem Q (-Q)]
  have hv : component01 P (-Q) = -component01 P Q := by
    simp only [component01, mul_neg, neg_mul]
  rw [hv, mul_neg, neg_mul, ← neg_add,
    ← odd_square_eq_cross_products P_isStarProjection.isIdempotentElem Q]

theorem negative_pair_not_commute :
    ¬ Commute (component10 P Q) (component01 P (-Q)) := by
  apply (pair_jordan_ne_zero_iff_not_commute P_isStarProjection.isIdempotentElem Q (-Q)).mp
  rw [← pair_square P_isStarProjection.isIdempotentElem Q (-Q), negative_pair_square]
  exact neg_ne_zero.mpr chiral_square_ne_zero

/-- Unconditional positivity fails inside the same full noncommutative matrix algebra. -/
theorem negative_pair_not_posSemidef :
    ¬ ((component10 P Q + component01 P (-Q)) *
      (component10 P Q + component01 P (-Q))).PosSemidef := by
  rw [negative_pair_square]
  intro h
  have hdiag : 0 ≤ (-(oddPart P Q * oddPart P Q) : Mat) 0 0 := h.diag_nonneg
  rw [chiral_square_matrix] at hdiag
  have hre := (Complex.nonneg_iff.mp hdiag).1
  norm_num at hre

end InfoGeometry.OperatorAlgebra.PeircePairExamples
