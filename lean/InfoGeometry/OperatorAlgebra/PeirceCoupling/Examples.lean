/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCoupling.Adjoint
import InfoGeometry.OperatorAlgebra.PeirceCoupling.Exactness

/-!
# Full noncommutative matrix witnesses

The first nondiagonal orthogonal projection has an adjoint coupling with a
nonzero but singular positive square. Reversing the adjoint's sign destroys
positivity. A second, balanced example satisfies the positive-definiteness
criterion. The ambient carrier throughout is the full algebra `Matrix (Fin 4)
(Fin 4) ℂ`, and genuine noncommutativity is proved explicitly.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling.Examples

open Matrix InfoGeometry.Core.PeirceDecomposition
open scoped ComplexOrder

noncomputable def projection : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1/2, 1/2, 0, 0; 1/2, 1/2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

def arrow : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 1; 0, 0, 1, 1; 0, 0, 0, 0; 0, 0, 0, 0]

def zeroMode : Fin 4 → ℂ := ![1, -1, 0, 0]

theorem projection_isStarProjection : IsStarProjection projection where
  isSelfAdjoint := by
    change projectionᴴ = projection
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [projection, conjTranspose_apply]
  isIdempotentElem := by
    change projection * projection = projection
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [projection, Matrix.mul_apply, Fin.sum_univ_succ]

theorem projection_nondiagonal : projection 0 1 ≠ 0 := by
  norm_num [projection]

theorem projection_mul_arrow : projection * arrow = arrow := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, arrow, Matrix.mul_apply, Fin.sum_univ_succ]

theorem arrow_mul_projection : arrow * projection = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, arrow, Matrix.mul_apply, Fin.sum_univ_succ]

theorem arrow_is_corner : component10 projection arrow = arrow := by
  rw [component10, complementIdempotent, projection_mul_arrow,
    mul_sub, mul_one, arrow_mul_projection, sub_zero]

theorem arrow_ne_zero : arrow ≠ 0 := by
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 2) h
  norm_num [arrow] at h02

theorem arrow_adjoint_noncommute : arrow * arrowᴴ ≠ arrowᴴ * arrow := by
  have h := adjoint_corners_commute_iff projection_isStarProjection arrow
  rw [arrow_is_corner] at h
  exact fun hc => arrow_ne_zero (h.mp hc)

theorem projection_arrow_noncommute : projection * arrow ≠ arrow * projection := by
  intro h
  exact arrow_ne_zero (by simpa only [projection_mul_arrow, arrow_mul_projection] using h)

theorem negative_adjoint_noncommute : ¬Commute arrow (-arrowᴴ) := by
  intro h
  apply arrow_adjoint_noncommute
  simpa only [mul_neg, neg_mul, neg_neg] using congrArg Neg.neg h.eq

theorem positive_square : (arrow * arrowᴴ + arrowᴴ * arrow).PosSemidef :=
  gramSum_posSemidef arrow

theorem square_nondiagonal : (arrow * arrowᴴ + arrowᴴ * arrow) 0 1 = 2 := by
  norm_num [arrow, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    conjTranspose_apply, Fin.sum_univ_succ]

theorem square_ne_zero : arrow * arrowᴴ + arrowᴴ * arrow ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 1) h
  rw [square_nondiagonal] at h01
  norm_num at h01

theorem zeroMode_ne_zero : zeroMode ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [zeroMode] at h0

theorem zeroMode_common_kernel : arrow *ᵥ zeroMode = 0 ∧ arrowᴴ *ᵥ zeroMode = 0 := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [arrow, zeroMode, Matrix.mulVec, dotProduct, conjTranspose_apply,
      Fin.sum_univ_succ]

theorem square_not_posDef : ¬(arrow * arrowᴴ + arrowᴴ * arrow).PosDef := by
  intro h
  exact zeroMode_ne_zero ((gramSum_posDef_iff arrow).mp h zeroMode zeroMode_common_kernel)

theorem square_not_isUnit : ¬IsUnit (arrow * arrowᴴ + arrowᴴ * arrow) := by
  intro h
  exact square_not_posDef ((gramSum_posDef_iff_isUnit arrow).mpr h)

/-- Changing only the independent reverse input to minus the adjoint gives a negative square. -/
theorem negative_coupling_square :
    (component10 projection arrow + component01 projection (-arrowᴴ)) ^ 2 =
      -(arrow * arrowᴴ + arrowᴴ * arrow) := by
  have hrev : component01 projection (-arrowᴴ) = -arrowᴴ := by
    calc
      _ = -(component01 projection arrowᴴ) := by simp [component01]
      _ = -arrowᴴ := by
        rw [adjoint_reverse_corner projection_isStarProjection arrow, arrow_is_corner]
  rw [opposite_sum_sq projection_isStarProjection.isIdempotentElem,
    arrow_is_corner, hrev]
  noncomm_ring

theorem negative_coupling_not_posSemidef :
    ¬((component10 projection arrow + component01 projection (-arrowᴴ)) ^ 2).PosSemidef := by
  rw [negative_coupling_square]
  intro h
  have h0 := h.diag_nonneg (i := (0 : Fin 4))
  norm_num [arrow, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    conjTranspose_apply, Fin.sum_univ_succ,
    Complex.le_def] at h0

def balancedArrow : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, -1, 1, -1; 1, -1, 1, -1; 0, 0, 2, -2; 0, 0, 2, -2]

theorem balancedArrow_sq_zero : balancedArrow * balancedArrow = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedArrow, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The criterion is inhabited on a nonzero full matrix algebra. -/
theorem balanced_posDef :
    (balancedArrow * balancedArrowᴴ + balancedArrowᴴ * balancedArrow).PosDef := by
  apply (gramSum_posDef_iff balancedArrow).mpr
  intro v hv
  have h0 := congrFun hv.1 0
  have h2 := congrFun hv.1 2
  have h0' := congrFun hv.2 0
  have h2' := congrFun hv.2 2
  norm_num [balancedArrow, Matrix.mulVec, dotProduct, conjTranspose_apply, map_ofNat,
    Fin.sum_univ_succ] at h0 h2 h0' h2'
  funext i
  fin_cases i
  · change v 0 = 0
    linear_combination (1 / 2 : ℂ) * h0 - (1 / 4 : ℂ) * h2 + (1 / 2 : ℂ) * h0'
  · change v 1 = 0
    linear_combination -(1 / 2 : ℂ) * h0 + (1 / 4 : ℂ) * h2 + (1 / 2 : ℂ) * h0'
  · change v 2 = 0
    linear_combination (1 / 4 : ℂ) * h2 + (1 / 4 : ℂ) * h2' - (1 / 4 : ℂ) * h0'
  · change v 3 = 0
    linear_combination -(1 / 4 : ℂ) * h2 + (1 / 4 : ℂ) * h2' - (1 / 4 : ℂ) * h0'

theorem balanced_exact : LinearMap.range balancedArrow.toEuclideanLin =
    LinearMap.ker balancedArrow.toEuclideanLin :=
  (gramSum_posDef_iff_exact balancedArrow balancedArrow_sq_zero).mp balanced_posDef

theorem balanced_adjoint_noncommute : ¬Commute balancedArrow balancedArrowᴴ := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h.eq
  norm_num [balancedArrow, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_succ] at h00

theorem balanced_square_nondiagonal :
    (balancedArrow * balancedArrowᴴ + balancedArrowᴴ * balancedArrow) 0 1 = 2 := by
  norm_num [balancedArrow, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    conjTranspose_apply, map_ofNat, Fin.sum_univ_succ]

end InfoGeometry.OperatorAlgebra.PeirceCoupling.Examples
