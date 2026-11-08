/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanBoundaryOperators
import InfoGeometry.Canonical.PeirceBoundaryComplex
import InfoGeometry.Canonical.LieJordanSandwichGeometry
import InfoGeometry.Canonical.PeirceCouplingExamples

/-!
# Dense matrix witnesses for exact boundary-operator hypotheses

The full matrix space and the dense P,S,U from the earlier owners are retained.
Ordinary Lie/Jordan squares, generator-swapped compositions, ambient centrality,
and unnormalized tripotency have explicit nonzero obstructions. The genuine
graded differential is nonzero and square-zero on this same matrix algebra.
-/

namespace InfoGeometry.Canonical.LieJordanBoundaryExamples

open Matrix
open scoped ComplexOrder
open Core.PeirceDecomposition Core.PeirceGrading Core.PeirceCoupledCorners
open Core.JordanMultiplicationClosure Core.LieJordanBoundaryOperators
open LieJordanMatrixExamples PeirceCouplingExamples PeirceCouplingPositivity
open LieJordanSandwichGeometry PeirceBoundaryComplex

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

theorem U_mul_U_eq_zero : U * U = 0 :=
  peirce10_mul_peirce10_eq_zero P P_isStarProjection.isIdempotentElem.eq
    U_mem_peirce10 U_mem_peirce10

theorem U_adj_mem_odd : Uᴴ ∈ LinearMap.range (odd P) := by
  rw [mem_odd_iff P_isStarProjection.isIdempotentElem]
  have hv := adjoint_mem_peirce01 P_isStarProjection U_mem_peirce10
  rw [left_support01 P_isStarProjection.isIdempotentElem hv,
    right_support01 P_isStarProjection.isIdempotentElem hv, zero_add]

theorem U_mul_adj_mul_U_entry : (U * Uᴴ * U) 0 0 = -1274 / 81 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  norm_num [U_apply, Fin.sum_univ_succ, map_ofNat]

/-- The ordinary adjoint square is nonzero even on an actual odd input. -/
theorem ad_U_sq_apply_adj_entry :
    ((LieAlgebra.ad ℂ Mat3 U ^ 2) Uᴴ) 0 0 = 2548 / 81 := by
  rw [ad_sq_of_sq_zero (R := ℂ) U_mul_U_eq_zero, two_nsmul]
  change -((U * Uᴴ * U) 0 0 + (U * Uᴴ * U) 0 0) = _
  rw [U_mul_adj_mul_U_entry]
  norm_num

theorem jordan_U_sq_apply_adj_entry :
    ((jordanLeft (R := ℂ) U ^ 2) Uᴴ) 0 0 = -2548 / 81 := by
  rw [jordan_sq_of_sq_zero (R := ℂ) U_mul_U_eq_zero, two_nsmul]
  change (U * Uᴴ * U) 0 0 + (U * Uᴴ * U) 0 0 = _
  rw [U_mul_adj_mul_U_entry]
  norm_num

theorem ad_U_sq_ne_zero : LieAlgebra.ad ℂ Mat3 U ^ 2 ≠ 0 := by
  intro h
  have he := congrArg (fun f : Module.End ℂ Mat3 => (f Uᴴ) 0 0) h
  rw [ad_U_sq_apply_adj_entry] at he
  norm_num at he

theorem jordan_U_sq_ne_zero : jordanLeft (R := ℂ) U ^ 2 ≠ 0 := by
  intro h
  have he := congrArg (fun f : Module.End ℂ Mat3 => (f Uᴴ) 0 0) h
  rw [jordan_U_sq_apply_adj_entry] at he
  norm_num at he

/-- The omitted mixed-composition correction is nonzero at the dense projection. -/
theorem swapped_mixed_defect_entry :
    (((LieAlgebra.ad ℂ Mat3 U * jordanLeft (R := ℂ) Uᴴ -
      LieAlgebra.ad ℂ Mat3 Uᴴ * jordanLeft (R := ℂ) U) -
        jordanLeft (R := ℂ) ⁅U, Uᴴ⁆) P) 0 0 = -338 / 27 := by
  rw [ad_mul_jordan_sub, add_sub_cancel_left, two_nsmul]
  change (U * P * Uᴴ - Uᴴ * P * U) 0 0 +
    (U * P * Uᴴ - Uᴴ * P * U) 0 0 = _
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  norm_num [U_apply, P, Fin.sum_univ_succ, map_ofNat]

theorem swapped_mixed_difference_ne :
    LieAlgebra.ad ℂ Mat3 U * jordanLeft (R := ℂ) Uᴴ -
      LieAlgebra.ad ℂ Mat3 Uᴴ * jordanLeft (R := ℂ) U ≠
        jordanLeft (R := ℂ) ⁅U, Uᴴ⁆ := by
  intro h
  have hz := sub_eq_zero.mpr h
  have he := congrArg (fun f : Module.End ℂ Mat3 => (f P) 0 0) hz
  rw [swapped_mixed_defect_entry] at he
  norm_num at he

theorem gram_S_bracket_entry :
    (⁅U * Uᴴ + Uᴴ * U, S⁆ : Mat3) 0 1 = -13 / 9 := by
  change ((U * Uᴴ + Uᴴ * U) * S - S * (U * Uᴴ + Uᴴ * U)) 0 1 = _
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  norm_num [U_apply, S, Fin.sum_univ_succ, map_ofNat]

/-- Commutation with the generated corner algebra does not imply ambient centrality. -/
theorem gram_not_commute_S : ¬ Commute (U * Uᴴ + Uᴴ * U) S := by
  intro h
  have hz : (⁅U * Uᴴ + Uᴴ * U, S⁆ : Mat3) = 0 := sub_eq_zero.mpr h.eq
  have he := congrArg (fun x : Mat3 => x 0 1) hz
  rw [gram_S_bracket_entry] at he
  norm_num at he

theorem coupled_cube_defect_entry :
    ((U + Uᴴ) ^ 3 - (U + Uᴴ)) 0 0 = -2314 / 81 := by
  simp only [pow_succ, pow_zero, Matrix.sub_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  norm_num [U_apply, Fin.sum_univ_succ, map_ofNat]

theorem coupled_not_tripotent : (U + Uᴴ) ^ 3 ≠ U + Uᴴ := by
  intro h
  have he := congrArg (fun x : Mat3 => x 0 0) (sub_eq_zero.mpr h)
  rw [coupled_cube_defect_entry] at he
  norm_num at he

theorem P_posSemidef : P.PosSemidef := by
  have hs : Pᴴ = P := P_isStarProjection.isSelfAdjoint.star_eq
  simpa only [hs, P_isStarProjection.isIdempotentElem.eq] using
    Matrix.posSemidef_self_mul_conjTranspose P

theorem independent_sandwich_trace_P :
    trace (U * P * (-Uᴴ) + (-Uᴴ) * P * U) = -98 / 9 := by
  rw [trace_sandwich_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.add_apply,
    Matrix.neg_apply, Matrix.conjTranspose_apply]
  norm_num [U_apply, P, Fin.sum_univ_succ, map_ofNat]

/-- Independent opposite inputs can fail positivity even at a positive projection. -/
theorem independent_sandwich_P_not_posSemidef :
    ¬ (U * P * (-Uᴴ) + (-Uᴴ) * P * U).PosSemidef := by
  intro h
  have ht := (Complex.nonneg_iff.mp h.trace_nonneg).1
  rw [independent_sandwich_trace_P] at ht
  norm_num at ht

theorem graded_U_ne_zero : differential (R := ℂ) P U ≠ 0 :=
  differential_ne_zero P_isStarProjection.isIdempotentElem U_mem_peirce10 U_ne_zero

theorem graded_U_sq_zero : differential (R := ℂ) P U ^ 2 = 0 :=
  differential_sq_zero_of_mem_peirce10 P_isStarProjection.isIdempotentElem U_mem_peirce10

end

end InfoGeometry.Canonical.LieJordanBoundaryExamples
