/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceCouplingPositivity
import InfoGeometry.Canonical.LieJordanMatrixExamples

/-!
# Noncommuting coupled corners with and without positivity

The existing dense three-dimensional matrices supply a nondiagonal star
projection and a nonzero directed corner. Its adjoint-paired square is positive
semidefinite with positive trace, but has an explicit nonzero kernel vector.
Changing the independent opposite input to its negative gives a nonzero square
that is not positive semidefinite. Both pairs have nonzero commutators.
-/

namespace InfoGeometry.Canonical.PeirceCouplingExamples

open scoped Matrix ComplexOrder
open Core.PeirceDecomposition Core.PeirceCoupledCorners
open LieJordanMatrixExamples PeirceCouplingGeometry PeirceCouplingPositivity

noncomputable section

/-- A genuine directed corner of the existing dense full matrices. -/
def U : Mat3 := component10 P S

/-- A vector orthogonal to both corner supports in this example. -/
def kernelVector : Fin 3 → ℂ := ![3, -8, 5]

theorem U_mem_peirce10 : U ∈ peirce10 P := component10_mem P S

theorem U_apply (i j : Fin 3) :
    U i j = (![-13 / 9, 2 / 9, 11 / 9] : Fin 3 → ℂ) j := by
  fin_cases i <;> fin_cases j <;>
    simp only [U, component10, complementIdempotent, Matrix.mul_apply, Matrix.sub_apply] <;>
    norm_num [P, S, Fin.sum_univ_succ, Matrix.one_apply]

theorem U_ne_zero : U ≠ 0 := by
  intro h
  have he := congrArg (fun m : Mat3 => m 0 0) h
  rw [U_apply] at he
  norm_num at he

theorem U_adj_eq_component01 : Uᴴ = component01 P S := by
  change star (component10 P S) = component01 P S
  rw [star_component10 P_isStarProjection.isSelfAdjoint, S_isSelfAdjoint.star_eq]

/-- The actual opposite corner operators do not commute. -/
theorem U_mul_adj_ne_adj_mul_U : U * Uᴴ ≠ Uᴴ * U := by
  intro h
  apply U_ne_zero
  apply (bracket_eq_zero_iff P_isStarProjection U_mem_peirce10).mp
  exact sub_eq_zero.mpr h

theorem U_gram_trace : Matrix.trace (U * Uᴴ + Uᴴ * U) = 196 / 9 := by
  norm_num [Matrix.trace_add, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, U_apply, Fin.sum_univ_succ, map_ofNat]

theorem U_gram_posSemidef : (U * Uᴴ + Uᴴ * U).PosSemidef := gram_posSemidef U

theorem U_gram_ne_zero : U * Uᴴ + Uᴴ * U ≠ 0 := by
  exact fun h => U_ne_zero ((gram_eq_zero_iff P_isStarProjection U_mem_peirce10).mp h)

theorem kernelVector_ne_zero : kernelVector ≠ 0 := by
  intro h
  have he := congrArg (fun x : Fin 3 → ℂ => x 0) h
  norm_num [kernelVector] at he

theorem U_mulVec_kernelVector : U *ᵥ kernelVector = 0 := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, U_apply, kernelVector, Fin.sum_univ_succ]

theorem U_adj_mulVec_kernelVector : Uᴴ *ᵥ kernelVector = 0 := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      U_apply, kernelVector, Fin.sum_univ_succ]

theorem kernelVector_mem_common_kernel :
    kernelVector ∈ LinearMap.ker U.mulVecLin ⊓ LinearMap.ker Uᴴ.mulVecLin := by
  simp only [Submodule.mem_inf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact ⟨U_mulVec_kernelVector, U_adj_mulVec_kernelVector⟩

theorem U_gram_mulVec_kernelVector : (U * Uᴴ + Uᴴ * U) *ᵥ kernelVector = 0 := by
  change kernelVector ∈ LinearMap.ker (U * Uᴴ + Uᴴ * U).mulVecLin
  rw [gram_kernel P_isStarProjection U_mem_peirce10]
  exact kernelVector_mem_common_kernel

/-- Positive trace and nonzero positive coupling do not remove all zero modes. -/
theorem U_gram_not_posDef : ¬ (U * Uᴴ + Uᴴ * U).PosDef := by
  intro h
  have hker := (gram_posDef_iff P_isStarProjection U_mem_peirce10).mp h
  have hx := kernelVector_mem_common_kernel
  rw [hker] at hx
  exact kernelVector_ne_zero (by simpa only [Submodule.mem_bot] using hx)

theorem negative_input_corner_eq : component01 P (-S) = -Uᴴ := by
  rw [U_adj_eq_component01]
  simp only [component01, mul_neg, neg_mul]

theorem negative_coupled_square :
    (U + component01 P (-S)) ^ 2 = -(U * Uᴴ + Uᴴ * U) := by
  rw [coupled_square P_isStarProjection.isIdempotentElem
    U_mem_peirce10 (component01_mem P (-S)), negative_input_corner_eq]
  simp only [mul_neg, neg_mul, neg_add]

theorem negative_coupled_trace :
    Matrix.trace ((U + component01 P (-S)) ^ 2) = -196 / 9 := by
  rw [negative_coupled_square, Matrix.trace_neg, U_gram_trace]
  norm_num

theorem negative_coupled_square_ne_zero : (U + component01 P (-S)) ^ 2 ≠ 0 := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [negative_coupled_trace, Matrix.trace_zero] at ht
  norm_num at ht

/-- Independent opposite inputs need not give a positive semidefinite square. -/
theorem negative_coupled_square_not_posSemidef :
    ¬ ((U + component01 P (-S)) ^ 2).PosSemidef := by
  intro h
  have ht := (Complex.nonneg_iff.mp h.trace_nonneg).1
  rw [negative_coupled_trace] at ht
  norm_num at ht

theorem U_mul_negative_ne_negative_mul_U :
    U * component01 P (-S) ≠ component01 P (-S) * U := by
  rw [negative_input_corner_eq, mul_neg, neg_mul]
  exact fun h => U_mul_adj_ne_adj_mul_U (neg_injective h)

end

end InfoGeometry.Canonical.PeirceCouplingExamples
