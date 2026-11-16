/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Sp4ContactPoles
import InfoGeometry.OperatorAlgebra.FiniteParityHeatSupertrace
import InfoGeometry.Canonical.SpinorialCore.FiniteIndex
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Contact supercharges with the same heat supertrace and different kernels

The endpoint sum is a nonzero self-adjoint odd full real 4-by-4 matrix. It is
its own Moore–Penrose inverse and has exactly the two-dimensional middle plane
as kernel. Adding the middle exchange gives an invertible odd self-adjoint
matrix. Both have identically zero balanced heat supertrace. Thus a vanishing
finite heat supertrace does not decide whether zero modes exist.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Sp4ContactSupertrace

open Matrix InfoGeometry.Algebra.Sp4Contact
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
open NormedSpace
open InfoGeometry.Canonical.SpinorialCore

/-- Balanced global chirality; it differs from the contact grading element. -/
def chiralitySign : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- The symmetric sum of the actual contact endpoints. -/
def endpointSupercharge : Mat := (zPlus : Mat) + (zMinus : Mat)

theorem endpointSupercharge_matrix :
    endpointSupercharge = !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0] := by
  rw [endpointSupercharge, zPlus_matrix, zMinus_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem endpointSupercharge_ne_zero : endpointSupercharge ≠ 0 := by
  intro h
  have h03 := congrArg (fun M : Mat => M 0 3) h
  norm_num [endpointSupercharge_matrix] at h03

theorem endpointSupercharge_star : star endpointSupercharge = endpointSupercharge := by
  rw [endpointSupercharge_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.star_apply]

theorem endpointSupercharge_odd : IsOdd chiralitySign endpointSupercharge := by
  rw [isOdd_iff_entries]
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralitySign, endpointSupercharge_matrix]

/-- The square is the proper endpoint support, not the full identity. -/
theorem endpointSupercharge_sq :
    endpointSupercharge * endpointSupercharge = activeSupport (zPlus : Mat) (zMinus : Mat) :=
  majoranaPlus_sq endpoints_moorePenrose zPlus_sq_zero

theorem endpointSupercharge_tripotent :
    endpointSupercharge * endpointSupercharge * endpointSupercharge = endpointSupercharge :=
  normalizedDirac_cube endpoints_moorePenrose zPlus_sq_zero

/-- A constructed four-equation generalized inverse, with the kernel retained. -/
theorem endpointSupercharge_moorePenrose :
    IsMoorePenroseInverse endpointSupercharge endpointSupercharge :=
  IsMoorePenroseInverse.selfAdjointTripotent_self_isMoorePenrose
    endpointSupercharge_tripotent endpointSupercharge_star

theorem endpointSupercharge_mulVec (v : Fin 4 → ℝ) :
    endpointSupercharge *ᵥ v = ![v 3, 0, 0, v 0] := by
  rw [endpointSupercharge_matrix]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The native kernel consists exactly of the two middle coordinates. -/
theorem mem_endpointSupercharge_ker (v : Fin 4 → ℝ) :
    v ∈ LinearMap.ker endpointSupercharge.mulVecLin ↔ v 0 = 0 ∧ v 3 = 0 := by
  change endpointSupercharge *ᵥ v = 0 ↔ _
  rw [endpointSupercharge_mulVec]
  constructor
  · intro h
    exact ⟨congrFun h 3, congrFun h 0⟩
  · rintro ⟨h0, h3⟩
    ext i
    fin_cases i <;> simp [h0, h3]

/-- Coordinates on the actual kernel, not an independently supplied count. -/
def endpointKernelEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] LinearMap.ker endpointSupercharge.mulVecLin where
  toFun x := ⟨![0, x 0, x 1, 0], (mem_endpointSupercharge_ker _).2 ⟨rfl, rfl⟩⟩
  invFun v := ![v.1 1, v.1 2]
  left_inv x := by
    ext i
    fin_cases i <;> rfl
  right_inv v := by
    apply Subtype.ext
    obtain ⟨h0, h3⟩ := (mem_endpointSupercharge_ker v.1).1 v.2
    ext i
    fin_cases i <;> simp [h0, h3]
  map_add' x y := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp

theorem endpointSupercharge_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker endpointSupercharge.mulVecLin) = 2 := by
  rw [← endpointKernelEquiv.finrank_eq]
  simp

/-- The existing harmonic support is exactly the projector onto this kernel. -/
theorem harmonicSupport_fixes_iff_kernel (v : Fin 4 → ℝ) :
    harmonicSupport (zPlus : Mat) (zMinus : Mat) *ᵥ v = v ↔
      v ∈ LinearMap.ker endpointSupercharge.mulVecLin := by
  rw [endpoint_harmonicSupport_matrix, mem_endpointSupercharge_ker]
  constructor
  · intro h
    constructor
    · have h0 := congrFun h 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h0.symm
    · have h3 := congrFun h 3
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h3.symm
  · rintro ⟨h0, h3⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h0, h3]

theorem chiralitySign_sq (i : Fin 4) : chiralitySign i ^ 2 = 1 := by
  fin_cases i <;> norm_num [chiralitySign]

theorem chirality_trace_zero : Matrix.trace (parityOperator chiralitySign) = 0 := by
  norm_num [parityOperator, chiralitySign, Matrix.trace, Fin.sum_univ_succ]

theorem endpointSupercharge_heat_supertrace (β : ℝ) :
    supertrace chiralitySign (exp ((-β) • endpointSupercharge ^ 2)) = 0 := by
  rw [supertrace_exp_smul_sq chiralitySign endpointSupercharge endpointSupercharge_odd,
    chirality_trace_zero]

/-- The actual positive-to-negative block of the endpoint supercharge. -/
def endpointChiralBlock : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

theorem endpointSupercharge_on_positive_sector (v : Fin 2 → ℝ) :
    endpointSupercharge *ᵥ ![v 0, v 1, 0, 0] =
      ![0, 0, (endpointChiralBlock *ᵥ v) 0, (endpointChiralBlock *ᵥ v) 1] := by
  rw [endpointSupercharge_mulVec]
  ext i
  fin_cases i <;>
    simp [endpointChiralBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The index uses the actual restricted block, including its native cokernel. -/
theorem endpointChiralBlock_index : finiteIndex endpointChiralBlock.mulVecLin = 0 := by
  rw [finiteIndex_eq_dimension_difference]
  simp

theorem endpoint_heat_supertrace_eq_chiral_index (β : ℝ) :
    supertrace chiralitySign (exp ((-β) • endpointSupercharge ^ 2)) =
      (finiteIndex endpointChiralBlock.mulVecLin : ℝ) := by
  rw [endpointSupercharge_heat_supertrace, endpointChiralBlock_index]
  norm_num

/-- Add the symmetric middle-plane exchange to fill the former kernel. -/
def invertibleSupercharge : Mat :=
  endpointSupercharge + (middleUpper : Mat) + (middleLower : Mat)

theorem invertibleSupercharge_matrix :
    invertibleSupercharge = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  rw [invertibleSupercharge, endpointSupercharge_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [middleUpper, middleLower, generator, matrixOfCoordinates, Pi.single_apply]

theorem invertibleSupercharge_ne_zero : invertibleSupercharge ≠ 0 := by
  intro h
  have h03 := congrArg (fun M : Mat => M 0 3) h
  norm_num [invertibleSupercharge_matrix] at h03

theorem invertibleSupercharge_star : star invertibleSupercharge = invertibleSupercharge := by
  rw [invertibleSupercharge_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.star_apply]

theorem invertibleSupercharge_odd : IsOdd chiralitySign invertibleSupercharge := by
  rw [isOdd_iff_entries]
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralitySign, invertibleSupercharge_matrix]

theorem invertibleSupercharge_sq : invertibleSupercharge * invertibleSupercharge = 1 := by
  rw [invertibleSupercharge_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

theorem invertibleSupercharge_ker : LinearMap.ker invertibleSupercharge.mulVecLin = ⊥ := by
  rw [Matrix.ker_mulVecLin_eq_bot_iff]
  intro v hv
  have h := congrArg (fun w => invertibleSupercharge *ᵥ w) hv
  rw [Matrix.mulVec_mulVec, invertibleSupercharge_sq] at h
  simpa using h

theorem invertibleSupercharge_heat_supertrace (β : ℝ) :
    supertrace chiralitySign (exp ((-β) • invertibleSupercharge ^ 2)) = 0 := by
  rw [supertrace_exp_smul_sq chiralitySign invertibleSupercharge invertibleSupercharge_odd,
    chirality_trace_zero]

/-- Two actual nonzero self-adjoint odd matrices have the same zero heat
supertrace, but one has a two-dimensional kernel and the other has none. -/
theorem zero_heat_supertrace_does_not_determine_kernel :
    ∃ Q₀ Q₁ : Mat,
      Q₀ ≠ 0 ∧ Q₁ ≠ 0 ∧ star Q₀ = Q₀ ∧ star Q₁ = Q₁ ∧
      IsOdd chiralitySign Q₀ ∧ IsOdd chiralitySign Q₁ ∧
      (∀ β : ℝ, supertrace chiralitySign (exp ((-β) • Q₀ ^ 2)) = 0 ∧
        supertrace chiralitySign (exp ((-β) • Q₁ ^ 2)) = 0) ∧
      Module.finrank ℝ (LinearMap.ker Q₀.mulVecLin) = 2 ∧
      LinearMap.ker Q₁.mulVecLin = ⊥ := by
  exact ⟨endpointSupercharge, invertibleSupercharge, endpointSupercharge_ne_zero,
    invertibleSupercharge_ne_zero, endpointSupercharge_star,
    invertibleSupercharge_star, endpointSupercharge_odd, invertibleSupercharge_odd,
    fun β => ⟨endpointSupercharge_heat_supertrace β, invertibleSupercharge_heat_supertrace β⟩,
    endpointSupercharge_kernel_finrank, invertibleSupercharge_ker⟩

end InfoGeometry.OperatorAlgebra.Sp4ContactSupertrace
