/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Lie.CartanTriality
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The first-coordinate convention for the existing Cartan triality matrices

The Hadamard matrix is the existing `trialitySwapVS`. A signed permutation
conjugates the owner's last-coordinate reflection to the first-coordinate
reflection. This transports the existing presentation and fixed submodule.
The resulting common fixed plane has an explicit native linear equivalence,
basis, and dimension, and the two nontrivial values of the cycle on the first
coordinate vector are recorded.

Orthogonality here is for the Euclidean coordinate pairing on `Fin 4 → ℝ`.
The presentation identities do not by themselves construct an action on a
Lie algebra, identify a fixed Lie subalgebra with G₂, or supply a symplectic
groupoid. Those require their respective maps and compatibility statements.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Lie.CartanTrialityFirstCoordinate

open Matrix
open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis
  (trialitySwapVS trialitySwapSpin trialityCycle3
   cartan_s3_triality_presentation s3FixedCartanSubmodule
   cartan_s3_fixed_subspace_iff s3FixedCartanEquiv finrank_s3FixedCartanSubmodule)

/-- The signed permutation `(v₀,v₁,v₂,v₃) ↦ (-v₃,v₁,v₂,-v₀)`. -/
def conventionChange : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, -1; 0, 1, 0, 0; 0, 0, 1, 0; -1, 0, 0, 0]

/-- The new convention reflects the first coordinate. -/
def firstCoordinateReflection : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- Apply the first-coordinate reflection, then the existing Hadamard swap. -/
def firstCoordinateCycle : Matrix (Fin 4) (Fin 4) ℝ :=
  trialitySwapVS * firstCoordinateReflection

theorem conventionChange_mulVec (v : Fin 4 → ℝ) :
    conventionChange.mulVec v = ![-v 3, v 1, v 2, -v 0] := by
  ext i
  fin_cases i <;>
    simp [conventionChange, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem conventionChange_sq : conventionChange * conventionChange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conventionChange, Matrix.mul_apply, Fin.sum_univ_four]

theorem conventionChange_transpose : conventionChangeᵀ = conventionChange := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem conventionChange_orthogonal : conventionChangeᵀ * conventionChange = 1 := by
  rw [conventionChange_transpose, conventionChange_sq]

theorem conventionChange_mul_swapVS :
    conventionChange * trialitySwapVS = trialitySwapVS * conventionChange := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conventionChange, trialitySwapVS, Matrix.mul_apply, Fin.sum_univ_four]

theorem conventionChange_mul_swapSpin :
    conventionChange * trialitySwapSpin =
      firstCoordinateReflection * conventionChange := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conventionChange, trialitySwapSpin, firstCoordinateReflection,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- The signed coordinate change preserves the Hadamard matrix itself. -/
theorem conventionChange_conjugates_swapVS :
    conventionChange * trialitySwapVS * conventionChange = trialitySwapVS := by
  rw [conventionChange_mul_swapVS, mul_assoc, conventionChange_sq, mul_one]

/-- The two reflection conventions are related by an actual conjugation. -/
theorem conventionChange_conjugates_swapSpin :
    conventionChange * trialitySwapSpin * conventionChange =
      firstCoordinateReflection := by
  rw [conventionChange_mul_swapSpin, mul_assoc, conventionChange_sq, mul_one]

theorem firstCoordinateCycle_eq_conjugate :
    firstCoordinateCycle = conventionChange * trialityCycle3 * conventionChange := by
  calc
    firstCoordinateCycle = trialitySwapVS *
        (conventionChange * trialitySwapSpin * conventionChange) := by
      simp only [conventionChange_conjugates_swapSpin, firstCoordinateCycle]
    _ = (trialitySwapVS * conventionChange) * trialitySwapSpin * conventionChange := by
      simp only [mul_assoc]
    _ = (conventionChange * trialitySwapVS) * trialitySwapSpin * conventionChange := by
      rw [conventionChange_mul_swapVS]
    _ = conventionChange * trialityCycle3 * conventionChange := by
      simp only [trialityCycle3, mul_assoc]

private theorem conjugate_mul (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    (conventionChange * A * conventionChange) *
        (conventionChange * B * conventionChange) =
      conventionChange * (A * B) * conventionChange := by
  calc
    _ = (conventionChange * A) * (conventionChange * conventionChange) *
        (B * conventionChange) := by simp only [mul_assoc]
    _ = _ := by rw [conventionChange_sq]; simp only [mul_one, mul_assoc]

private theorem conjugate_involutive (A : Matrix (Fin 4) (Fin 4) ℝ) :
    conventionChange * (conventionChange * A * conventionChange) * conventionChange =
      A := by
  calc
    _ = (conventionChange * conventionChange) * A *
        (conventionChange * conventionChange) := by simp only [mul_assoc]
    _ = _ := by rw [conventionChange_sq]; simp

private theorem conjugate_pow (A : Matrix (Fin 4) (Fin 4) ℝ) (n : ℕ) :
    (conventionChange * A * conventionChange) ^ n =
      conventionChange * A ^ n * conventionChange := by
  induction n with
  | zero => simp only [pow_zero, mul_one, conventionChange_sq]
  | succ n ih => rw [pow_succ, ih, conjugate_mul, pow_succ]

/-- The new reflection's involution law is transported from the original owner. -/
theorem firstCoordinateReflection_sq :
    firstCoordinateReflection * firstCoordinateReflection = 1 := by
  calc
    _ = (conventionChange * trialitySwapSpin * conventionChange) *
        (conventionChange * trialitySwapSpin * conventionChange) := by
      rw [conventionChange_conjugates_swapSpin]
    _ = conventionChange * (trialitySwapSpin * trialitySwapSpin) * conventionChange :=
      conjugate_mul _ _
    _ = 1 := by
      rw [cartan_s3_triality_presentation.2.1, mul_one, conventionChange_sq]

/-- The order-three relation is inherited by conjugation. -/
theorem firstCoordinateCycle_pow_three : firstCoordinateCycle ^ 3 = 1 := by
  rw [firstCoordinateCycle_eq_conjugate, conjugate_pow,
    cartan_s3_triality_presentation.2.2.1, mul_one, conventionChange_sq]

theorem firstCoordinateCycle_ne_one : firstCoordinateCycle ≠ 1 := by
  intro h
  have h' := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ =>
    conventionChange * A * conventionChange) h
  rw [firstCoordinateCycle_eq_conjugate, conjugate_involutive] at h'
  apply cartan_s3_triality_presentation.2.2.2.1
  simpa only [mul_one, conventionChange_sq] using h'

/-- The reflection conjugates the cycle to its square in the new convention. -/
theorem firstCoordinateReflection_cycle_reflection :
    firstCoordinateReflection * firstCoordinateCycle * firstCoordinateReflection =
      firstCoordinateCycle ^ 2 := by
  calc
    _ = (conventionChange * trialitySwapSpin * conventionChange) *
        (conventionChange * trialityCycle3 * conventionChange) *
        (conventionChange * trialitySwapSpin * conventionChange) := by
      rw [conventionChange_conjugates_swapSpin, ← firstCoordinateCycle_eq_conjugate]
    _ = conventionChange * (trialitySwapSpin * trialityCycle3 * trialitySwapSpin) *
        conventionChange := by rw [conjugate_mul, conjugate_mul]
    _ = conventionChange * trialityCycle3 ^ 2 * conventionChange := by
      rw [cartan_s3_triality_presentation.2.2.2.2]
    _ = (conventionChange * trialityCycle3 * conventionChange) ^ 2 :=
      (conjugate_pow _ _).symm
    _ = firstCoordinateCycle ^ 2 := by rw [← firstCoordinateCycle_eq_conjugate]

theorem swapVS_transpose : trialitySwapVSᵀ = trialitySwapVS := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem swapVS_orthogonal : trialitySwapVSᵀ * trialitySwapVS = 1 := by
  rw [swapVS_transpose]
  exact cartan_s3_triality_presentation.1

theorem firstCoordinateReflection_transpose :
    firstCoordinateReflectionᵀ = firstCoordinateReflection := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem firstCoordinateReflection_orthogonal :
    firstCoordinateReflectionᵀ * firstCoordinateReflection = 1 := by
  rw [firstCoordinateReflection_transpose, firstCoordinateReflection_sq]

theorem firstCoordinateCycle_orthogonal :
    firstCoordinateCycleᵀ * firstCoordinateCycle = 1 := by
  unfold firstCoordinateCycle
  rw [Matrix.transpose_mul, firstCoordinateReflection_transpose, swapVS_transpose]
  calc
    _ = firstCoordinateReflection * (trialitySwapVS * trialitySwapVS) *
        firstCoordinateReflection := by simp only [mul_assoc]
    _ = 1 := by
      rw [cartan_s3_triality_presentation.1, mul_one, firstCoordinateReflection_sq]

/-- The signed coordinate matrix as a native real linear equivalence. -/
def conventionChangeEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := conventionChange.mulVec
  invFun := conventionChange.mulVec
  left_inv v := by rw [Matrix.mulVec_mulVec, conventionChange_sq, Matrix.one_mulVec]
  right_inv v := by rw [Matrix.mulVec_mulVec, conventionChange_sq, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _

/-- The actual common fixed submodule for the first-coordinate convention. -/
def firstFixedCartanSubmodule : Submodule ℝ (Fin 4 → ℝ) where
  carrier := {v | trialitySwapVS.mulVec v = v ∧ firstCoordinateReflection.mulVec v = v}
  zero_mem' := ⟨Matrix.mulVec_zero _, Matrix.mulVec_zero _⟩
  add_mem' {u v} hu hv :=
    ⟨by rw [Matrix.mulVec_add, hu.1, hv.1], by rw [Matrix.mulVec_add, hu.2, hv.2]⟩
  smul_mem' r v hv :=
    ⟨by rw [Matrix.mulVec_smul, hv.1], by rw [Matrix.mulVec_smul, hv.2]⟩

private theorem swapVS_change_mulVec (v : Fin 4 → ℝ) :
    trialitySwapVS.mulVec (conventionChange.mulVec v) =
      conventionChange.mulVec (trialitySwapVS.mulVec v) := by
  simp only [Matrix.mulVec_mulVec]
  rw [conventionChange_mul_swapVS]

private theorem reflection_change_mulVec (v : Fin 4 → ℝ) :
    firstCoordinateReflection.mulVec (conventionChange.mulVec v) =
      conventionChange.mulVec (trialitySwapSpin.mulVec v) := by
  simp only [Matrix.mulVec_mulVec]
  rw [conventionChange_mul_swapSpin]

/-- Common fixed vectors are transported by the signed coordinate change. -/
theorem conventionChange_mem_fixed_iff (v : Fin 4 → ℝ) :
    conventionChange.mulVec v ∈ firstFixedCartanSubmodule ↔
      v ∈ s3FixedCartanSubmodule := by
  change (trialitySwapVS.mulVec (conventionChange.mulVec v) = conventionChange.mulVec v ∧
    firstCoordinateReflection.mulVec (conventionChange.mulVec v) =
      conventionChange.mulVec v) ↔
    (trialitySwapVS.mulVec v = v ∧ trialitySwapSpin.mulVec v = v)
  rw [swapVS_change_mulVec, reflection_change_mulVec]
  constructor
  · rintro ⟨hM, hS⟩
    exact ⟨conventionChangeEquiv.injective hM, conventionChangeEquiv.injective hS⟩
  · rintro ⟨hM, hS⟩
    rw [hM, hS]
    exact ⟨rfl, rfl⟩

theorem firstFixedCartanSubmodule_iff (v : Fin 4 → ℝ) :
    v ∈ firstFixedCartanSubmodule ↔ (v 0 = 0 ∧ v 1 + v 2 + v 3 = 0) := by
  have h := conventionChange_mem_fixed_iff (conventionChange.mulVec v)
  simp only [Matrix.mulVec_mulVec, conventionChange_sq, Matrix.one_mulVec] at h
  rw [h, cartan_s3_fixed_subspace_iff]
  simp only [conventionChange_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, neg_eq_zero]
  constructor
  · rintro ⟨h0, hsum⟩
    exact ⟨h0, by linarith⟩
  · rintro ⟨h0, hsum⟩
    exact ⟨h0, by linarith⟩

theorem conventionChange_map_fixed :
    s3FixedCartanSubmodule.map conventionChangeEquiv.toLinearMap =
      firstFixedCartanSubmodule := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (conventionChange_mem_fixed_iff w).mpr hw
  · intro hv
    refine ⟨conventionChangeEquiv.symm v, ?_, conventionChangeEquiv.apply_symm_apply v⟩
    apply (conventionChange_mem_fixed_iff _).mp
    change conventionChangeEquiv (conventionChangeEquiv.symm v) ∈ firstFixedCartanSubmodule
    simpa only [LinearEquiv.apply_symm_apply] using hv

/-- Restrict the actual coordinate equivalence to the two common fixed submodules. -/
def fixedCartanTransport : s3FixedCartanSubmodule ≃ₗ[ℝ] firstFixedCartanSubmodule :=
  conventionChangeEquiv.ofSubmodules _ _ conventionChange_map_fixed

/-- Transport the owner's existing two-parameter equivalence. -/
def firstFixedCartanEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] firstFixedCartanSubmodule :=
  s3FixedCartanEquiv.trans fixedCartanTransport

theorem firstFixedCartanEquiv_apply (p : Fin 2 → ℝ) :
    (firstFixedCartanEquiv p : Fin 4 → ℝ) = ![0, p 0, p 1, -(p 0 + p 1)] := by
  change conventionChange.mulVec ![p 0 + p 1, p 0, p 1, 0] = _
  rw [conventionChange_mulVec]
  simp

/-- The transported coordinate basis is a genuine basis of the common fixed plane. -/
def firstFixedCartanBasis : Module.Basis (Fin 2) ℝ firstFixedCartanSubmodule :=
  (Pi.basisFun ℝ (Fin 2)).map firstFixedCartanEquiv

theorem firstFixedCartanBasis_zero :
    (firstFixedCartanBasis 0 : Fin 4 → ℝ) = ![0, 1, 0, -1] := by
  change (firstFixedCartanEquiv ((Pi.basisFun ℝ (Fin 2)) 0) : Fin 4 → ℝ) = _
  rw [firstFixedCartanEquiv_apply]
  simp [Pi.basisFun_apply]

theorem firstFixedCartanBasis_one :
    (firstFixedCartanBasis 1 : Fin 4 → ℝ) = ![0, 0, 1, -1] := by
  change (firstFixedCartanEquiv ((Pi.basisFun ℝ (Fin 2)) 1) : Fin 4 → ℝ) = _
  rw [firstFixedCartanEquiv_apply]
  simp [Pi.basisFun_apply]

theorem finrank_firstFixedCartanSubmodule :
    Module.finrank ℝ firstFixedCartanSubmodule = 2 := by
  rw [← fixedCartanTransport.finrank_eq]
  exact finrank_s3FixedCartanSubmodule

/-- First nontrivial value of the cycle on the first coordinate vector. -/
theorem firstCoordinateCycle_e0 :
    firstCoordinateCycle.mulVec ![1, 0, 0, 0] =
      ![-(1 / 2), -(1 / 2), -(1 / 2), -(1 / 2)] := by
  change (trialitySwapVS * firstCoordinateReflection).mulVec _ = _
  rw [← Matrix.mulVec_mulVec]
  ext i
  fin_cases i <;>
    norm_num [trialitySwapVS, firstCoordinateReflection, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four]

/-- Second nontrivial value, with the sign forced by `C = M * S`. -/
theorem firstCoordinateCycle_sq_e0 :
    (firstCoordinateCycle ^ 2).mulVec ![1, 0, 0, 0] =
      ![-(1 / 2), 1 / 2, 1 / 2, 1 / 2] := by
  rw [pow_two, ← Matrix.mulVec_mulVec, firstCoordinateCycle_e0]
  change (trialitySwapVS * firstCoordinateReflection).mulVec _ = _
  rw [← Matrix.mulVec_mulVec]
  ext i
  fin_cases i <;>
    norm_num [trialitySwapVS, firstCoordinateReflection, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four]

/-- The square is nonidentity, witnessed on the actual first coordinate vector. -/
theorem firstCoordinateCycle_sq_ne_one : firstCoordinateCycle ^ 2 ≠ 1 := by
  intro h
  have h0 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ =>
    (A.mulVec (![1, 0, 0, 0] : Fin 4 → ℝ)) 0) h
  simp only [firstCoordinateCycle_sq_e0, Matrix.one_mulVec, Matrix.cons_val_zero] at h0
  norm_num at h0

end InfoGeometry.Lie.CartanTrialityFirstCoordinate

end
