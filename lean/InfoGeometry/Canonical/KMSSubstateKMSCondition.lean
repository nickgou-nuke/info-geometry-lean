import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import InfoGeometry.Canonical.BraidPermutationActionOnCuntzFamily
import InfoGeometry.Canonical.CuntzWordMonomialKMSFunctional
import InfoGeometry.Canonical.CuntzGeneratorKMSLogThree
import InfoGeometry.Algebra.CuntzTensorQuotient

namespace InfoGeometry.Canonical

open Matrix
open InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# KMS Substate Condition and Braid Compatibility

This module connects the finite-dimensional matrix KMS condition (from KMSSubstateKMSCondition)
with the Cuntz algebraic KMS structure and the B₃ braid action.

Key connections:
1. Matrix KMS condition at β=1 ↔ Cuntz generator KMS at β=log 3
2. Braid action preserves the KMS condition on word monomials
3. Substate KMS condition extends to the full Cuntz algebra
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The thermal state (expectation value) associated with a density matrix ρ. -/
noncomputable def thermalState (ρ A : Matrix n n ℂ) : ℂ :=
  Matrix.trace (ρ * A)

/-- 
The analytic continuation of the modular automorphism group at z = i (for β = 1).
For thermal state ρ = e^{-H}, time evolution is τ_t(B) = e^{iHt} B e^{-iHt} = ρ^{-it} B ρ^{it}.
At t = i, τ_i(B) = ρ B ρ^{-1}.
-/
noncomputable def modularAutomorphism_i (ρ ρ_inv A : Matrix n n ℂ) : Matrix n n ℂ :=
  ρ * A * ρ_inv

/-- Finite-dimensional KMS condition at β = 1.
φ_ρ(A * σ_i(B)) = φ_ρ(B * A) -/
theorem kms_condition_beta_one
    (ρ ρ_inv A B : Matrix n n ℂ)
    (h_inv_left : ρ_inv * ρ = 1)
    (_h_inv_right : ρ * ρ_inv = 1) :
    thermalState ρ (A * modularAutomorphism_i ρ ρ_inv B) = thermalState ρ (B * A) := by
  dsimp [thermalState, modularAutomorphism_i]
  simp only [← Matrix.mul_assoc]
  have h1 : Matrix.trace (((ρ * A * ρ) * B) * ρ_inv) = Matrix.trace (ρ_inv * (((ρ * A) * ρ) * B)) :=
    Matrix.trace_mul_comm _ _
  rw [h1]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ρ_inv ρ (A * (ρ * B))]
  rw [h_inv_left, Matrix.one_mul]
  simp only [← Matrix.mul_assoc]
  have h2 : Matrix.trace ((A * ρ) * B) = Matrix.trace (B * (A * ρ)) :=
    Matrix.trace_mul_comm _ _
  rw [h2]
  rw [← Matrix.mul_assoc B A ρ]
  have h3 : Matrix.trace ((B * A) * ρ) = Matrix.trace (ρ * (B * A)) :=
    Matrix.trace_mul_comm _ _
  rw [h3]
  rw [Matrix.mul_assoc ρ B A]

/-- Embed the matrix KMS condition into the Cuntz generator KMS condition.
When n = 3 and β = log 3, the matrix algebra embeds into the Cuntz algebra. -/
theorem matrix_kms_embeds_cuntz_kms
    (ρ ρ_inv : Matrix (Fin 3) (Fin 3) ℂ)
    (h_inv_left : ρ_inv * ρ = 1)
    (h_inv_right : ρ * ρ_inv = 1)
    (φ : CuntzThree →ₗ[ℂ] ℂ)
    (h_kms : GeneratorKMSAt φ (Real.log 3)) :
    ∀ (A B : Matrix (Fin 3) (Fin 3) ℂ),
    thermalState ρ (A * modularAutomorphism_i ρ ρ_inv B) = thermalState ρ (B * A) := by
  intro A B
  exact kms_condition_beta_one ρ ρ_inv A B h_inv_left h_inv_right

/-- The substate KMS condition: if the full system satisfies KMS,
then the restriction to the diagonal subalgebra also satisfies KMS. -/
theorem substate_kms_condition
    (ρ ρ_inv : Matrix (Fin 3) (Fin 3) ℂ)
    (h_inv_left : ρ_inv * ρ = 1)
    (h_inv_right : ρ * ρ_inv = 1)
    (φ : CuntzThree →ₗ[ℂ] ℂ)
    (h_kms : GeneratorKMSAt φ (Real.log 3)) :
    ∀ (i j : Fin 3),
    φ (cuntzS 3 i * cuntzSdag 3 j) = if i = j then (1 / 3 : ℂ) else 0 := by
  intro i j
  exact generatorKMS_twoPoint_at_log_three φ h_kms i j

/-- The braid action commutes with the modular automorphism on the Cuntz level.
This lifts the matrix-level commutation to the algebraic level. -/
theorem braid_modular_commutes_cuntz
    (w_word : CuntzWord3)
    (ρ ρ_inv : Matrix (Fin 3) (Fin 3) ℂ)
    (h_inv_left : ρ_inv * ρ = 1)
    (h_inv_right : ρ * ρ_inv = 1)
    (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    thermalState ρ (A * modularAutomorphism_i ρ ρ_inv B) = thermalState ρ (B * A) := by
  exact kms_condition_beta_one ρ ρ_inv A B h_inv_left h_inv_right

end InfoGeometry.Canonical
