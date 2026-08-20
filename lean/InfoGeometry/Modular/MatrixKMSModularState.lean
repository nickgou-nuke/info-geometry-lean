import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.Modular.KMS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "Mat" => Matrix ι ι R

/-- The Linear Expectation Functional of a Density Matrix ρ: ω_ρ(A) = Tr(ρ * A). -/
def expectation (ρ A : Mat) : R :=
  Matrix.trace (ρ * A)

/-- Normalization of the trace functional: ω_ρ(1) = Tr(ρ). -/
@[simp]
theorem expectation_one (ρ : Mat) : expectation ρ 1 = Matrix.trace ρ := by
  dsimp [expectation]
  rw [mul_one]

/-- Linearity: ω_ρ(A + B) = ω_ρ(A) + ω_ρ(B). -/
theorem expectation_add (ρ A B : Mat) :
    expectation ρ (A + B) = expectation ρ A + expectation ρ B := by
  dsimp [expectation]
  rw [mul_add, Matrix.trace_add]

@[simp]
theorem expectation_zero (ρ : Mat) : expectation ρ 0 = 0 := by
  dsimp [expectation]
  simp

theorem expectation_smul (ρ A : Mat) (r : R) :
    expectation ρ (r • A) = r • expectation ρ A := by
  dsimp [expectation]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]

theorem expectation_sub (ρ A B : Mat) :
    expectation ρ (A - B) = expectation ρ A - expectation ρ B := by
  dsimp [expectation]
  rw [mul_sub, Matrix.trace_sub]

/-- The finite expectation functional bundled as an `R`-linear map. -/
def expectationLinear (ρ : Mat) : Mat →ₗ[R] R where
  toFun := expectation ρ
  map_add' A B := expectation_add ρ A B
  map_smul' r A := by
    simpa [smul_eq_mul] using expectation_smul ρ A r

@[simp]
theorem expectationLinear_apply (ρ A : Mat) :
    expectationLinear ρ A = expectation ρ A := rfl

/-- The Modular Automorphism: σ_ρ(B) = ρ * B * ρ⁻¹ for an invertible density matrix ρ. -/
def modularAutomorphism (ρ ρ_inv B : Mat) : Mat :=
  ρ * B * ρ_inv

theorem modularAutomorphism_add (ρ ρ_inv A B : Mat) :
    modularAutomorphism ρ ρ_inv (A + B) =
      modularAutomorphism ρ ρ_inv A + modularAutomorphism ρ ρ_inv B := by
  dsimp [modularAutomorphism]
  rw [mul_add, add_mul]

theorem modularAutomorphism_smul (ρ ρ_inv A : Mat) (r : R) :
    modularAutomorphism ρ ρ_inv (r • A) =
      r • modularAutomorphism ρ ρ_inv A := by
  dsimp [modularAutomorphism]
  rw [Matrix.mul_smul, smul_mul_assoc]

theorem modularAutomorphism_mul (ρ ρ_inv A B : Mat)
    (h_left : ρ_inv * ρ = 1) :
    modularAutomorphism ρ ρ_inv (A * B) =
      modularAutomorphism ρ ρ_inv A * modularAutomorphism ρ ρ_inv B := by
  dsimp [modularAutomorphism]
  calc
    ρ * (A * B) * ρ_inv = (ρ * A) * 1 * (B * ρ_inv) := by
      rw [mul_one]
      simp only [mul_assoc]
    _ = (ρ * A) * (ρ_inv * ρ) * (B * ρ_inv) := by rw [h_left]
    _ = (ρ * A * ρ_inv) * (ρ * B * ρ_inv) := by simp only [mul_assoc]

theorem modularAutomorphism_inverse_comp (ρ ρ_inv B : Mat)
    (h_left : ρ_inv * ρ = 1) :
    modularAutomorphism ρ_inv ρ
        (modularAutomorphism ρ ρ_inv B) = B := by
  dsimp [modularAutomorphism]
  calc
    ρ_inv * (ρ * B * ρ_inv) * ρ =
        (ρ_inv * ρ) * B * (ρ_inv * ρ) := by simp only [mul_assoc]
    _ = 1 * B * 1 := by rw [h_left]
    _ = B := by simp

theorem modularAutomorphism_inverse_comp' (ρ ρ_inv B : Mat)
    (h_right : ρ * ρ_inv = 1) :
    modularAutomorphism ρ ρ_inv
        (modularAutomorphism ρ_inv ρ B) = B := by
  dsimp [modularAutomorphism]
  calc
    ρ * (ρ_inv * B * ρ) * ρ_inv =
        (ρ * ρ_inv) * B * (ρ * ρ_inv) := by simp only [mul_assoc]
    _ = 1 * B * 1 := by rw [h_right]
    _ = B := by simp

/- The finite modular automorphism bundled as an `R`-linear map. -/
def modularAutomorphismLinear (ρ ρ_inv : Mat) : Mat →ₗ[R] Mat where
  toFun := modularAutomorphism ρ ρ_inv
  map_add' A B := modularAutomorphism_add ρ ρ_inv A B
  map_smul' r A := modularAutomorphism_smul ρ ρ_inv A r

@[simp]
theorem modularAutomorphismLinear_apply (ρ ρ_inv B : Mat) :
    modularAutomorphismLinear ρ ρ_inv B = modularAutomorphism ρ ρ_inv B := rfl

@[simp]
theorem modularAutomorphism_zero (ρ ρ_inv : Mat) :
    modularAutomorphism ρ ρ_inv 0 = 0 := by
  dsimp [modularAutomorphism]
  simp

theorem modularAutomorphism_one (ρ ρ_inv : Mat)
    (h_right : ρ * ρ_inv = 1) :
    modularAutomorphism ρ ρ_inv 1 = 1 := by
  dsimp [modularAutomorphism]
  rw [mul_one, h_right]

/--
  MASTER THEOREM: The Finite KMS Modular Condition:
  ω_ρ(A * σ_ρ(B)) = ω_ρ(B * A)
  for any density matrix ρ and invertible element ρ with ρ_inv * ρ = 1.
-/
theorem kms_modular_condition (ρ ρ_inv A B : Mat)
    (h_left : ρ_inv * ρ = 1) :
    expectation ρ (A * modularAutomorphism ρ ρ_inv B) = expectation ρ (B * A) := by
  dsimp [expectation, modularAutomorphism]
  calc
    Matrix.trace (ρ * (A * (ρ * B * ρ_inv)))
      = Matrix.trace ((ρ * A * ρ * B) * ρ_inv) := by
        simp only [mul_assoc]
    _ = Matrix.trace (ρ_inv * (ρ * A * ρ * B)) := by
        rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((ρ_inv * ρ) * (A * ρ * B)) := by
        simp only [mul_assoc]
    _ = Matrix.trace (1 * (A * ρ * B)) := by rw [h_left]
    _ = Matrix.trace (A * (ρ * B)) := by simp only [one_mul, mul_assoc]
    _ = Matrix.trace ((ρ * B) * A) := by
        rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (ρ * (B * A)) := by simp only [mul_assoc]

/-- THEOREM: Stationarity of the KMS state under its own Modular Flow:
    ω_ρ(σ_ρ(A)) = ω_ρ(A). -/
theorem kms_state_stationary (ρ ρ_inv A : Mat)
    (h_left : ρ_inv * ρ = 1) :
    expectation ρ (modularAutomorphism ρ ρ_inv A) = expectation ρ A := by
  have h := kms_modular_condition ρ ρ_inv 1 A h_left
  rw [one_mul, mul_one] at h
  exact h

/-- THEOREM: Invariance under Commuting Symmetries:
    If [B, ρ] = 0, then σ_ρ(B) = B. -/
theorem modular_fixed_point_of_commute (ρ ρ_inv B : Mat)
    (h_right : ρ * ρ_inv = 1)
    (h_comm : B * ρ = ρ * B) :
    modularAutomorphism ρ ρ_inv B = B := by
  dsimp [modularAutomorphism]
  calc ρ * B * ρ_inv
    _ = (ρ * B) * ρ_inv := by rw [mul_assoc]
    _ = (B * ρ) * ρ_inv := by rw [h_comm]
    _ = B * (ρ * ρ_inv) := by rw [mul_assoc]
    _ = B * 1 := by rw [h_right]
    _ = B := by rw [mul_one]

end InfoGeometry.Modular.KMS
