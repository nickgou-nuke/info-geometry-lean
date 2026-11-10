/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
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
variable {R : Type*} [Ring R]

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

theorem expectation_smul {R : Type*} [CommRing R] (ρ A : Matrix ι ι R) (r : R) :
    expectation ρ (r • A) = r • expectation ρ A := by
  dsimp [expectation]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]

theorem expectation_sub (ρ A B : Mat) :
    expectation ρ (A - B) = expectation ρ A - expectation ρ B := by
  dsimp [expectation]
  rw [mul_sub, Matrix.trace_sub]

/-- The finite expectation functional bundled as an `R`-linear map. -/
def expectationLinear {R : Type*} [CommRing R] (ρ : Matrix ι ι R) : Matrix ι ι R →ₗ[R] R where
  toFun := expectation ρ
  map_add' A B := expectation_add ρ A B
  map_smul' r A := by
    simpa [smul_eq_mul] using expectation_smul ρ A r

@[simp]
theorem expectationLinear_apply {R : Type*} [CommRing R] (ρ A : Matrix ι ι R) :
    expectationLinear ρ A = expectation ρ A := rfl

/-- The Modular Automorphism: σ_ρ(B) = ρ * B * ρ⁻¹ for an invertible density matrix ρ. -/
def modularAutomorphism (ρ ρ_inv B : Mat) : Mat :=
  ρ * B * ρ_inv

theorem modularAutomorphism_add (ρ ρ_inv A B : Mat) :
    modularAutomorphism ρ ρ_inv (A + B) =
      modularAutomorphism ρ ρ_inv A + modularAutomorphism ρ ρ_inv B := by
  dsimp [modularAutomorphism]
  rw [mul_add, add_mul]

theorem modularAutomorphism_smul {R : Type*} [CommRing R] (ρ ρ_inv A : Matrix ι ι R) (r : R) :
    modularAutomorphism ρ ρ_inv (r • A) =
      r • modularAutomorphism ρ ρ_inv A := by
  dsimp [modularAutomorphism]
  rw [Matrix.mul_smul, smul_mul_assoc]

theorem modularAutomorphism_sub (ρ ρ_inv A B : Mat) :
    modularAutomorphism ρ ρ_inv (A - B) =
      modularAutomorphism ρ ρ_inv A - modularAutomorphism ρ ρ_inv B := by
  dsimp [modularAutomorphism]
  rw [mul_sub, sub_mul]

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

theorem modularAutomorphism_commutator (ρ ρ_inv A B : Mat)
    (h_left : ρ_inv * ρ = 1) :
    modularAutomorphism ρ ρ_inv (A * B - B * A) =
      modularAutomorphism ρ ρ_inv A * modularAutomorphism ρ ρ_inv B -
        modularAutomorphism ρ ρ_inv B * modularAutomorphism ρ ρ_inv A := by
  rw [modularAutomorphism_sub, modularAutomorphism_mul ρ ρ_inv A B h_left,
    modularAutomorphism_mul ρ ρ_inv B A h_left]

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
def modularAutomorphismLinear {R : Type*} [CommRing R] (ρ ρ_inv : Matrix ι ι R) : Matrix ι ι R →ₗ[R] Matrix ι ι R where
  toFun := modularAutomorphism ρ ρ_inv
  map_add' A B := modularAutomorphism_add ρ ρ_inv A B
  map_smul' r A := modularAutomorphism_smul ρ ρ_inv A r

@[simp]
theorem modularAutomorphismLinear_apply {R : Type*} [CommRing R] (ρ ρ_inv B : Matrix ι ι R) :
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
theorem kms_modular_condition {R : Type*} [CommRing R] (ρ ρ_inv A B : Matrix ι ι R)
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

/-- The expectation of a commutator is exactly the modular displacement of
its first entry, paired against the second entry. This is the commutator
defect form of the finite KMS identity. -/
theorem kms_expectation_commutator_eq_modular_defect {R : Type*} [CommRing R]
    (ρ ρ_inv A B : Matrix ι ι R) (h_left : ρ_inv * ρ = 1) :
    expectation ρ (A * B - B * A) =
      expectation ρ (B * (modularAutomorphism ρ ρ_inv A - A)) := by
  calc
    expectation ρ (A * B - B * A) =
        expectation ρ (A * B) - expectation ρ (B * A) := by
          exact expectation_sub ρ (A * B) (B * A)
    _ = expectation ρ (B * modularAutomorphism ρ ρ_inv A) -
        expectation ρ (B * A) := by
          rw [← kms_modular_condition ρ ρ_inv B A h_left]
    _ = expectation ρ (B * (modularAutomorphism ρ ρ_inv A - A)) := by
          rw [mul_sub, expectation_sub]

/-- A matrix trace weight commuting with an idempotent cut annihilates its
inner derivation. The associated odd Peirce grade has zero readout, even
pinching preserves the readout, and products of two tangent directions are
fixed by even pinching. This is an algebraic trace statement: no positivity,
normalization, or KMS modular condition is assumed. -/
theorem traceWeight_peirce_tangent_qgt_synthesis {R : Type*} [CommRing R]
    (K P X A B : Matrix ι ι R) (hP : P * P = P) (hKP : K * P = P * K) :
    expectation K (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X) = 0 ∧
    expectation K (InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade P X) = 0 ∧
    expectation K (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade P X) =
      expectation K X ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade P
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P A *
          InfoGeometry.OperatorAlgebra.PeirceSpine.comm P B) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm P A *
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm P B := by
  let opComm : Matrix ι ι R → Matrix ι ι R → Matrix ι ι R := InfoGeometry.OperatorAlgebra.PeirceSpine.comm
  have hStationary (Y : Matrix ι ι R) : expectation K (opComm P Y) = 0 := by
    dsimp [expectation, opComm, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    have hTraceCycle : Matrix.trace (K * (P * Y)) =
        Matrix.trace (K * (Y * P)) := by
      calc
        Matrix.trace (K * (P * Y)) = Matrix.trace ((K * P) * Y) := by
          rw [Matrix.mul_assoc]
        _ = Matrix.trace ((P * K) * Y) := by rw [hKP]
        _ = Matrix.trace (P * (K * Y)) := by rw [Matrix.mul_assoc]
        _ = Matrix.trace ((K * Y) * P) := Matrix.trace_mul_comm P (K * Y)
        _ = Matrix.trace (K * (Y * P)) := by rw [Matrix.mul_assoc]
    calc
      Matrix.trace (K * (P * Y - Y * P)) =
          Matrix.trace (K * (P * Y) - K * (Y * P)) := by rw [mul_sub]
      _ = Matrix.trace (K * (P * Y)) - Matrix.trace (K * (Y * P)) :=
          Matrix.trace_sub _ _
      _ = 0 := sub_eq_zero.mpr hTraceCycle
  have hOddFormula (Y : Matrix ι ι R) :
      InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade P Y =
        opComm P (opComm P Y) := by
    dsimp [opComm]
    peirce_nf hP
  have hEven : InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade P X =
      X - opComm P (opComm P X) := by
    calc
      InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade P X =
          X - InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade P X := by
            have hSum :=
              (InfoGeometry.OperatorAlgebra.PeirceSpine.grade_projection_laws hP X).2.2.2.2
            calc
              _ = (_ + InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade P X) -
                    InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade P X := by abel
              _ = _ := by rw [hSum]
      _ = X - opComm P (opComm P X) := by rw [hOddFormula]
  have hTangent : opComm P (opComm P A * opComm P B) = 0 := by
    dsimp [opComm]
    peirce_nf hP
  have hTangentOdd :
      InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade P
          (opComm P A * opComm P B) = 0 := by
    rw [hOddFormula, hTangent]
    simp [opComm, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  have hTangentEven :
      InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade P
          (opComm P A * opComm P B) = opComm P A * opComm P B := by
    simpa [hTangentOdd] using
      (InfoGeometry.OperatorAlgebra.PeirceSpine.grade_projection_laws hP
        (opComm P A * opComm P B)).2.2.2.2
  refine ⟨hStationary X, ?_, ?_, ?_⟩
  · rw [hOddFormula]
    exact hStationary (opComm P X)
  · rw [hEven, expectation_sub, hStationary, sub_zero]
  · exact hTangentEven

/-- THEOREM: Stationarity of the KMS state under its own Modular Flow:
    ω_ρ(σ_ρ(A)) = ω_ρ(A). -/
theorem kms_state_stationary {R : Type*} [CommRing R] (ρ ρ_inv A : Matrix ι ι R)
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
