/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import proofs.KANTraceSectorization

noncomputable section

open Matrix Complex
open InfoGeometry.GrandUnification.KANTraceSectorization

namespace InfoGeometry.GrandUnification.BogoliubovFrameTransport

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli basis used as internal soldering frame (`σ_x,σ_y,σ_z`). -/
def pauliBasis : Fin 3 → M2C
  | ⟨0, _⟩ => pauliSigmaX
  | ⟨1, _⟩ => pauliSigmaY
  | ⟨2, _⟩ => pauliSigmaZ

/-- Explicit noncommutativity witness for the complex `2 × 2` matrix carrier. -/
def matX : M2C := pauliSigmaX

def matY : M2C := pauliSigmaY

lemma matX_mul_matY_ne_matY_mul_matX : matX * matY ≠ matY * matX := by
  intro h
  have h00 : Complex.I = -Complex.I := by
    simpa [matX, matY, pauliSigmaX, pauliSigmaY, Matrix.mul_apply, Fin.sum_univ_two] using
      congrFun (congrFun h 0) 0
  have hI : Complex.I = 0 := by
    linear_combination (1 / 2 : ℂ) * h00
  exact Complex.I_ne_zero hI

/-- Generalized two-sided conjugation transport. -/
def transportBy (U V : M2C) (S : M2C) : M2C :=
  U * S * V

/-- Basic multiplication compatibility of transported generators. -/
lemma transport_mul (U V : M2C)
    (hVU : V * U = (1 : M2C))
    (A B : M2C) :
    transportBy U V A * transportBy U V B = U * (A * B) * V := by
  calc
    transportBy U V A * transportBy U V B
        = (U * A * V) * (U * B * V) := by
          simp [transportBy]
    _ = U * A * (V * U) * (B * V) := by simp [mul_assoc]
    _ = U * A * (1 : M2C) * (B * V) := by rw [hVU]
    _ = U * A * (B * V) := by simp [mul_assoc]
    _ = U * (A * B) * V := by simp [mul_assoc]

/-- Trace is invariant under the transported pair when `V` is a right inverse of `U`. -/
lemma trace_transport_mul (U V : M2C)
    (hVU : V * U = (1 : M2C))
    (A B : M2C) :
    Matrix.trace (transportBy U V A * transportBy U V B) = Matrix.trace (A * B) := by
  rw [transport_mul U V hVU]
  calc
    Matrix.trace (U * (A * B) * V)
        = Matrix.trace (V * (U * (A * B))) := by
          simpa [mul_assoc] using (Matrix.trace_mul_cycle U (A * B) V)
    _ = Matrix.trace ((V * U) * (A * B)) := by simp [mul_assoc]
    _ = Matrix.trace ((1 : M2C) * (A * B)) := by rw [hVU]
    _ = Matrix.trace (A * B) := by simp [one_mul]

/-- Co-frame coefficients from trace projection (soldering definition). -/
def solderingCoeff (U V : M2C) (μ a : Fin 3) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace (transportBy U V (pauliBasis μ) * pauliBasis a)

/-- Anticommutator-projected induced metric via transported Pauli frame. -/
def inducedMetric (U V : M2C) (μ ν : Fin 3) : ℂ :=
  (1 / 2 : ℂ) * Matrix.trace
    (transportBy U V (pauliBasis μ) * transportBy U V (pauliBasis ν)
      + transportBy U V (pauliBasis ν) * transportBy U V (pauliBasis μ))

/-- Trace of transported anticommutator is the flat reference anticommutator trace. -/
lemma induced_metric_invariance (U V : M2C)
    (hVU : V * U = (1 : M2C)) (μ ν : Fin 3) :
    inducedMetric U V μ ν =
      (1 / 2 : ℂ) * Matrix.trace
        (pauliBasis μ * pauliBasis ν + pauliBasis ν * pauliBasis μ) := by
  have h1 : Matrix.trace (U * pauliBasis μ * V * (U * pauliBasis ν * V)) =
      Matrix.trace (pauliBasis μ * pauliBasis ν) := by
    simpa [transportBy, mul_assoc] using
      (trace_transport_mul U V hVU (pauliBasis μ) (pauliBasis ν))
  have h2 : Matrix.trace (U * pauliBasis ν * V * (U * pauliBasis μ * V)) =
      Matrix.trace (pauliBasis ν * pauliBasis μ) := by
    simpa [transportBy, mul_assoc] using
      (trace_transport_mul U V hVU (pauliBasis ν) (pauliBasis μ))
  unfold inducedMetric
  simp [transportBy, Matrix.trace_add, mul_add, h1, h2]

/-- Finite-dimensional proxy for the local gauge potential `\omega = (dU)U^{-1}`. -/
def spinConnection (U dU : M2C) : M2C := dU * U

/-- The finite spin connection is definitionally right multiplication by the frame. -/
lemma spinConnection_eq (U dU : M2C) : spinConnection U dU = dU * U := rfl

/-- KAN-specific transport operator and its explicit inverse pair from factors (no analytic assumptions). -/
def KANTransport (θ : ℝ) (β : ℝ) (z : ℂ) : M2C := KPart θ * APart β * NPart z

def KANTransport_inv (θ : ℝ) (β : ℝ) (z : ℂ) : M2C := NPart (-z) * APart (-β) * KPart (-θ)

lemma exp_mul_inv (z : ℂ) : Complex.exp z * Complex.exp (-z) = 1 := by
  calc
    Complex.exp z * Complex.exp (-z) = Complex.exp (z + -z) := by
      simpa using (Complex.exp_add z (-z)).symm
    _ = 1 := by simp [Complex.exp_zero]

lemma exp_inv_mul (z : ℂ) : Complex.exp (-z) * Complex.exp z = 1 := by
  rw [mul_comm]
  exact exp_mul_inv z

lemma KPart_inv (θ : ℝ) : KPart θ * KPart (-θ) = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KPart, exp_mul_inv, exp_inv_mul]

lemma KPart_inv' (θ : ℝ) : KPart (-θ) * KPart θ = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KPart, exp_mul_inv, exp_inv_mul]

lemma APart_inv (β : ℝ) : APart β * APart (-β) = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [APart, exp_mul_inv, exp_inv_mul]

lemma APart_inv' (β : ℝ) : APart (-β) * APart β = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [APart, exp_mul_inv, exp_inv_mul]

lemma NPart_inv (z : ℂ) : NPart z * NPart (-z) = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NPart]

lemma NPart_inv' (z : ℂ) : NPart (-z) * NPart z = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NPart]

lemma KANTransport_inverse_pair (θ : ℝ) (β : ℝ) (z : ℂ) :
    KANTransport θ β z * KANTransport_inv θ β z = (1 : M2C) ∧
      KANTransport_inv θ β z * KANTransport θ β z = (1 : M2C) := by
  constructor
  ·
    calc
      KANTransport θ β z * KANTransport_inv θ β z
          = KPart θ * APart β * (NPart z * NPart (-z)) * APart (-β) * KPart (-θ) := by
            simp [KANTransport, KANTransport_inv, mul_assoc]
      _ = KPart θ * APart β * (1 : M2C) * APart (-β) * KPart (-θ) := by rw [NPart_inv]
      _ = KPart θ * (APart β * APart (-β)) * KPart (-θ) := by simp [mul_assoc]
      _ = KPart θ * (1 : M2C) * KPart (-θ) := by rw [APart_inv β]
      _ = KPart θ * KPart (-θ) := by rw [mul_one]
      _ = (1 : M2C) := KPart_inv θ
  ·
    calc
      KANTransport_inv θ β z * KANTransport θ β z
          = NPart (-z) * APart (-β) * (KPart (-θ) * KPart θ) * APart β * NPart z := by
            simp [KANTransport, KANTransport_inv, mul_assoc]
      _ = NPart (-z) * APart (-β) * (1 : M2C) * APart β * NPart z := by rw [KPart_inv' θ]
      _ = NPart (-z) * (APart (-β) * APart β) * NPart z := by simp [mul_assoc]
      _ = NPart (-z) * (1 : M2C) * NPart z := by rw [APart_inv' β]
      _ = NPart (-z) * NPart z := by rw [mul_one]
      _ = (1 : M2C) := NPart_inv' z

/-- KAN transport inherits the same finite anticommutator metric as the flat Pauli frame. -/
theorem KAN_inducedMetric_formula (θ β : ℝ) (z : ℂ) (μ ν : Fin 3) :
    inducedMetric (KANTransport θ β z) (KANTransport_inv θ β z) μ ν
      =
    (1 / 2 : ℂ) * Matrix.trace
      (pauliBasis μ * pauliBasis ν + pauliBasis ν * pauliBasis μ) := by
  apply induced_metric_invariance
    (KANTransport θ β z) (KANTransport_inv θ β z)
    (KANTransport_inverse_pair θ β z).2

end InfoGeometry.GrandUnification.BogoliubovFrameTransport
