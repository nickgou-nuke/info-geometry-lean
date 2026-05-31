import InfoGeometry.Prequantum.SouriauJaynesTrace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

/-!
# InfoGeometry.Prequantum.SouriauJonesNilpotentBridge

Finite algebraic bridge between the Souriau--Jaynes trace lane and the
Wigner/Jones tensor-step lane.

This module proves only finite matrix facts:

* the local `2 × 2` Jordan generator squares to zero;
* the one-step tensor embedding `A ↦ A ⊗ I₂` preserves multiplication;
* the embedded Jordan generator is nilpotent;
* the finite Souriau--Jaynes trace pairing is equivariant for this nilpotent
  atom under a supplied `SL(2, ℝ)` matrix unit.

This module is only the finite nilpotent/tensor trace bridge.  Broader Souriau,
MaxEnt, Tomita--Takesaki, LCFT, and completed-operator-algebra statements are
owned by their corresponding repository modules and are not re-proved here.
-/

noncomputable section

open Matrix
open scoped Matrix Kronecker

namespace InfoGeometry.Prequantum.SouriauJonesNilpotentBridge

open InfoGeometry.Prequantum.SouriauJaynesTrace

/-- Standard `2 × 2` real matrix carrier from the finite Souriau trace bridge. -/
abbrev Mat2 := SouriauJaynesTrace.Mat2

/-- The one-step binary tensor stage, represented with product indices. -/
abbrev Mat2Tensor := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

/-- Local `2 × 2` nilpotent Jordan generator. -/
def localJordanNilpotent : Mat2 :=
  !![0, 1; 0, 0]

/-- One finite Wigner/Jones tensor step `A ↦ A ⊗ I₂`. -/
def jonesTensorStep (A : Mat2) : Mat2Tensor :=
  A ⊗ₖ (1 : Mat2)

/-- The local Jordan generator is strictly nilpotent. -/
theorem localJordanNilpotent_sq :
    localJordanNilpotent * localJordanNilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [localJordanNilpotent, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite tensor step preserves multiplication. -/
theorem jonesTensorStep_mul (A B : Mat2) :
    jonesTensorStep (A * B) = jonesTensorStep A * jonesTensorStep B := by
  unfold jonesTensorStep
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- The one-step embedded Jordan generator remains strictly nilpotent. -/
theorem jonesTensorStep_nilpotent :
    jonesTensorStep localJordanNilpotent * jonesTensorStep localJordanNilpotent = 0 := by
  rw [← jonesTensorStep_mul]
  rw [localJordanNilpotent_sq]
  unfold jonesTensorStep
  simp

/-- The local Jordan generator has zero trace. -/
theorem trace_localJordanNilpotent :
    Matrix.trace localJordanNilpotent = 0 := by
  simp [localJordanNilpotent, Matrix.trace, Fin.sum_univ_two]

/-- The embedded local Jordan generator has zero trace after one tensor step. -/
theorem trace_jonesTensorStep_localJordanNilpotent :
    Matrix.trace (jonesTensorStep localJordanNilpotent) = 0 := by
  unfold jonesTensorStep
  rw [Matrix.trace_kronecker]
  rw [trace_localJordanNilpotent]
  ring

/--
Finite Souriau--Jaynes trace-pairing equivariance specialized to the nilpotent
Jordan atom.
-/
theorem souriau_nilpotent_pairing_equivariance
    (g : SL2RUnit) (X : Mat2) :
    Matrix.trace (adjointAction g localJordanNilpotent * adjointAction g X) =
      Matrix.trace (localJordanNilpotent * X) :=
  souriau_momentum_equivariance g localJordanNilpotent X

/-- The trace of the conjugated nilpotent square remains zero. -/
theorem souriau_nilpotent_square_trace_equivariance
    (g : SL2RUnit) :
    Matrix.trace (adjointAction g localJordanNilpotent * adjointAction g localJordanNilpotent) = 0 := by
  rw [souriau_nilpotent_pairing_equivariance]
  rw [localJordanNilpotent_sq]
  simp

/-- Additive real-valued trace/readout functional. -/
structure AddTraceFunctional (A : Type*) [AddMonoid A] where
  /-- Underlying real-valued readout. -/
  tau : A → ℝ
  /-- Additivity of the readout. -/
  map_add : ∀ x y : A, tau (x + y) = tau x + tau y

namespace AddTraceFunctional

/-- Any additive real-valued trace/readout sends zero to zero. -/
theorem map_zero {A : Type*} [AddMonoid A] (F : AddTraceFunctional A) :
    F.tau 0 = 0 := by
  have h : F.tau (0 + 0) = F.tau 0 + F.tau 0 := F.map_add 0 0
  rw [zero_add] at h
  linarith

end AddTraceFunctional

/--
First-order nilpotent logarithm readout for a square-zero perturbation `1 + N`.

The definition records only the finite algebraic truncation `log(1+N) = N` used
when the logarithm is supplied by a square-zero model.  It is not an analytic
logarithm or convergence theorem.
-/
def firstOrderNilpotentLog {A : Type*} [Ring A] (N : A) : A :=
  N

/-- Finite algebraic regularization residual `(1+N) - 1 - log₁(N)`. -/
def modularRegularizationLCFT {A : Type*} [Ring A] (N : A) : A :=
  (1 + N) - 1 - firstOrderNilpotentLog N

/-- The finite first-order residual vanishes identically. -/
theorem modularRegularizationLCFT_eq_zero {A : Type*} [Ring A] (N : A) :
    modularRegularizationLCFT N = 0 := by
  unfold modularRegularizationLCFT firstOrderNilpotentLog
  noncomm_ring

/-- The same residual vanishes for any explicitly square-zero element. -/
theorem modularRegularizationLCFT_eq_zero_of_square_zero {A : Type*} [Ring A]
    (N : A) (_hN : N * N = 0) :
    modularRegularizationLCFT N = 0 :=
  modularRegularizationLCFT_eq_zero N

/-- Every additive trace/readout of the finite first-order residual is zero. -/
theorem trace_modularRegularizationLCFT_eq_zero {A : Type*} [Ring A]
    (F : AddTraceFunctional A) (N : A) :
    F.tau (modularRegularizationLCFT N) = 0 := by
  rw [modularRegularizationLCFT_eq_zero]
  exact F.map_zero

/-- The finite regularization residual vanishes on the local Jordan nilpotent. -/
theorem localJordan_modularRegularizationLCFT_eq_zero :
    modularRegularizationLCFT localJordanNilpotent = 0 :=
  modularRegularizationLCFT_eq_zero localJordanNilpotent

/-- Matrix trace of the local finite regularization residual is zero. -/
theorem trace_localJordan_modularRegularizationLCFT_eq_zero :
    Matrix.trace (modularRegularizationLCFT localJordanNilpotent) = 0 := by
  rw [localJordan_modularRegularizationLCFT_eq_zero]
  simp

end InfoGeometry.Prequantum.SouriauJonesNilpotentBridge
