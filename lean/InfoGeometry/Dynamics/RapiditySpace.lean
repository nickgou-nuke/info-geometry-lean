import InfoGeometry.Dynamics.HyperbolicComponent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

noncomputable section

/-!
# RapiditySpace

Finite real-coordinate readouts for the hyperbolic `A` component.

This file proves only the matrix/log identities that are available at the
finite `2 × 2` level:

* hyperbolic boosts compose by adding rapidities;
* a positive exponential light-cone coordinate shifts additively after `log`.

No KMS condition, modular analyticity, or Rindler thermal theorem is asserted.
-/

namespace InfoGeometry.Dynamics.RapiditySpace

open Matrix
open InfoGeometry.Dynamics.HyperbolicComponent

/-- Positive logarithmic coordinate, with positivity carried explicitly. -/
def logCoordinate (z : ℝ) (_hz : 0 < z) : ℝ :=
  Real.log z

/-- Real two-component light-cone column. -/
abbrev LightConeColumn : Type :=
  Matrix (Fin 2) (Fin 1) ℝ

/-- The upper light-cone exponential ray `x₊ = exp ξ`, `x₋ = 0`. -/
def upperExponentialRay (ξ : ℝ) : LightConeColumn :=
  !![Real.exp ξ; 0]

/-! ## Hyperbolic rapidity composition -/

/-- Hyperbolic boosts compose by addition of rapidities. -/
theorem rapidity_additive_composition (lam₁ lam₂ : ℝ) :
    componentAReal lam₁ * componentAReal lam₂ = componentAReal (lam₁ + lam₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [componentAReal, Matrix.mul_apply, Real.exp_add]
  ring

/-- The zero rapidity boost is the identity. -/
theorem rapidity_zero :
    componentAReal 0 = (1 : Mat2R) :=
  componentAReal_zero

/-- The negative rapidity boost is a right inverse. -/
theorem rapidity_mul_neg (lam : ℝ) :
    componentAReal lam * componentAReal (-lam) = (1 : Mat2R) := by
  rw [rapidity_additive_composition]
  simp [componentAReal_zero]

/-- The negative rapidity boost is a left inverse. -/
theorem rapidity_neg_mul (lam : ℝ) :
    componentAReal (-lam) * componentAReal lam = (1 : Mat2R) := by
  rw [rapidity_additive_composition]
  simp [componentAReal_zero, add_comm]

/-! ## Log-coordinate readout -/

/-- The top light-cone coordinate is scaled by `exp λ`. -/
theorem rapidity_upper_ray_coordinate (ξ lam : ℝ) :
    (componentAReal lam * upperExponentialRay ξ) 0 0 =
      Real.exp (lam + ξ) := by
  simp [componentAReal, upperExponentialRay, Matrix.mul_apply, Real.exp_add]

/--
Taking the real logarithm turns the hyperbolic boost into an additive
rapidity shift.
-/
theorem log_coordinate_rapidity_shift (ξ lam : ℝ) :
    Real.log ((componentAReal lam * upperExponentialRay ξ) 0 0) = ξ + lam := by
  rw [rapidity_upper_ray_coordinate]
  rw [Real.log_exp]
  ring

end InfoGeometry.Dynamics.RapiditySpace
