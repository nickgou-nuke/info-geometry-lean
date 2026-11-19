/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.CanonicalScalarStress
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp

/-! # Scalar kinetic energy, source balance, and sign obstructions

The energy is the time-time component of the constructed canonical scalar
stress tensor. Its time derivative is proved with native `HasDerivAt`.
The supplied scalar evolution equation gives a conditional energy-exchange
identity and, in the source-free case, a conserved scaled energy.

The velocity derivative of a quadratic kinetic Lagrangian also constructs its
Legendre energy. Reversing the kinetic sign reverses that energy. These are
real-variable and fixed-frame consequences, not a continuum action variation,
an existence theorem for cosmological solutions, or a microscopic source law.
-/

noncomputable section

namespace InfoGeometry.Physics.ScalarKineticBalance

open InfoGeometry.Physics.CanonicalScalarStress

/-- A quadratic kinetic Lagrangian with fixed spatial quadratic contribution.
Positive `kappa` is the positive temporal-kinetic convention in signature `(-+++)`. -/
def kineticLagrangian (kappa spatialSq velocity : ℝ) : ℝ :=
  kappa / 2 * (velocity ^ 2 - spatialSq)

/-- The momentum is the actual velocity derivative, not an additional assumption. -/
def kineticMomentum (kappa spatialSq velocity : ℝ) : ℝ :=
  deriv (kineticLagrangian kappa spatialSq) velocity

/-- The Legendre expression constructed from the actual velocity derivative. -/
def legendreEnergy (kappa spatialSq velocity : ℝ) : ℝ :=
  kineticMomentum kappa spatialSq velocity * velocity -
    kineticLagrangian kappa spatialSq velocity

theorem hasDerivAt_kineticLagrangian (kappa spatialSq velocity : ℝ) :
    HasDerivAt (kineticLagrangian kappa spatialSq) (kappa * velocity) velocity := by
  unfold kineticLagrangian
  convert (((hasDerivAt_id velocity).pow 2).sub_const spatialSq).const_mul
    (kappa / 2) using 1 <;> simp <;> ring

theorem kineticMomentum_eq (kappa spatialSq velocity : ℝ) :
    kineticMomentum kappa spatialSq velocity = kappa * velocity :=
  (hasDerivAt_kineticLagrangian kappa spatialSq velocity).deriv

theorem legendreEnergy_eq (kappa spatialSq velocity : ℝ) :
    legendreEnergy kappa spatialSq velocity =
      kappa / 2 * (velocity ^ 2 + spatialSq) := by
  rw [legendreEnergy, kineticMomentum_eq, kineticLagrangian]
  ring

/-- The positive kinetic convention agrees with the already constructed tensor energy. -/
theorem legendreEnergy_eq_energyDensity (lambda : ℝ) (v : Fin 4 → ℝ) :
    legendreEnergy lambda (spatialGradientSq v) (v 0) = energyDensity lambda v := by
  rw [legendreEnergy_eq, energyDensity_eq]

/-- Reversing the kinetic convention reverses the tensor energy. -/
theorem legendreEnergy_neg_eq_neg_energyDensity (lambda : ℝ) (v : Fin 4 → ℝ) :
    legendreEnergy (-lambda) (spatialGradientSq v) (v 0) = -energyDensity lambda v := by
  rw [legendreEnergy_eq, energyDensity_eq]
  ring

theorem legendreEnergy_nonneg (kappa spatialSq velocity : ℝ)
    (hkappa : 0 ≤ kappa) (hspatial : 0 ≤ spatialSq) :
    0 ≤ legendreEnergy kappa spatialSq velocity := by
  rw [legendreEnergy_eq]
  exact mul_nonneg (div_nonneg hkappa (by norm_num))
    (add_nonneg (sq_nonneg velocity) hspatial)

/-- With positive coupling and a nonzero temporal derivative, the reversed sign
has strictly negative Legendre energy even in the homogeneous sector. -/
theorem legendreEnergy_neg_homogeneous (lambda velocity : ℝ)
    (hlambda : 0 < lambda) (hvelocity : velocity ≠ 0) :
    legendreEnergy (-lambda) 0 velocity < 0 := by
  rw [legendreEnergy_eq]
  have hpos : 0 < lambda / 2 * velocity ^ 2 :=
    mul_pos (div_pos hlambda (by norm_num)) (sq_pos_of_ne_zero hvelocity)
  nlinarith

/-- Differentiate the actual time-time component along a homogeneous covector. -/
theorem hasDerivAt_homogeneous_energy (lambda : ℝ) {u : ℝ → ℝ} {du t : ℝ}
    (hu : HasDerivAt u du t) :
    HasDerivAt (fun s => energyDensity lambda (homogeneousCovector (u s)))
      (lambda * u t * du) t := by
  simp only [energyDensity_homogeneous]
  convert (hu.pow 2).const_mul (lambda / 2) using 1 <;> simp <;> ring

/-- The sourced scalar equation yields the canonical energy-exchange balance. -/
theorem homogeneous_source_balance (lambda H Gamma : ℝ)
    {u : ℝ → ℝ} {du t : ℝ} (hu : HasDerivAt u du t)
    (hevolution : du + 3 * H * u t = Gamma) :
    deriv (fun s => energyDensity lambda (homogeneousCovector (u s))) t +
      3 * H * (energyDensity lambda (homogeneousCovector (u t)) +
        meanSpatialStress (stressTensor lambda (homogeneousCovector (u t)))) =
      lambda * u t * Gamma := by
  rw [(hasDerivAt_homogeneous_energy lambda hu).deriv,
    energyDensity_homogeneous, meanSpatialStress_homogeneous]
  have hdu : du = Gamma - 3 * H * u t := by linarith
  rw [hdu]
  ring

/-- Subtracting `lambda * Gamma` from the canonical pressure changes the balance
by this nonzero-in-general residual. -/
theorem source_pressure_residual (lambda H Gamma : ℝ)
    {u : ℝ → ℝ} {du t : ℝ} (hu : HasDerivAt u du t)
    (hevolution : du + 3 * H * u t = Gamma) :
    deriv (fun s => energyDensity lambda (homogeneousCovector (u s))) t +
      3 * H * (energyDensity lambda (homogeneousCovector (u t)) +
        (meanSpatialStress (stressTensor lambda (homogeneousCovector (u t))) -
          lambda * Gamma)) - lambda * u t * Gamma = -3 * H * lambda * Gamma := by
  have hbalance := homogeneous_source_balance lambda H Gamma hu hevolution
  linarith

/-- Absorbing the exchange term into an effective pressure requires its actual
energy-transfer coefficient and a nonzero Hubble coefficient. -/
theorem effective_pressure_balance (lambda H Gamma : ℝ) (hH : H ≠ 0)
    {u : ℝ → ℝ} {du t : ℝ} (hu : HasDerivAt u du t)
    (hevolution : du + 3 * H * u t = Gamma) :
    deriv (fun s => energyDensity lambda (homogeneousCovector (u s))) t +
      3 * H * (energyDensity lambda (homogeneousCovector (u t)) +
        (meanSpatialStress (stressTensor lambda (homogeneousCovector (u t))) -
          lambda * u t * Gamma / (3 * H))) = 0 := by
  have hbalance := homogeneous_source_balance lambda H Gamma hu hevolution
  have hcancel : 3 * H * (lambda * u t * Gamma / (3 * H)) =
      lambda * u t * Gamma := by field_simp [hH]
  nlinarith

/-- A precise source-free equation fixes the derivative-to-friction ratio. -/
theorem abs_derivative_of_source_free (H u du : ℝ) (hH : 0 ≤ H)
    (hevolution : du + 3 * H * u = 0) :
    |du| = 3 * H * |u| := by
  have hdu : du = -(3 * H * u) := by linarith
  rw [hdu, abs_neg, abs_mul, abs_mul, abs_of_nonneg hH]
  norm_num

/-- Any quantitative slow-roll bound with factor below three forces the
source-free temporal derivative to vanish when the Hubble coefficient is positive. -/
theorem eq_zero_of_source_free_slow_roll (H u du epsilon : ℝ)
    (hH : 0 < H) (hepsilon : epsilon < 3)
    (hevolution : du + 3 * H * u = 0)
    (hslow : |du| ≤ epsilon * H * |u|) : u = 0 := by
  rw [abs_derivative_of_source_free H u du hH.le hevolution] at hslow
  by_contra hu
  have hpos : 0 < H * |u| := mul_pos hH (abs_pos.mpr hu)
  have hstrict := mul_lt_mul_of_pos_right hepsilon hpos
  nlinarith

/-- The source-free equation has the first integral `a^6 * rho`.
This is a derivative statement at the specified time, with both ODE inputs explicit. -/
theorem hasDerivAt_scaled_energy_zero (lambda H : ℝ)
    {a u : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt a (H * a t) t)
    (hu : HasDerivAt u (-3 * H * u t) t) :
    HasDerivAt (fun s => a s ^ 6 * energyDensity lambda (homogeneousCovector (u s)))
      0 t := by
  have h := (ha.pow 6).mul (hasDerivAt_homogeneous_energy lambda hu)
  convert h using 1 <;> simp [energyDensity_homogeneous] <;> ring

/-- If the source-free ODEs hold on the real time line, the scaled energy is constant. -/
theorem scaled_energy_constant (lambda : ℝ) (a u H : ℝ → ℝ)
    (ha : ∀ t, HasDerivAt a (H t * a t) t)
    (hu : ∀ t, HasDerivAt u (-3 * H t * u t) t) (s t : ℝ) :
    a s ^ 6 * energyDensity lambda (homogeneousCovector (u s)) =
      a t ^ 6 * energyDensity lambda (homogeneousCovector (u t)) := by
  have hd := fun x => hasDerivAt_scaled_energy_zero lambda (H x) (ha x) (hu x)
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) s t

end InfoGeometry.Physics.ScalarKineticBalance

end
