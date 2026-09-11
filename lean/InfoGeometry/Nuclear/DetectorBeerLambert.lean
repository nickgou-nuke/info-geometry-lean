import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact first-collision path integration

This module derives the finite-path attenuation probability from an actual
interval integral and the fundamental theorem of calculus. The zero-attenuation
case is included; it is not hidden behind division by μ.
-/

noncomputable section

namespace InfoGeometry.Nuclear.DetectorBeerLambert

open Set MeasureTheory

/-- First-collision density per unit path length. -/
def collisionDensity (μ t : ℝ) : ℝ := μ * Real.exp (-μ * t)

def collisionIntegral (μ ℓ : ℝ) : ℝ := ∫ t in 0..ℓ, collisionDensity μ t

/-- Selected-outcome probability conditional on the first collision is κ. -/
def acceptedRayIntegral (μ ℓ : ℝ) (κ : ℝ → ℝ) : ℝ :=
  ∫ t in 0..ℓ, collisionDensity μ t * κ t

theorem continuous_collisionDensity (μ : ℝ) : Continuous (collisionDensity μ) := by
  unfold collisionDensity
  fun_prop

theorem hasDerivAt_collisionPrimitive (μ t : ℝ) :
    HasDerivAt (fun u : ℝ => -Real.exp (-μ * u)) (collisionDensity μ t) t := by
  convert (((hasDerivAt_id t).const_mul (-μ)).exp).neg using 1 <;>
    simp [collisionDensity] <;> ring

/-- Exact Beer--Lambert first-collision probability, valid algebraically even
at μ = 0; physical bounds use μ ≥ 0 and ℓ ≥ 0. -/
theorem collisionIntegral_eq (μ ℓ : ℝ) :
    collisionIntegral μ ℓ = 1 - Real.exp (-μ * ℓ) := by
  unfold collisionIntegral
  calc
    (∫ t in 0..ℓ, collisionDensity μ t) =
        -Real.exp (-μ * ℓ) - (-Real.exp (-μ * 0)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_collisionPrimitive μ t)
        ((continuous_collisionDensity μ).intervalIntegrable 0 ℓ)
    _ = 1 - Real.exp (-μ * ℓ) := by simp <;> ring

theorem collisionDensity_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (t : ℝ) :
    0 ≤ collisionDensity μ t :=
  mul_nonneg hμ (Real.exp_pos _).le

theorem collisionIntegral_nonneg {μ ℓ : ℝ} (hμ : 0 ≤ μ) (hℓ : 0 ≤ ℓ) :
    0 ≤ collisionIntegral μ ℓ := by
  apply intervalIntegral.integral_nonneg hℓ
  intro t _
  exact collisionDensity_nonneg hμ t

theorem collisionIntegral_le_one (μ ℓ : ℝ) : collisionIntegral μ ℓ ≤ 1 := by
  rw [collisionIntegral_eq]
  have h := Real.exp_pos (-μ * ℓ)
  linarith

theorem collisionIntegral_mem_unitInterval {μ ℓ : ℝ}
    (hμ : 0 ≤ μ) (hℓ : 0 ≤ ℓ) :
    collisionIntegral μ ℓ ∈ Icc (0 : ℝ) 1 :=
  ⟨collisionIntegral_nonneg hμ hℓ, collisionIntegral_le_one μ ℓ⟩

@[simp] theorem collisionIntegral_zero (ℓ : ℝ) : collisionIntegral 0 ℓ = 0 := by
  simp [collisionIntegral_eq]

theorem integrable_acceptedRay (μ ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    {κ : ℝ → ℝ} (hκ : ContinuousOn κ (Icc 0 ℓ)) :
    IntervalIntegrable (fun t => collisionDensity μ t * κ t) volume 0 ℓ := by
  apply ContinuousOn.intervalIntegrable_of_Icc hℓ
  exact (continuous_collisionDensity μ).continuousOn.mul hκ

theorem acceptedRay_nonneg {μ ℓ : ℝ} (hμ : 0 ≤ μ) (hℓ : 0 ≤ ℓ)
    {κ : ℝ → ℝ} (hκ : ∀ t ∈ Icc 0 ℓ, 0 ≤ κ t) :
    0 ≤ acceptedRayIntegral μ ℓ κ := by
  apply intervalIntegral.integral_nonneg hℓ
  intro t ht
  exact mul_nonneg (collisionDensity_nonneg hμ t) (hκ t ht)

theorem acceptedRay_le_collision {μ ℓ : ℝ} (hμ : 0 ≤ μ) (hℓ : 0 ≤ ℓ)
    {κ : ℝ → ℝ} (hκ : ContinuousOn κ (Icc 0 ℓ))
    (hκ1 : ∀ t ∈ Icc 0 ℓ, κ t ≤ 1) :
    acceptedRayIntegral μ ℓ κ ≤ collisionIntegral μ ℓ := by
  apply intervalIntegral.integral_mono_on hℓ (integrable_acceptedRay μ ℓ hℓ hκ)
    ((continuous_collisionDensity μ).intervalIntegrable 0 ℓ)
  intro t ht
  exact mul_le_of_le_one_right (collisionDensity_nonneg hμ t) (hκ1 t ht)

theorem acceptedRay_le_one {μ ℓ : ℝ} (hμ : 0 ≤ μ) (hℓ : 0 ≤ ℓ)
    {κ : ℝ → ℝ} (hκ : ContinuousOn κ (Icc 0 ℓ))
    (hκ1 : ∀ t ∈ Icc 0 ℓ, κ t ≤ 1) :
    acceptedRayIntegral μ ℓ κ ≤ 1 :=
  (acceptedRay_le_collision hμ hℓ hκ hκ1).trans (collisionIntegral_le_one μ ℓ)

/-- A constant partial interaction coefficient ν gives this particular
first-interaction channel. It is not automatically a full-energy peak. -/
theorem partialCollisionIntegral_eq (μ ν ℓ : ℝ) (hμ : μ ≠ 0) :
    (∫ t in 0..ℓ, ν * Real.exp (-μ * t)) =
      (ν / μ) * (1 - Real.exp (-μ * ℓ)) := by
  have hfun : (fun t : ℝ => ν * Real.exp (-μ * t)) =
      (fun t : ℝ => (ν / μ) * collisionDensity μ t) := by
    funext t
    unfold collisionDensity
    field_simp [hμ] <;> ring
  rw [hfun, intervalIntegral.integral_const_mul]
  exact congrArg (fun x : ℝ => (ν / μ) * x) (collisionIntegral_eq μ ℓ)

end InfoGeometry.Nuclear.DetectorBeerLambert
