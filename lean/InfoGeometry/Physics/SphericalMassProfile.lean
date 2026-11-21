/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A spherical mass profile and its derived density

The two-term profile is the interpolation in equation (8) of Neukart, Marx,
and Vinokur, *Finite-Capacity Spacetime and Entropic Contributions to
Cosmological Structure Formation*, Physics 8 (2026), 49,
DOI: 10.3390/physics8020049. This file proves its real-variable consequences.

The density is defined using the actual derivative of the enclosed mass,
divided by the spherical area `4 * π * r²`. For positive amplitude and saturation
radius, its inner behavior is an unbounded `1 / r` cusp and its outer behavior
is `1 / r²`. No entropy-to-gravity law,
field equation, or empirical fit is inferred from this prescribed profile.
-/

noncomputable section

namespace InfoGeometry.Physics.SphericalMassProfile

open Filter Set
open scoped Topology

/-- The two-term interpolation as printed in the source paper. -/
def twoTermMass (η s r : ℝ) : ℝ :=
  η * r ^ 2 * (1 + r / s)⁻¹ + η * s * r * (1 + s / r)⁻¹

/-- The reduced rational form of the enclosed mass profile. -/
def mass (η s r : ℝ) : ℝ :=
  2 * η * s * r ^ 2 / (r + s)

/-- Both printed terms contribute the same rational expression. -/
theorem twoTermMass_eq_mass (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    twoTermMass η s r = mass η s r := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have h₁ : 1 + r / s ≠ 0 := ne_of_gt (by positivity)
  have h₂ : 1 + s / r ≠ 0 := ne_of_gt (by positivity)
  unfold twoTermMass mass
  field_simp [hs0, hr0, hrs, h₁, h₂]
  <;> ring

/-- The derivative of the reduced mass profile is proved by the quotient rule. -/
theorem hasDerivAt_mass (η s r : ℝ) (hrs : r + s ≠ 0) :
    HasDerivAt (mass η s)
      (2 * η * s * r * (r + 2 * s) / (r + s) ^ 2) r := by
  have hnum : HasDerivAt (fun x : ℝ => 2 * η * s * x ^ 2)
      (2 * η * s * (2 * r)) r := by
    convert ((hasDerivAt_id r).pow 2).const_mul (2 * η * s) using 1
    · funext x
      rfl
    · simp only [id_eq]
      ring
  have hquot := hnum.div ((hasDerivAt_id r).add_const s) hrs
  convert hquot using 1
  · funext x
    rfl
  · simp only [id_eq]
    field_simp [hrs]
    <;> ring

theorem deriv_mass (η s r : ℝ) (hrs : r + s ≠ 0) :
    deriv (mass η s) r =
      2 * η * s * r * (r + 2 * s) / (r + s) ^ 2 :=
  (hasDerivAt_mass η s r hrs).deriv

/-- Density obtained from the actual derivative of the enclosed mass. -/
def density (η s r : ℝ) : ℝ :=
  deriv (mass η s) r / (4 * Real.pi * r ^ 2)

theorem density_eq (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    density η s r = η * s * (r + 2 * s) /
      (2 * Real.pi * r * (r + s) ^ 2) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [density, deriv_mass η s r hrs]
  field_simp [hr0, hrs, hπ]
  <;> ring

theorem density_pos (η s r : ℝ) (hη : 0 < η) (hs : 0 < s) (hr : 0 < r) :
    0 < density η s r := by
  rw [density_eq η s r hs hr]
  positivity

/-- Multiplying by the radius removes the inner singular factor. -/
theorem radius_mul_density (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    r * density η s r =
      η * s * (r + 2 * s) / (2 * Real.pi * (r + s) ^ 2) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [density_eq η s r hs hr]
  field_simp [hr0, hrs, hπ]
  <;> ring

/-- Exact coefficient of the inner `1 / r` cusp. -/
theorem tendsto_radius_mul_density_zero (η s : ℝ) (hs : 0 < s) :
    Tendsto (fun r : ℝ => r * density η s r) (𝓝[>] 0)
      (𝓝 (η / Real.pi)) := by
  have hnum : Tendsto (fun r : ℝ => η * s * (r + 2 * s)) (𝓝 0)
      (𝓝 (η * s * (0 + 2 * s))) :=
    tendsto_const_nhds.mul (tendsto_id.add tendsto_const_nhds)
  have hden : Tendsto (fun r : ℝ => 2 * Real.pi * (r + s) ^ 2) (𝓝 0)
      (𝓝 (2 * Real.pi * (0 + s) ^ 2)) :=
    tendsto_const_nhds.mul ((tendsto_id.add tendsto_const_nhds).pow 2)
  have hden0 : 2 * Real.pi * (0 + s) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h : Tendsto
      (fun r : ℝ => η * s * (r + 2 * s) / (2 * Real.pi * (r + s) ^ 2))
      (𝓝[>] 0) (𝓝 (η * s * (0 + 2 * s) / (2 * Real.pi * (0 + s) ^ 2))) :=
    (hnum.div hden hden0).mono_left nhdsWithin_le_nhds
  have hc : η * s * (0 + 2 * s) / (2 * Real.pi * (0 + s) ^ 2) =
      η / Real.pi := by
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [hs0, hπ]
    <;> ring
  rw [hc] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (radius_mul_density η s r hs hr).symm

/-- Positive profile parameters force divergence at the center. -/
theorem tendsto_density_zero_atTop (η s : ℝ) (hη : 0 < η) (hs : 0 < s) :
    Tendsto (density η s) (𝓝[>] 0) atTop := by
  have h := (tendsto_radius_mul_density_zero η s hs).pos_mul_atTop
    (div_pos hη Real.pi_pos) tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  field_simp [hr0]

/-- In particular, this prescribed profile has no finite central density limit. -/
theorem not_tendsto_density_zero_finite (η s L : ℝ) (hη : 0 < η) (hs : 0 < s) :
    ¬ Tendsto (density η s) (𝓝[>] 0) (𝓝 L) :=
  not_tendsto_nhds_of_tendsto_atTop (tendsto_density_zero_atTop η s hη hs) L

/-- A form of the scaled outer density suitable for taking the limit at infinity. -/
theorem radius_sq_mul_density (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    r ^ 2 * density η s r =
      η * s * (1 + 2 * s * r⁻¹) /
        (2 * Real.pi * (1 + s * r⁻¹) ^ 2) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hden : 1 + s * r⁻¹ ≠ 0 := ne_of_gt (by positivity)
  rw [density_eq η s r hs hr]
  field_simp [hr0, hrs, hπ, hden]
  <;> ring

/-- Exact coefficient of the outer `1 / r²` envelope. -/
theorem tendsto_radius_sq_mul_density_atTop (η s : ℝ) (hs : 0 < s) :
    Tendsto (fun r : ℝ => r ^ 2 * density η s r) atTop
      (𝓝 (η * s / (2 * Real.pi))) := by
  have hi : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto (fun r : ℝ => η * s * (1 + 2 * s * r⁻¹)) atTop
      (𝓝 (η * s * (1 + 2 * s * 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hi))
  have hden : Tendsto (fun r : ℝ => 2 * Real.pi * (1 + s * r⁻¹) ^ 2) atTop
      (𝓝 (2 * Real.pi * (1 + s * 0) ^ 2)) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.add (tendsto_const_nhds.mul hi)).pow 2)
  have hden0 : 2 * Real.pi * (1 + s * 0) ^ 2 ≠ 0 := by
    simpa using ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  have h := hnum.div hden hden0
  simp only [mul_zero, add_zero, one_pow, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (radius_sq_mul_density η s r hs hr).symm

/-- The usual spherical circular-speed expression for the prescribed mass. -/
def circularSpeedSq (G η s r : ℝ) : ℝ := G * mass η s r / r

theorem circularSpeedSq_eq (G η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    circularSpeedSq G η s r = 2 * G * η * s * r / (r + s) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold circularSpeedSq mass
  field_simp [hr0, hrs]
  <;> ring

end InfoGeometry.Physics.SphericalMassProfile
