/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SphericalMassProfile

/-!
# A prescribed spherical mass profile with a finite central density limit

The phenomenological alternative `2 * η * s * r³ / (r + s)²` is distinct
from the source paper's mass profile in `SphericalMassProfile`. Its density
is defined from the actual derivative divided by `4 * π * r²`. For positive
parameters it has a finite right-hand central density limit and the same
outer `1 / r²` coefficient as the original profile.

No uniqueness, necessity, field equation, entropy-to-gravity law, or empirical
fit is claimed. The central statement concerns the limit from positive radii;
the literal quotient definition at `r = 0` uses Lean's totalized division and
has value zero.
-/

noncomputable section

namespace InfoGeometry.Physics.CoredSphericalMassProfile

open Filter Set
open scoped Topology

/-- A new prescribed alternative, not the profile printed in the paper. -/
def mass (η s r : ℝ) : ℝ :=
  2 * η * s * r ^ 3 / (r + s) ^ 2

/-- The alternative mass attenuates the original by `r / (r + s)`. -/
theorem mass_eq_original_mul (η s r : ℝ) (hrs : r + s ≠ 0) :
    mass η s r = SphericalMassProfile.mass η s r * (r / (r + s)) := by
  unfold mass SphericalMassProfile.mass
  field_simp [hrs] <;> ring

/-- The derivative is constructed by the native power and quotient rules. -/
theorem hasDerivAt_mass (η s r : ℝ) (hrs : r + s ≠ 0) :
    HasDerivAt (mass η s)
      (2 * η * s * r ^ 2 * (r + 3 * s) / (r + s) ^ 3) r := by
  have hnum : HasDerivAt (fun x : ℝ => 2 * η * s * x ^ 3)
      (2 * η * s * (3 * r ^ 2)) r := by
    convert ((hasDerivAt_id r).pow 3).const_mul (2 * η * s) using 1
    · funext x
      rfl
    · simp only [id_eq]
      ring
  have hden : HasDerivAt (fun x : ℝ => (x + s) ^ 2) (2 * (r + s)) r := by
    convert ((hasDerivAt_id r).add_const s).pow 2 using 1
    · funext x
      rfl
    · simp only [id_eq]
      ring
  have hquot := hnum.div hden (pow_ne_zero 2 hrs)
  convert hquot using 1
  · funext x
    rfl
  · field_simp [hrs]
    <;> ring

theorem deriv_mass (η s r : ℝ) (hrs : r + s ≠ 0) :
    deriv (mass η s) r =
      2 * η * s * r ^ 2 * (r + 3 * s) / (r + s) ^ 3 :=
  (hasDerivAt_mass η s r hrs).deriv

/-- Spherical density from the actual derivative of the prescribed mass. -/
def density (η s r : ℝ) : ℝ :=
  deriv (mass η s) r / (4 * Real.pi * r ^ 2)

/-- This totalized value is separate from the limit from positive radii. -/
@[simp] theorem density_zero (η s : ℝ) : density η s 0 = 0 := by
  simp [density]

theorem density_eq (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    density η s r = η * s * (r + 3 * s) /
      (2 * Real.pi * (r + s) ^ 3) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [density, deriv_mass η s r hrs]
  field_simp [hr0, hrs, hπ] <;> ring

theorem density_pos (η s r : ℝ) (hη : 0 < η) (hs : 0 < s) (hr : 0 < r) :
    0 < density η s r := by
  rw [density_eq η s r hs hr]
  positivity

/-- Exact finite central density limit of the alternative profile. -/
theorem tendsto_density_zero (η s : ℝ) (hs : 0 < s) :
    Tendsto (density η s) (𝓝[>] 0) (𝓝 (3 * η / (2 * Real.pi * s))) := by
  have hnum : Tendsto (fun r : ℝ => η * s * (r + 3 * s)) (𝓝 0)
      (𝓝 (η * s * (0 + 3 * s))) :=
    tendsto_const_nhds.mul (tendsto_id.add tendsto_const_nhds)
  have hden : Tendsto (fun r : ℝ => 2 * Real.pi * (r + s) ^ 3) (𝓝 0)
      (𝓝 (2 * Real.pi * (0 + s) ^ 3)) :=
    tendsto_const_nhds.mul ((tendsto_id.add tendsto_const_nhds).pow 3)
  have hden0 : 2 * Real.pi * (0 + s) ^ 3 ≠ 0 := ne_of_gt (by positivity)
  have h : Tendsto
      (fun r : ℝ => η * s * (r + 3 * s) / (2 * Real.pi * (r + s) ^ 3))
      (𝓝[>] 0) (𝓝 (η * s * (0 + 3 * s) / (2 * Real.pi * (0 + s) ^ 3))) :=
    (hnum.div hden hden0).mono_left nhdsWithin_le_nhds
  have hc : η * s * (0 + 3 * s) / (2 * Real.pi * (0 + s) ^ 3) =
      3 * η / (2 * Real.pi * s) := by
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [hs0, hπ] <;> ring
  rw [hc] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (density_eq η s r hs hr).symm

/-- An exact inverse-radius expression for the outer scaled density. -/
theorem radius_sq_mul_density (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    r ^ 2 * density η s r =
      η * s * (1 + 3 * s * r⁻¹) /
        (2 * Real.pi * (1 + s * r⁻¹) ^ 3) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hden : 1 + s * r⁻¹ ≠ 0 := ne_of_gt (by positivity)
  rw [density_eq η s r hs hr]
  field_simp [hr0, hrs, hπ, hden] <;> ring

/-- The alternative retains the original outer `1 / r²` coefficient. -/
theorem tendsto_radius_sq_mul_density_atTop (η s : ℝ) (hs : 0 < s) :
    Tendsto (fun r : ℝ => r ^ 2 * density η s r) atTop
      (𝓝 (η * s / (2 * Real.pi))) := by
  have hi : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto (fun r : ℝ => η * s * (1 + 3 * s * r⁻¹)) atTop
      (𝓝 (η * s * (1 + 3 * s * 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hi))
  have hden : Tendsto (fun r : ℝ => 2 * Real.pi * (1 + s * r⁻¹) ^ 3) atTop
      (𝓝 (2 * Real.pi * (1 + s * 0) ^ 3)) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.add (tendsto_const_nhds.mul hi)).pow 3)
  have hden0 : 2 * Real.pi * (1 + s * 0) ^ 3 ≠ 0 := by
    positivity
  have h := hnum.div hden hden0
  simp only [mul_zero, add_zero, one_pow, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (radius_sq_mul_density η s r hs hr).symm



/-- The cored mass has an exact cubic-normalized expression away from the origin. -/
theorem mass_div_radius_cube (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    mass η s r / r ^ 3 = 2 * η * s / (r + s) ^ 2 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold mass
  field_simp [hr0, hrs]
  <;> ring

/-- The cubic-normalized core mass has the finite central value `2η/s`. -/
theorem tendsto_mass_div_radius_cube_zero (η s : ℝ) (hs : 0 < s) :
    Tendsto (fun r : ℝ => mass η s r / r ^ 3) (𝓝[>] 0) (𝓝 (2 * η / s)) := by
  have hden : Tendsto (fun r : ℝ => (r + s) ^ 2) (𝓝 0) (𝓝 ((0 + s) ^ 2)) :=
    (tendsto_id.add tendsto_const_nhds).pow 2
  have hden0 : (0 + s) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h : Tendsto (fun r : ℝ => 2 * η * s / (r + s) ^ 2) (𝓝[>] 0)
      (𝓝 (2 * η * s / (0 + s) ^ 2)) :=
    (tendsto_const_nhds.div hden hden0).mono_left nhdsWithin_le_nhds
  have hc : 2 * η * s / (0 + s) ^ 2 = 2 * η / s := by
    field_simp [ne_of_gt hs]
    <;> ring
  rw [hc] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (mass_div_radius_cube η s r hs hr).symm

/-- Squared circular speed for the prescribed cored mass profile. -/
def circularSpeedSq (G η s r : ℝ) : ℝ := G * mass η s r / r

/-- Exact positive-radius formula for the cored circular speed. -/
theorem circularSpeedSq_eq (G η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    circularSpeedSq G η s r = 2 * G * η * s * r ^ 2 / (r + s) ^ 2 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold circularSpeedSq mass
  field_simp [hr0, hrs]
  <;> ring

/-- The cored circular speed approaches a finite outer value. -/
theorem tendsto_circularSpeedSq_atTop (G η s : ℝ) (hs : 0 < s) :
    Tendsto (circularSpeedSq G η s) atTop (𝓝 (2 * G * η * s)) := by
  have hi : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hden : Tendsto (fun r : ℝ => (1 + s * r⁻¹) ^ 2) atTop (𝓝 ((1 + s * 0) ^ 2)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hi)).pow 2
  have hden0 : (1 + s * 0) ^ 2 ≠ 0 := by norm_num
  have h : Tendsto (fun r : ℝ => 2 * G * η * s / (1 + s * r⁻¹) ^ 2) atTop
      (𝓝 (2 * G * η * s / (1 + s * 0) ^ 2)) :=
    tendsto_const_nhds.div hden hden0
  simp only [mul_zero, add_zero, one_pow, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have hdenr : 1 + s * r⁻¹ ≠ 0 := ne_of_gt (by positivity)
  rw [circularSpeedSq_eq G η s r hs hr]
  field_simp [hr0, hrs, hdenr]
  <;> ring

end InfoGeometry.Physics.CoredSphericalMassProfile
