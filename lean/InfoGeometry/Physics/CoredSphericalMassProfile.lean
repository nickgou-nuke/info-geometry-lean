/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SphericalMassProfile

/-! # A cored spherical mass profile with a derived density

The prescribed mass `2 * η * s * r³ / (r + s)²` is the earlier spherical mass
profile multiplied by `r / (r + s)`. Its density is constructed from its actual
derivative, divided by `4 * π * r²`. For positive scale and radius, the density
has an explicit rational form, a finite central one-sided limit, and the same
outer inverse-square coefficient as the earlier profile.

The raw quotient at radius zero uses total division and is not the continuous
extension with the nonzero central limit. All central density conclusions are
therefore stated as limits from positive radii. These are analytic consequences
of a chosen profile, not a field-equation derivation or a uniqueness claim.
-/

noncomputable section

namespace InfoGeometry.Physics.SphericalMassProfile

open Filter Set
open scoped Topology

/-- A prescribed mass profile whose leading central order is cubic. -/
def coreMass (η s r : ℝ) : ℝ :=
  2 * η * s * r ^ 3 / (r + s) ^ 2

/-- The cored profile is obtained by attenuating the previously defined mass. -/
theorem coreMass_eq_mass_mul (η s r : ℝ) (hrs : r + s ≠ 0) :
    coreMass η s r = mass η s r * (r / (r + s)) := by
  unfold coreMass mass
  field_simp [hrs]
  <;> ring

/-- Differentiate the prescribed mass using the native quotient rule. -/
theorem hasDerivAt_coreMass (η s r : ℝ) (hrs : r + s ≠ 0) :
    HasDerivAt (coreMass η s)
      (2 * η * s * r ^ 2 * (r + 3 * s) / (r + s) ^ 3) r := by
  have hnum : HasDerivAt (fun x : ℝ => 2 * η * s * x ^ 3)
      (2 * η * s * (3 * r ^ 2)) r := by
    convert ((hasDerivAt_id r).pow 3).const_mul (2 * η * s) using 1 <;>
      simp only [id_eq, Nat.cast_ofNat, mul_one]
  have hquot := hnum.div (((hasDerivAt_id r).add_const s).pow 2)
    (pow_ne_zero 2 hrs)
  convert hquot using 1 <;> dsimp [coreMass, id] <;>
    field_simp [hrs] <;> ring

theorem deriv_coreMass (η s r : ℝ) (hrs : r + s ≠ 0) :
    deriv (coreMass η s) r =
      2 * η * s * r ^ 2 * (r + 3 * s) / (r + s) ^ 3 :=
  (hasDerivAt_coreMass η s r hrs).deriv

/-- Density from the actual radial derivative; the origin is treated by a limit. -/
def coreDensity (η s r : ℝ) : ℝ :=
  deriv (coreMass η s) r / (4 * Real.pi * r ^ 2)

theorem coreDensity_eq (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    coreDensity η s r = η * s * (r + 3 * s) /
      (2 * Real.pi * (r + s) ^ 3) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [coreDensity, deriv_coreMass η s r hrs]
  field_simp [hr0, hrs, hπ]
  <;> ring

theorem coreDensity_pos (η s r : ℝ) (hη : 0 < η) (hs : 0 < s) (hr : 0 < r) :
    0 < coreDensity η s r := by
  rw [coreDensity_eq η s r hs hr]
  positivity

/-- Cancelling the explicit cubic factor yields the exact central mass ratio. -/
theorem coreMass_div_radius_cube (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    coreMass η s r / r ^ 3 = 2 * η * s / (r + s) ^ 2 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold coreMass
  field_simp [hr0, hrs]
  <;> ring

/-- The exact positive-radius central mass coefficient. -/
theorem tendsto_coreMass_div_radius_cube_zero (η s : ℝ) (hs : 0 < s) :
    Tendsto (fun r : ℝ => coreMass η s r / r ^ 3) (𝓝[>] 0)
      (𝓝 (2 * η / s)) := by
  have hden : Tendsto (fun r : ℝ => (r + s) ^ 2) (𝓝 0)
      (𝓝 ((0 + s) ^ 2)) :=
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
  exact (coreMass_div_radius_cube η s r hs hr).symm

/-- A finite central density is a proved one-sided limit of the derivative quotient. -/
theorem tendsto_coreDensity_zero (η s : ℝ) (hs : 0 < s) :
    Tendsto (coreDensity η s) (𝓝[>] 0) (𝓝 (3 * η / (2 * Real.pi * s))) := by
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
    field_simp [hs0, hπ]
    <;> ring
  rw [hc] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (coreDensity_eq η s r hs hr).symm

/-- Express the scaled outer density using inverse radius. -/
theorem radius_sq_mul_coreDensity (η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    r ^ 2 * coreDensity η s r =
      η * s * (1 + 3 * s * r⁻¹) /
        (2 * Real.pi * (1 + s * r⁻¹) ^ 3) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hden : 1 + s * r⁻¹ ≠ 0 := ne_of_gt (by positivity)
  rw [coreDensity_eq η s r hs hr]
  field_simp [hr0, hrs, hπ, hden]
  <;> ring

/-- The cored profile preserves the original outer inverse-square coefficient. -/
theorem tendsto_radius_sq_mul_coreDensity_atTop (η s : ℝ) (hs : 0 < s) :
    Tendsto (fun r : ℝ => r ^ 2 * coreDensity η s r) atTop
      (𝓝 (η * s / (2 * Real.pi))) := by
  have hi : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto (fun r : ℝ => η * s * (1 + 3 * s * r⁻¹)) atTop
      (𝓝 (η * s * (1 + 3 * s * 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hi))
  have hden : Tendsto (fun r : ℝ => 2 * Real.pi * (1 + s * r⁻¹) ^ 3) atTop
      (𝓝 (2 * Real.pi * (1 + s * 0) ^ 3)) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.add (tendsto_const_nhds.mul hi)).pow 3)
  have hden0 : 2 * Real.pi * (1 + s * 0) ^ 3 ≠ 0 := by
    simpa using ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  have h := hnum.div hden hden0
  simp only [mul_zero, add_zero, one_pow, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (radius_sq_mul_coreDensity η s r hs hr).symm

/-- The spherical circular-speed expression attached to the prescribed core mass. -/
def coreCircularSpeedSq (G η s r : ℝ) : ℝ := G * coreMass η s r / r

theorem coreCircularSpeedSq_eq (G η s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    coreCircularSpeedSq G η s r = 2 * G * η * s * r ^ 2 / (r + s) ^ 2 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrs : r + s ≠ 0 := ne_of_gt (add_pos hr hs)
  unfold coreCircularSpeedSq coreMass
  field_simp [hr0, hrs]
  <;> ring

/-- The squared circular-speed expression tends to a finite outer constant. -/
theorem tendsto_coreCircularSpeedSq_atTop (G η s : ℝ) (hs : 0 < s) :
    Tendsto (coreCircularSpeedSq G η s) atTop (𝓝 (2 * G * η * s)) := by
  have hi : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hden : Tendsto (fun r : ℝ => (1 + s * r⁻¹) ^ 2) atTop
      (𝓝 ((1 + s * 0) ^ 2)) :=
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
  rw [coreCircularSpeedSq_eq G η s r hs hr]
  field_simp [hr0, hrs, hdenr]
  <;> ring

end InfoGeometry.Physics.SphericalMassProfile

end
