import Mathlib

/-!
# Exact finite-aperture reference integral

For an isotropic on-axis source, the radial disk integrand includes both
projected area and the radial area Jacobian. Its integral is evaluated by FTC,
not defined to be its closed form. This is geometric acceptance, not photopeak
probability. A volume-to-ray transport change of variables is a separate result.
-/

noncomputable section

namespace InfoGeometry.Nuclear.DetectorDiskIntegral

open MeasureTheory

/-- Azimuth-integrated projected solid-angle density, divided by 4π. -/
def diskDensity (d ρ : ℝ) : ℝ :=
  d * ρ / (2 * Real.sqrt (d ^ 2 + ρ ^ 2) ^ 3)

def diskProbability (d R : ℝ) : ℝ := ∫ ρ in 0..R, diskDensity d ρ

private theorem root_pos {d : ℝ} (hd : 0 < d) (ρ : ℝ) :
    0 < Real.sqrt (d ^ 2 + ρ ^ 2) := by
  apply Real.sqrt_pos.mpr
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hd) (sq_nonneg ρ)

theorem continuous_diskDensity {d : ℝ} (hd : 0 < d) :
    Continuous (diskDensity d) := by
  unfold diskDensity
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro ρ
    exact ne_of_gt (mul_pos (by norm_num) (pow_pos (root_pos hd ρ) 3))

theorem hasDerivAt_diskPrimitive {d : ℝ} (hd : 0 < d) (ρ : ℝ) :
    HasDerivAt
      (fun r : ℝ => (-d / 2) * (Real.sqrt (d ^ 2 + r ^ 2))⁻¹)
      (diskDensity d ρ) ρ := by
  have hq : d ^ 2 + ρ ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hd) (sq_nonneg ρ))
  have hs : Real.sqrt (d ^ 2 + ρ ^ 2) ≠ 0 := ne_of_gt (root_pos hd ρ)
  have hder : HasDerivAt (fun r : ℝ => Real.sqrt (d ^ 2 + r ^ 2))
      ((2 * ρ) / (2 * Real.sqrt (d ^ 2 + ρ ^ 2))) ρ := by
    convert ((((hasDerivAt_id ρ).pow 2).const_add (d ^ 2)).sqrt hq) using 1 <;>
      norm_num
  convert (hder.inv hs).const_mul (-d / 2) using 1 <;>
    unfold diskDensity <;> field_simp [hs] <;> ring

/-- Exact disk acceptance derived from its projected solid-angle integral. -/
theorem diskProbability_eq {d : ℝ} (hd : 0 < d) (R : ℝ) :
    diskProbability d R = (1 - d / Real.sqrt (d ^ 2 + R ^ 2)) / 2 := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hR0 : Real.sqrt (d ^ 2 + R ^ 2) ≠ 0 := ne_of_gt (root_pos hd R)
  unfold diskProbability
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ρ _ => hasDerivAt_diskPrimitive hd ρ)
    ((continuous_diskDensity hd).intervalIntegrable 0 R)]
  have h0 : Real.sqrt (d ^ 2 + (0 : ℝ) ^ 2) = d := by
    rw [sq (0 : ℝ), mul_zero, add_zero, Real.sqrt_sq hd.le]
  change (-d / 2) * (Real.sqrt (d ^ 2 + R ^ 2))⁻¹ - (-d / 2) * (Real.sqrt (d ^ 2 + (0 : ℝ) ^ 2))⁻¹ = _
  rw [h0]
  field_simp [hd0, hR0]
  ring

theorem diskProbability_nonneg {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) :
    0 ≤ diskProbability d R := by
  apply intervalIntegral.integral_nonneg hR
  intro ρ hρ
  unfold diskDensity
  exact div_nonneg (mul_nonneg hd.le hρ.1)
    (mul_nonneg (by norm_num) (pow_nonneg (Real.sqrt_nonneg _) _))

theorem diskProbability_le_half {d : ℝ} (hd : 0 < d) (R : ℝ) :
    diskProbability d R ≤ 1 / 2 := by
  rw [diskProbability_eq hd R]
  have h := div_nonneg hd.le (Real.sqrt_nonneg (d ^ 2 + R ^ 2))
  linarith

/-- Rationalization exposes the finite-aperture correction. -/
theorem diskProbability_rationalized {d : ℝ} (hd : 0 < d) (R : ℝ) :
    diskProbability d R = R ^ 2 /
      (2 * Real.sqrt (d ^ 2 + R ^ 2) * (Real.sqrt (d ^ 2 + R ^ 2) + d)) := by
  have hs := root_pos hd R
  have hsum : 0 < Real.sqrt (d ^ 2 + R ^ 2) + d := add_pos hs hd
  have hs2 := Real.sq_sqrt (show 0 ≤ d ^ 2 + R ^ 2 by positivity)
  rw [diskProbability_eq hd R]
  field_simp [ne_of_gt hs, ne_of_gt hsum] <;> nlinarith [hs2]

private theorem root_ge {d : ℝ} (hd : 0 < d) (R : ℝ) :
    d ≤ Real.sqrt (d ^ 2 + R ^ 2) := by
  have hs2 := Real.sq_sqrt (show 0 ≤ d ^ 2 + R ^ 2 by positivity)
  by_contra h
  have hlt : Real.sqrt (d ^ 2 + R ^ 2) < d := lt_of_not_ge h
  have hm := mul_pos (sub_pos.mpr hlt) (add_pos hd (root_pos hd R))
  nlinarith [sq_nonneg R]

/-- The familiar area/(4πd²) expression is an upper bound here, not the
exact finite-disk integral. -/
theorem diskProbability_le_inverseSquare {d : ℝ} (hd : 0 < d) (R : ℝ) :
    diskProbability d R ≤ R ^ 2 / (4 * d ^ 2) := by
  have hs := root_ge hd R
  have hm := mul_le_mul hs (add_le_add_right hs d)
    (show 0 ≤ d + d by linarith) (Real.sqrt_nonneg (d ^ 2 + R ^ 2))
  have hden : 4 * d ^ 2 ≤
      2 * Real.sqrt (d ^ 2 + R ^ 2) * (Real.sqrt (d ^ 2 + R ^ 2) + d) := by
    nlinarith [hm]
  rw [diskProbability_rationalized hd R]
  exact div_le_div_of_nonneg_left (sq_nonneg R) (by positivity) hden

end InfoGeometry.Nuclear.DetectorDiskIntegral
