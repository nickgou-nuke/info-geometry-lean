/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.DetectorCrossSectionDuality

/-!
# Virtual-point-detector cross section: the normalized quadratic bridge

This module proves algebraic identities over `Real` using the existing
`DetectorCrossSectionDuality.singlesResponse` and `virtualSummingArea` owners.
The geometry predictor is the specified inverse-square model. Quadratic-model
identities and deterministic signed-residual identities are kept separate.
The results do not prove that a physical detector obeys these laws,
that a net spectral deficit is entirely summing-out, or that a fitted virtual
point is a material detector boundary.

`geometryArea` has physical units of length squared when the transfer is
dimensionless. Unit interpretation is external to the scalar `Real` carrier.
`inferredCrossSection` is signed; its nonnegativity requires an additional
nonpositive quadratic coefficient. `a = 1` removes the distance-dependent
physical-baseline defect when the free response is the transfer itself.
For arbitrary `a`, the fitted baseline is `a * transfer`.

The quadratic response is `singlesResponse a (-b) x (x ^ 2)`, so the signed
coefficient `b` corresponds to the negation of the existing loss coefficient.
No new response definition is introduced. The theorem
`inferred_cross_section_eq_virtual_summing_area` identifies the inferred area
with the existing `virtualSummingArea` for an affine geometric linearizer.

All results are scalar algebra conditional on the stated model and denominator
hypotheses. They neither verify simulation outputs nor establish an empirical
fit, a microscopic detector law, or a statistical error model.
-/

noncomputable section

namespace InfoGeometry.Probability.DetectorCrossSectionDuality.Response

/-- Dimensionless transfer for a dimensionful inverse-square geometry scale. -/
def transfer (geometryArea distance : ℝ) : ℝ := geometryArea / distance ^ 2

/-- Signed area inferred relative to the fitted baseline `a * x`. -/
def inferredCrossSection (geometryArea a b : ℝ) : ℝ :=
  -(4 * Real.pi) * geometryArea * b / a

/-- Spherical area times a fractional deficit, for a specified baseline. -/
def crossSectionFromDeficit (distance baseline observed : ℝ) : ℝ :=
  4 * Real.pi * distance ^ 2 * (1 - observed / baseline)

/-- The normalized quadratic is exactly a baseline times a spherical loss factor. -/
theorem response_factorization (geometryArea distance a b : ℝ)
    (hr : distance ≠ 0) (ha : a ≠ 0) :
    singlesResponse a (-b) (transfer geometryArea distance)
      ((transfer geometryArea distance) ^ 2) =
      a * transfer geometryArea distance *
        (1 - inferredCrossSection geometryArea a b /
          (4 * Real.pi * distance ^ 2)) := by
  dsimp [singlesResponse, transfer, inferredCrossSection]
  field_simp [hr, ha, Real.pi_ne_zero]

/-- The fractional-deficit construction recovers the same constant area. -/
theorem recover_fitted_cross_section (geometryArea distance a b : ℝ)
    (hL : geometryArea ≠ 0) (hr : distance ≠ 0) (ha : a ≠ 0) :
    crossSectionFromDeficit distance (a * transfer geometryArea distance)
      (singlesResponse a (-b) (transfer geometryArea distance)
        ((transfer geometryArea distance) ^ 2)) =
      inferredCrossSection geometryArea a b := by
  dsimp [crossSectionFromDeficit, singlesResponse, transfer, inferredCrossSection]
  field_simp [hL, hr, ha]
  ring

/-- A nonpositive curvature gives a nonnegative loss area on a positive scale. -/
theorem inferred_cross_section_nonneg (geometryArea a b : ℝ)
    (hL : 0 ≤ geometryArea) (ha : 0 < a) (hb : b ≤ 0) :
    0 ≤ inferredCrossSection geometryArea a b := by
  dsimp [inferredCrossSection]
  apply div_nonneg _ ha.le
  have hpi : 0 ≤ 4 * Real.pi := by positivity
  convert mul_nonneg (mul_nonneg hpi hL) (neg_nonneg.mpr hb) using 1
  ring

/-- Negative curvature on a strictly positive scale gives a strictly positive area. -/
theorem inferred_cross_section_pos (geometryArea a b : ℝ)
    (hL : 0 < geometryArea) (ha : 0 < a) (hb : b < 0) :
    0 < inferredCrossSection geometryArea a b := by
  dsimp [inferredCrossSection]
  apply div_pos _ ha
  have hpi : 0 < 4 * Real.pi := by positivity
  convert mul_pos (mul_pos hpi hL) (neg_pos.mpr hb) using 1
  ring

/-- A gain coefficient can be represented as a signed area, without a loss claim. -/
theorem inferred_cross_section_nonpos_of_gain (geometryArea a b : ℝ)
    (hL : 0 ≤ geometryArea) (ha : 0 < a) (hb : 0 ≤ b) :
    inferredCrossSection geometryArea a b ≤ 0 := by
  dsimp [inferredCrossSection]
  apply div_nonpos_of_nonpos_of_nonneg _ ha.le
  have hpi : 0 ≤ 4 * Real.pi := by positivity
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpi) hL) hb

/-- With the physical free baseline `x`, a nonunit fitted slope leaves a distance term. -/
theorem physical_baseline_defect (geometryArea distance a b : ℝ)
    (hL : geometryArea ≠ 0) (hr : distance ≠ 0) :
    crossSectionFromDeficit distance (transfer geometryArea distance)
      (singlesResponse a (-b) (transfer geometryArea distance)
        ((transfer geometryArea distance) ^ 2)) =
      4 * Real.pi * (1 - a) * distance ^ 2 - 4 * Real.pi * b * geometryArea := by
  dsimp [crossSectionFromDeficit, singlesResponse, transfer]
  field_simp [hL, hr]
  ring

/-- Unit slope in the exact quadratic model removes the distance-dependent baseline defect. -/
theorem unit_slope_physical_cross_section (geometryArea distance b : ℝ)
    (hL : geometryArea ≠ 0) (hr : distance ≠ 0) :
    crossSectionFromDeficit distance (transfer geometryArea distance)
      (singlesResponse 1 (-b) (transfer geometryArea distance)
        ((transfer geometryArea distance) ^ 2)) =
      -(4 * Real.pi) * b * geometryArea := by
  rw [physical_baseline_defect geometryArea distance 1 b hL hr]
  ring

/-- Equal physical-baseline areas at two different squared distances force unit slope. -/
theorem constant_physical_area_forces_unit_slope
    (geometryArea r1 r2 a b : ℝ) (hL : geometryArea ≠ 0)
    (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) (hsep : r1 ^ 2 ≠ r2 ^ 2)
    (hconstant :
      crossSectionFromDeficit r1 (transfer geometryArea r1)
          (singlesResponse a (-b) (transfer geometryArea r1)
            ((transfer geometryArea r1) ^ 2)) =
        crossSectionFromDeficit r2 (transfer geometryArea r2)
          (singlesResponse a (-b) (transfer geometryArea r2)
            ((transfer geometryArea r2) ^ 2))) :
    a = 1 := by
  rw [physical_baseline_defect geometryArea r1 a b hL hr1,
    physical_baseline_defect geometryArea r2 a b hL hr2] at hconstant
  have hproduct : (4 * Real.pi * (1 - a)) * (r1 ^ 2 - r2 ^ 2) = 0 := by
    nlinarith [hconstant]
  have hcoefficient : 4 * Real.pi * (1 - a) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right (sub_ne_zero.mpr hsep)
  have hunit : 1 - a = 0 :=
    (mul_eq_zero.mp hcoefficient).resolve_left
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  linarith

/-- The manuscript gauge `x = G * r0^2 / r^2` must be retained in the inferred area. -/
theorem gauge_conversion (G r0 a b : ℝ) :
    inferredCrossSection (G * r0 ^ 2) a b =
      -4 * Real.pi * (b / a) * G * r0 ^ 2 := by
  dsimp [inferredCrossSection]
  ring

/-- The affine inverse-square-root fit gives geometry area `1 / beta^2`. -/
theorem affine_transfer_conversion (alpha beta d : ℝ) (hbeta : beta ≠ 0) :
    transfer (1 / beta ^ 2) (d + alpha / beta) =
      1 / (alpha + beta * d) ^ 2 := by
  dsimp [transfer]
  have hfactor : d + alpha / beta = (alpha + beta * d) / beta := by
    field_simp [hbeta]
    ring
  rw [hfactor, div_pow, div_div]
  field_simp [hbeta]

/-- The same area from the affine geometry slope avoids treating `G` as one. -/
theorem affine_cross_section_conversion (beta a b : ℝ) :
    inferredCrossSection (1 / beta ^ 2) a b =
      -4 * Real.pi * b / (a * beta ^ 2) := by
  dsimp [inferredCrossSection]
  ring

/-- Area for the count-rate proxy `X = H / r^2`, `S = c*X - k*X^2`. -/
theorem sum_proxy_conversion (H c k : ℝ) :
    inferredCrossSection H c (-k) = 4 * Real.pi * H * k / c := by
  dsimp [inferredCrossSection]
  ring

/-- Algebraic link to the established loss-area convention using `H = 1/slope^2`. -/
theorem sum_proxy_linearizer_conversion (slope c k : ℝ) :
    inferredCrossSection (1 / slope ^ 2) c (-k) =
      4 * Real.pi * k / (c * slope ^ 2) := by
  dsimp [inferredCrossSection]
  ring

/-- The inferred area uses exactly the existing virtual-summing-area owner
when the proxy scale is the inverse square of its affine linearizer slope. -/
theorem inferred_cross_section_eq_virtual_summing_area (slope c k : ℝ) :
    inferredCrossSection (1 / slope ^ 2) c (-k) = virtualSummingArea k c slope := by
  exact sum_proxy_linearizer_conversion slope c k

/-- Retained and diverted events conserve the modeled primary event rate. -/
theorem event_partition_conservation (baseline p : ℝ) :
    baseline * (1 - p) + baseline * p = baseline := by
  ring

/-- Both branches are nonnegative when the conditional diversion is a probability. -/
theorem event_partition_nonneg (baseline p : ℝ)
    (hB : 0 ≤ baseline) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ baseline * (1 - p) ∧ 0 ≤ baseline * p := by
  exact ⟨mul_nonneg hB (sub_nonneg.mpr hp1), mul_nonneg hB hp⟩

/-- The spherical loss factor lies in `[0, 1]` on the stated area range. -/
theorem spherical_loss_probability_bounds (lossArea distance : ℝ)
    (hr : distance ≠ 0) (hs0 : 0 ≤ lossArea)
    (hs1 : lossArea ≤ 4 * Real.pi * distance ^ 2) :
    0 ≤ lossArea / (4 * Real.pi * distance ^ 2) ∧
      lossArea / (4 * Real.pi * distance ^ 2) ≤ 1 := by
  have hden : 0 < 4 * Real.pi * distance ^ 2 := by positivity
  exact ⟨div_nonneg hs0 hden.le, (div_le_one hden).mpr hs1⟩

/-- A single count rate times an inverse-square conditional loss is inverse-fourth order. -/
theorem pair_rate_inverse_fourth (emissionRate peakArea lossArea distance : ℝ)
    (hr : distance ≠ 0) :
    (emissionRate * peakArea / (4 * Real.pi * distance ^ 2)) *
      (lossArea / (4 * Real.pi * distance ^ 2)) =
      emissionRate * peakArea * lossArea /
        ((4 * Real.pi) ^ 2 * distance ^ 4) := by
  field_simp [hr, Real.pi_ne_zero]

/-! ## Residuals: an empirical quadratic need not be an exact response law

The residual below is the actual response minus the quadratic prediction. It
may have either sign. These identities propagate a supplied deterministic
residual or bound; they make no statistical or confidence-interval claim.
-/

/-- Adding a signed response residual changes the inferred area by an exactly
linear amount. The baseline is explicit, so this also applies to a physical
baseline `transfer geometryArea distance`. -/
theorem cross_section_residual_difference
    (distance baseline observed residual : ℝ) :
    crossSectionFromDeficit distance baseline (observed + residual) -
        crossSectionFromDeficit distance baseline observed =
      -(4 * Real.pi) * distance ^ 2 * residual / baseline := by
  dsimp [crossSectionFromDeficit]
  ring

/-- The actual physical-baseline area retains both the nonunit-slope defect
and the signed quadratic-fit residual. The geometry law remains a hypothesis
encoded by `transfer`; the observed response need not be exactly quadratic. -/
theorem physical_baseline_with_residual
    (geometryArea distance a b residual : ℝ)
    (hL : geometryArea ≠ 0) (hr : distance ≠ 0) :
    crossSectionFromDeficit distance (transfer geometryArea distance)
        (singlesResponse a (-b) (transfer geometryArea distance)
          ((transfer geometryArea distance) ^ 2) + residual) =
      4 * Real.pi * (1 - a) * distance ^ 2 - 4 * Real.pi * b * geometryArea -
        4 * Real.pi * distance ^ 2 * residual / transfer geometryArea distance := by
  have h := cross_section_residual_difference distance (transfer geometryArea distance)
    (singlesResponse a (-b) (transfer geometryArea distance)
      ((transfer geometryArea distance) ^ 2)) residual
  rw [physical_baseline_defect geometryArea distance a b hL hr] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  ring

/-- Converting the fitted-baseline area to the actual physical-baseline area
requires a factor `a`, the baseline defect, and the residual correction. -/
theorem physical_baseline_inferred_with_residual
    (geometryArea distance a b residual : ℝ)
    (hL : geometryArea ≠ 0) (hr : distance ≠ 0) (ha : a ≠ 0) :
    crossSectionFromDeficit distance (transfer geometryArea distance)
        (singlesResponse a (-b) (transfer geometryArea distance)
          ((transfer geometryArea distance) ^ 2) + residual) =
      a * inferredCrossSection geometryArea a b +
        4 * Real.pi * (1 - a) * distance ^ 2 -
        4 * Real.pi * distance ^ 2 * residual / transfer geometryArea distance := by
  rw [physical_baseline_with_residual geometryArea distance a b residual hL hr]
  dsimp [inferredCrossSection]
  field_simp [ha]
  ring

/-- A deterministic response-residual bound yields a deterministic area-error
bound for a positive baseline. Substituting `baseline = transfer L r` makes
the amplification factor explicit as `4 * pi * r^2 / x`; this is not a
statistical uncertainty estimate. -/
theorem cross_section_residual_error_bound
    (distance baseline observed residual epsilon : ℝ)
    (hbaseline : 0 < baseline) (hresidual : |residual| ≤ epsilon) :
    |crossSectionFromDeficit distance baseline (observed + residual) -
        crossSectionFromDeficit distance baseline observed| ≤
      4 * Real.pi * distance ^ 2 * epsilon / baseline := by
  rw [cross_section_residual_difference]
  have harea : 0 ≤ 4 * Real.pi * distance ^ 2 := by positivity
  have habs : |-(4 * Real.pi) * distance ^ 2 * residual / baseline| =
      (4 * Real.pi * distance ^ 2) * |residual| / baseline := by
    rw [abs_div, abs_of_pos hbaseline, abs_mul, abs_mul, abs_neg,
      abs_of_pos (show 0 < 4 * Real.pi by positivity), abs_of_nonneg (sq_nonneg distance)]
  rw [habs]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hresidual harea)
    hbaseline.le

end InfoGeometry.Probability.DetectorCrossSectionDuality.Response
