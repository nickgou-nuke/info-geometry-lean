/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.DetectorCrossSectionResponse
import InfoGeometry.Nuclear.ApollonianBipolarField
import Mathlib.Analysis.Real.Sqrt

/-!
# Receiving area from the virtual-point-detector linearizer

This module uses the existing `geometricCoupling`, `effectiveArea`, and
`photopeakArea` definitions. It introduces no additional response or area API.
The receiving response is `epsilon = geometricCoupling Sigma rho Real.pi`,
namely `Sigma / (4 * pi * rho^2)`. For an absolute-efficiency linearizer
`1 / sqrt epsilon = m*d + c`, the corresponding distance is `d + c/m` and
the area is the existing `effectiveArea m Real.pi = 4*pi/m^2`.

For normalized transfer, the absolute reference efficiency must be retained:
`Sigma = 4*pi*epsilonRef*L`, and an affine normalized inverse-square-root
predictor has `L = 1/beta^2`. For a count-rate linearizer the emitted photon
rate `A*p` must instead be retained. The receiving area and the signed
conditional coincidence-transfer area have
different roles in the first-order and second-order response.

All carriers are real. The results are conditional scalar identities for the
given inverse-square model and exact linearizer relations. Positive square-root
branches and nonzero denominators are stated explicitly. Length, efficiency,
and count-rate units are interpretations external to the `Real` carrier.
These theorems do not identify a material detector surface, establish a fit to
measurements, validate a simulation, or propagate statistical uncertainties.
-/

noncomputable section

namespace InfoGeometry.Probability.DetectorCrossSectionDuality.ReceivingArea

open InfoGeometry.Nuclear.ApollonianBipolarField (geometricCoupling effectiveArea)

/-- An absolute reference efficiency supplies the area scale removed by a
normalized inverse-square transfer. This is an extraction from a supplied
transfer identity, not a calibration from normalized data alone. -/
theorem receiving_area_of_normalized_transfer
    (area referenceEfficiency geometryArea distance : ℝ)
    (href : referenceEfficiency ≠ 0) (hr : distance ≠ 0)
    (htransfer : geometricCoupling area distance Real.pi / referenceEfficiency =
      Response.transfer geometryArea distance) :
    area = 4 * Real.pi * referenceEfficiency * geometryArea := by
  dsimp [geometricCoupling, Response.transfer] at htransfer
  have hscaled := congrArg
    (fun z : ℝ => z * (4 * Real.pi * distance ^ 2) * referenceEfficiency) htransfer
  field_simp [href, hr, Real.pi_ne_zero] at hscaled
  nlinarith [hscaled]

/-- The reciprocal-square-root linearizer and inverse-square response are
equivalent on their positive branches. -/
theorem inverse_sqrt_eq_iff_inverse_square (efficiency affineValue : ℝ)
    (he : 0 < efficiency) (hv : 0 < affineValue) :
    1 / Real.sqrt efficiency = affineValue ↔ efficiency = 1 / affineValue ^ 2 := by
  constructor
  · intro h
    have hsquare := congrArg (fun z : ℝ => z ^ 2) h
    have hinverse : 1 / efficiency = affineValue ^ 2 := by
      simpa only [div_pow, one_pow, Real.sq_sqrt he.le] using hsquare
    have hback := congrArg (fun z : ℝ => 1 / z) hinverse
    simpa only [one_div_one_div] using hback
  · intro h
    rw [h, Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num), Real.sqrt_one,
      Real.sqrt_sq hv.le, one_div_one_div]

/-- An absolute-efficiency affine linearizer determines the receiving area.
Its positive affine value excludes the zero-distance pole. A positive slope
additionally makes `d + c/m` a positive physical distance. -/
theorem receiving_area_of_affine_efficiency_linearizer
    (area slope intercept displacement : ℝ) (harea : 0 < area)
    (hslope : slope ≠ 0) (hvalue : 0 < linearizer slope intercept displacement)
    (hlinear :
      1 / Real.sqrt
          (geometricCoupling area (displacement + intercept / slope) Real.pi) =
        linearizer slope intercept displacement) :
    area = effectiveArea slope Real.pi := by
  have hfactor : linearizer slope intercept displacement =
      slope * (displacement + intercept / slope) := by
    dsimp [linearizer]
    rw [mul_add, mul_div_cancel₀ intercept hslope]
  have hr : displacement + intercept / slope ≠ 0 := by
    intro hz
    have hzero : linearizer slope intercept displacement = 0 := by
      rw [hfactor, hz, mul_zero]
    exact (ne_of_gt hvalue) hzero
  have he : 0 < geometricCoupling area (displacement + intercept / slope) Real.pi := by
    dsimp [geometricCoupling]
    positivity
  have hinverse :=
    (inverse_sqrt_eq_iff_inverse_square _ _ he hvalue).mp hlinear
  have hgeometry := Response.affine_transfer_conversion intercept slope displacement hslope
  have htransfer :
      geometricCoupling area (displacement + intercept / slope) Real.pi / 1 =
        Response.transfer (1 / slope ^ 2) (displacement + intercept / slope) := by
    calc
      _ = 1 / (linearizer slope intercept displacement) ^ 2 := by
        simpa only [div_one] using hinverse
      _ = 1 / (intercept + slope * displacement) ^ 2 := by
        rw [linearizer, add_comm]
      _ = _ := hgeometry.symm
  have hresult := receiving_area_of_normalized_transfer area 1 (1 / slope ^ 2)
    (displacement + intercept / slope) (by norm_num) hr htransfer
  rw [hresult]
  dsimp [effectiveArea]
  ring

/-- A normalized affine transfer determines the receiving area only after an
absolute reference efficiency is supplied: `Sigma = 4*pi*epsilonRef/beta^2`. -/
theorem receiving_area_of_normalized_affine_transfer
    (area referenceEfficiency alpha beta displacement : ℝ)
    (href : referenceEfficiency ≠ 0) (hbeta : beta ≠ 0)
    (hr : displacement + alpha / beta ≠ 0)
    (htransfer :
      geometricCoupling area (displacement + alpha / beta) Real.pi / referenceEfficiency =
        1 / (alpha + beta * displacement) ^ 2) :
    area = referenceEfficiency * effectiveArea beta Real.pi := by
  have hgeometry := Response.affine_transfer_conversion alpha beta displacement hbeta
  have hnormalized :
      geometricCoupling area (displacement + alpha / beta) Real.pi / referenceEfficiency =
        Response.transfer (1 / beta ^ 2) (displacement + alpha / beta) :=
    htransfer.trans hgeometry.symm
  have hresult := receiving_area_of_normalized_transfer area referenceEfficiency
    (1 / beta ^ 2) (displacement + alpha / beta) href hr hnormalized
  rw [hresult]
  dsimp [effectiveArea]
  ring

/-- For a count-rate linearizer, the emitted photon rate `activity*emission`
remains in the denominator. The result is the existing `photopeakArea` owner:
`4*pi / (activity*emission*slope^2)`. -/
theorem receiving_area_of_count_rate_linearizer
    (area activity emission slope distance : ℝ)
    (harea : 0 < area) (hactivity : 0 < activity) (hemission : 0 < emission)
    (hslope : 0 < slope) (hr : 0 < distance)
    (hlinear :
      1 / Real.sqrt
          ((activity * emission) * geometricCoupling area distance Real.pi) =
        slope * distance) :
    area = photopeakArea 1 activity emission slope := by
  have hrate : (activity * emission) * geometricCoupling area distance Real.pi =
      geometricCoupling ((activity * emission) * area) distance Real.pi := by
    dsimp [geometricCoupling]
    ring
  rw [hrate] at hlinear
  have hfit :
      1 / Real.sqrt
          (geometricCoupling ((activity * emission) * area)
            (distance + 0 / slope) Real.pi) = linearizer slope 0 distance := by
    simpa only [zero_div, add_zero, linearizer] using hlinear
  have hresult := receiving_area_of_affine_efficiency_linearizer
    ((activity * emission) * area) slope 0 distance
    (mul_pos (mul_pos hactivity hemission) harea) (ne_of_gt hslope)
    (by simpa only [linearizer, add_zero] using mul_pos hslope hr) hfit
  have hscaled := congrArg (fun z : ℝ => z / (activity * emission)) hresult
  rw [mul_div_cancel_left₀ area (mul_ne_zero (ne_of_gt hactivity) (ne_of_gt hemission))]
    at hscaled
  calc
    area = effectiveArea slope Real.pi / (activity * emission) := hscaled
    _ = photopeakArea 1 activity emission slope := by
      dsimp [effectiveArea, photopeakArea]
      ring

/-- The receiving area fixes the conversion of signed quadratic curvature to
the signed fitted-baseline transfer area, retaining the absolute reference scale.
For a general nonunit `a`, this is not the physical-baseline net-transfer area. -/
theorem inferred_loss_area_from_receiving_area
    (geometryArea a b referenceEfficiency area : ℝ)
    (href : referenceEfficiency ≠ 0)
    (harea : area = 4 * Real.pi * referenceEfficiency * geometryArea) :
    Response.inferredCrossSection geometryArea a b =
      -(b / a) * area / referenceEfficiency := by
  apply (eq_div_iff href).mpr
  rw [harea]
  dsimp [Response.inferredCrossSection]
  ring

/-- With `u = 1/(4*pi*rho^2)`, the receiving area supplies the first-order
coefficient and its product with the signed loss area supplies the second:
`Sigma*u - Sigma*sigma*u^2 = epsilon*(1 - sigma*u)`. This remains a signed
algebraic model; it does not assert that every net deficit is pure summing-out. -/
theorem two_area_efficiency_factorization (receivingArea lossArea distance : ℝ) :
    singlesResponse receivingArea (receivingArea * lossArea)
        (geometricCoupling 1 distance Real.pi)
        ((geometricCoupling 1 distance Real.pi) ^ 2) =
      geometricCoupling receivingArea distance Real.pi *
        (1 - geometricCoupling lossArea distance Real.pi) := by
  dsimp [singlesResponse, geometricCoupling]
  ring

end InfoGeometry.Probability.DetectorCrossSectionDuality.ReceivingArea
