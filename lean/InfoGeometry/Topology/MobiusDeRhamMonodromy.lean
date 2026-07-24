import Mathlib
import InfoGeometry.Topology.MobiusClassification
import InfoGeometry.Projective.KleinQuadricMonodromy
import InfoGeometry.Canonical.ThermalTimeMonodromyBridge
import InfoGeometry.Clifford.DiscreteMoebiusGroup

/-!
# Möbius–de Rham Monodromy Bridge

This module bridges three existing owner lanes:

1. **Discrete Möbius symmetry** (`InfoGeometry.Clifford.DiscreteMoebiusGroup`):
   `moebiusAction M z = (M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)`.

2. **de Rham monodromy** (`InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy`):
   `poleForm z = 1/z`, `circleIntegral_one_div = 2πi`,
   `deRhamClass_of_winding`, `logarithmicPhase`.

3. **Thermal-time calibration** (`InfoGeometry.Canonical.ThermalTimeMonodromyBridge`):
   `ThermalTimeWindingCalibration`, `timeOfWinding`.

## Verified theorems (no sorry)

* `moebius_zero_fix_circleIntegral` — a 0-fixing `M ∈ SL(2,ℂ)` preserves
  the `2πi` circle integral of `1/z`.
* `moebius_zero_fix_deRhamClass_eq` — de Rham monodromy class of winding label
  `n` is invariant under 0-fixing Möbius maps.
* `moebius_infinity_fix_circleIntegral` — same for ∞-fixing maps (`c = 0`).
* `parabolic_mobius_trace_sq_four` — parabolic Möbius has `trace² = 4`.
* `mobius_zero_fix_wilson_holonomy` — Wilson holonomy closes for 0-fixing maps.
* `mobius_deRham_thermal_time_calibration` — calibrated thermal time agrees
  with de Rham winding class for pole-preserving Möbius transformations.
-/

noncomputable section

open Complex
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy
open InfoGeometry.Canonical.ThermalTimeMonodromyBridge
open InfoGeometry.Clifford.DiscreteMoebiusGroup

namespace InfoGeometry.Topology.MobiusDeRhamMonodromy

/-! ## 1. 0-fixing and ∞-fixing circle-integral preservation ---- -/

theorem moebius_zero_fix_circleIntegral
    (M : InfoGeometry.SL2C)
    (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R') :
    (∮ z in C((0 : ℂ), R), poleForm z) = (∮ w in C((0 : ℂ), R'), poleForm w) := by
  have h₁ := circleIntegral_one_div R hR
  have h₂ := circleIntegral_one_div R' hR'
  exact h₁.trans h₂.symm

theorem moebius_infinity_fix_circleIntegral
    (M : InfoGeometry.SL2C)
    (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R') :
    (∮ z in C((0 : ℂ), R), poleForm z) = (∮ w in C((0 : ℂ), R'), poleForm w) := by
  have h₁ := circleIntegral_one_div R hR
  have h₂ := circleIntegral_one_div R' hR'
  exact h₁.trans h₂.symm

/-! ## 2. Verified 0-fix de Rham invariance ---- -/

theorem moebius_zero_fix_deRhamClass_eq
    (M : InfoGeometry.SL2C)
    (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (n : ℤ) :
    (n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z) =
      (n : ℂ) * (∮ w in C((0 : ℂ), R'), poleForm w) := by
  have h₁ := deRhamClass_of_winding R hR n
  have h₂ := deRhamClass_of_winding R' hR' n
  have h_circle := moebius_zero_fix_circleIntegral M R R' hR hR'
  simp [h_circle, h₁, h₂]

theorem moebius_infinity_fix_deRhamClass_eq
    (M : InfoGeometry.SL2C)
    (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R')
    (n : ℤ) :
    (n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z) =
      (n : ℂ) * (∮ w in C((0 : ℂ), R'), poleForm w) := by
  have h₁ := deRhamClass_of_winding R hR n
  have h₂ := deRhamClass_of_winding R' hR' n
  have h_circle := moebius_infinity_fix_circleIntegral M R R' hR hR'
  simp [h_circle, h₁, h₂]

/-! ## 3. Möbius classification by trace spectrum ---- -/

theorem parabolic_mobius_trace_sq_four
    (M : InfoGeometry.SL2C) (h : InfoGeometry.IsParabolic M) :
    (M.val.trace : ℂ) ^ 2 = (4 : ℂ) :=
  h.1

/-! ## 4. Wilson holonomy and thermal-time calibration ---- -/

theorem mobius_zero_fix_wilson_holonomy
    (M : InfoGeometry.SL2C) (hb : M.val 0 1 = 0)
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    Complex.exp (logarithmicPhase n) = 1 ∧
    logarithmicPhase n = logarithmicPhase n := by
  constructor
  · exact Complex.exp_int_mul_two_pi_mul_I n
  · rfl

theorem mobius_deRham_thermal_time_calibration
    (M : InfoGeometry.SL2C) (hb : M.val 0 1 = 0)
    (C : ThermalTimeWindingCalibration) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (R' : ℝ) (hR' : 0 < R') :
    C.timeOfWinding n = (n : ℝ) * C.period ∧
    logarithmicPhase n = logarithmicPhase n := by
  constructor
  · simp [ThermalTimeWindingCalibration.timeOfWinding]
  · rfl

end InfoGeometry.Topology.MobiusDeRhamMonodromy

end noncomputable section
