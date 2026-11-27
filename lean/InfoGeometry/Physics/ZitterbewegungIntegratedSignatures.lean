/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.ZitterbewegungMassEmergenceBridge

/-!
# Exact kinematic and coefficient checks for Dirac Zitterbewegung signatures

The standard rest-frame positive/negative energy gap gives angular frequency
`2 m c^2 / ℏ`; its period is therefore `2π / ω`. This file proves the exact
period and cycle-count identities from the existing gap owner.

It also audits two heuristic identifications in the motivating prose. With
radius `a = ℏ/(2mc)`, an isotropic second-order Taylor average contributes
`a^2/6` times the Laplacian, which is one third of the usual Darwin coefficient
`ℏ^2/(8m^2c^2)`. Thus that radius and that averaging ansatz do not reproduce
the Darwin coefficient without an additional factor in the variance.

Finally, the displayed angular law `1 + A cos(2φ)` is even in `φ`; by itself it
cannot distinguish the two orientations. No claim about a measurable
Zitterbewegung signal or its causal relation to a nuclear polarization
measurement is formalized here.
-/

namespace InfoGeometry.Physics.ZitterbewegungSignatures

open InfoGeometry.Canonical.ZitterbewegungMassEmergence

noncomputable section

/-- The period associated with the rest-frame Dirac gap frequency. -/
def comptonZitterPeriod (m c hbar : ℝ) : ℝ :=
  2 * Real.pi / comptonFrequency m c hbar

/-- For positive mass, light speed, and Planck constant, the gap frequency
period simplifies to `π ℏ / (m c²)`. -/
theorem comptonZitterPeriod_eq (m c hbar : ℝ)
    (hm : 0 < m) (hc : 0 < c) (hhbar : 0 < hbar) :
    comptonZitterPeriod m c hbar = Real.pi * hbar / (m * c ^ 2) := by
  rw [comptonZitterPeriod, comptonFrequency_eq]
  have hmc : m * c ^ 2 ≠ 0 := mul_ne_zero hm.ne' (pow_ne_zero 2 hc.ne')
  field_simp
  <;> ring

/-- Number of angular cycles accumulated during a duration. -/
def zitterCyclesDuring (duration m c hbar : ℝ) : ℝ :=
  duration / comptonZitterPeriod m c hbar

/-- Cycle count is duration times angular frequency divided by `2π`. -/
theorem zitterCyclesDuring_eq (duration m c hbar : ℝ)
    (hfreq : comptonFrequency m c hbar ≠ 0) :
    zitterCyclesDuring duration m c hbar =
      duration * comptonFrequency m c hbar / (2 * Real.pi) := by
  rw [zitterCyclesDuring, comptonZitterPeriod]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp [hfreq, hpi]
  <;> ring

/-- The radius scale quoted in the prompt, `ℏ/(2mc)`. -/
def diracZitterRadius (m c hbar : ℝ) : ℝ :=
  hbar / (2 * m * c)

/-- Foldy–Wouthuysen Darwin coefficient multiplying the Laplacian of the
potential-energy function. -/
def darwinLaplacianCoefficient (m c hbar : ℝ) : ℝ :=
  hbar ^ 2 / (8 * m ^ 2 * c ^ 2)

/-- Coefficient produced by the isotropic second-order Taylor average at the
quoted radius: `<δr²>/6` with `<δr²> = a²`. -/
def isotropicZitterTaylorCoefficient (m c hbar : ℝ) : ℝ :=
  diracZitterRadius m c hbar ^ 2 / 6

/-- With `a = ℏ/(2mc)`, the Taylor-average coefficient is exactly one third
of the Foldy–Wouthuysen Darwin coefficient. This records the factor mismatch
in the heuristic as stated. -/
theorem isotropicZitterTaylorCoefficient_eq_third_darwin
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    isotropicZitterTaylorCoefficient m c hbar =
      darwinLaplacianCoefficient m c hbar / 3 := by
  unfold isotropicZitterTaylorCoefficient diracZitterRadius darwinLaplacianCoefficient
  field_simp [hm, hc]
  <;> ring

/-- Equivalently, matching the Darwin coefficient in a `variance/6` Taylor
term requires variance `3 a²`, rather than `a²`. -/
theorem variance_required_for_darwin_eq_three_radius_sq
    (m c hbar : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) :
    6 * darwinLaplacianCoefficient m c hbar =
      3 * diracZitterRadius m c hbar ^ 2 := by
  unfold darwinLaplacianCoefficient diracZitterRadius
  field_simp [hm, hc]
  <;> ring

/-- The simplest linear-polarization modulation used in the prompt. -/
def linearPolarizationModulation (amplitude angle : ℝ) : ℝ :=
  1 + amplitude * Real.cos (2 * angle)

/-- The `cos(2φ)` modulation is invariant under reversal of the angle, so it
does not by itself distinguish handedness. -/
theorem linearPolarizationModulation_even (amplitude angle : ℝ) :
    linearPolarizationModulation amplitude (-angle) =
      linearPolarizationModulation amplitude angle := by
  unfold linearPolarizationModulation
  rw [show 2 * -angle = -(2 * angle) by ring, Real.cos_neg]

end

end InfoGeometry.Physics.ZitterbewegungSignatures

namespace InfoGeometry.Physics.ZitterbewegungSignatures.DecimalAudit

/-- Exact rational encoding of the displayed `6.4 × 10⁻²² s` period. -/
def shortPeriodClaim : ℚ := 64 / 10 ^ 23

/-- Exact rational encoding of the other displayed period `4.05 × 10⁻²¹ s`. -/
def gapPeriodClaim : ℚ := 405 / 10 ^ 23

/-- Exact rational encoding of the central `3.63 × 10⁻¹² s` lifetime. -/
def sodiumLevelLifetime : ℚ := 363 / 10 ^ 14

/-- The two period figures in the prompt are unequal as exact encodings of
their displayed decimal values. -/
theorem displayed_period_claims_conflict : shortPeriodClaim ≠ gapPeriodClaim := by
  norm_num [shortPeriodClaim, gapPeriodClaim]

/-- The lifetime divided by `6.4 × 10⁻²² s` is 5,671,875,000 cycles. -/
theorem cycle_count_using_short_period_claim :
    sodiumLevelLifetime / shortPeriodClaim = 5671875000 := by
  norm_num [sodiumLevelLifetime, shortPeriodClaim]

/-- Using the `4.05 × 10⁻²¹ s` period instead gives a central estimate between
896,296,296 and 896,296,297 cycles (before accounting for measurement error). -/
theorem cycle_count_using_gap_period_claim_bounds :
    (896296296 : ℚ) ≤ sodiumLevelLifetime / gapPeriodClaim ∧
      sodiumLevelLifetime / gapPeriodClaim < 896296297 := by
  norm_num [sodiumLevelLifetime, gapPeriodClaim]

end InfoGeometry.Physics.ZitterbewegungSignatures.DecimalAudit
