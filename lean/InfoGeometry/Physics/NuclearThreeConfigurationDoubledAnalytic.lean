/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction

/-!
# Real analyticity and bounds for the actual doubled complementary resolvent

The energy-dependent operator is the native `doubledResolvent` used by the
Krein Feshbach reduction. Its scalar formula gives genuine real analyticity
away from the complementary pole and a uniform bound on the established
midpoint window. The operator norm is the carrier's auxiliary norm; no
positivity of the signed Krein pairing is inferred.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfigurationDoubledAnalytic

open InfoGeometry.Krein
open NuclearThreeConfiguration NuclearDoubledConfiguration
open NuclearThreeConfigurationResolvent NuclearThreeConfigurationKreinReduction

/-- The actual doubled inverse is a scalar multiple of the paired complement. -/
theorem doubledResolvent_eq_scalar (c E : ℝ) :
    doubledResolvent c E = (E - c)⁻¹ • pairedLift complement := by
  change pairedLift ((E - c)⁻¹ • complement) = _
  exact pairedLift_smul (E - c)⁻¹ complement

/-- Phase-axis compatibility is a separate exact operator identity. -/
theorem doubledResolvent_comp_clockAxis (c E : ℝ) :
    (doubledResolvent c E).comp (clockAxis (E := ConfigurationSpace)) =
      (clockAxis (E := ConfigurationSpace)).comp (doubledResolvent c E) :=
  pairedLift_comp_clockAxis (resolvent c E)

/-- Real analyticity on the actual bounded doubled-operator algebra. -/
theorem analyticOnNhd_doubledResolvent (c : ℝ) :
    AnalyticOnNhd ℝ (doubledResolvent c) {E : ℝ | E ≠ c} := by
  have hsub : AnalyticOnNhd ℝ (fun E : ℝ => E - c) {E : ℝ | E ≠ c} :=
    analyticOnNhd_id.sub analyticOnNhd_const
  have hinv : AnalyticOnNhd ℝ (fun E : ℝ => (E - c)⁻¹) {E : ℝ | E ≠ c} :=
    hsub.inv (fun E hE => sub_ne_zero.mpr hE)
  have hfun : doubledResolvent c =
      (fun E : ℝ => (E - c)⁻¹ • pairedLift complement) := by
    funext E
    exact doubledResolvent_eq_scalar c E
  rw [hfun]
  exact hinv.smul (analyticOnNhd_const : AnalyticOnNhd ℝ
    (fun _ : ℝ => pairedLift complement) {E : ℝ | E ≠ c})

theorem analyticOnNhd_doubledResolvent_validityWindow (a c : ℝ) (hac : a < c) :
    AnalyticOnNhd ℝ (doubledResolvent c) (validityWindow a c) :=
  (analyticOnNhd_doubledResolvent c).mono
    (fun E hE => energy_ne_eliminated a c E hac hE)

/-- Exact norm identity retaining the actual paired complementary projection. -/
theorem norm_doubledResolvent (c E : ℝ) :
    ‖doubledResolvent c E‖ = |E - c|⁻¹ * ‖pairedLift complement‖ := by
  rw [doubledResolvent_eq_scalar, norm_smul, norm_inv, Real.norm_eq_abs]

theorem norm_doubledResolvent_le (c E δ : ℝ) (hδ : 0 < δ) (hgap : δ ≤ |E - c|) :
    ‖doubledResolvent c E‖ ≤ δ⁻¹ * ‖pairedLift complement‖ := by
  rw [norm_doubledResolvent]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg (pairedLift complement))
  simpa only [one_div] using one_div_le_one_div_of_le hδ hgap

/-- Uniform control on the same real energy window as the exact inverse. -/
theorem norm_doubledResolvent_le_on_validityWindow (a c E : ℝ) (hac : a < c)
    (hE : E ∈ validityWindow a c) :
    ‖doubledResolvent c E‖ ≤ ((c - a) / 2)⁻¹ * ‖pairedLift complement‖ := by
  apply norm_doubledResolvent_le c E ((c - a) / 2)
  · linarith
  · have hEc : E - c < 0 := sub_neg.mpr (energy_lt_eliminated a c E hac hE)
    rw [abs_of_neg hEc]
    change E < (a + c) / 2 at hE
    linarith

end InfoGeometry.Physics.NuclearThreeConfigurationDoubledAnalytic
