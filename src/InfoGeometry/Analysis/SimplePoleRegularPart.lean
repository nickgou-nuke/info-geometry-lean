/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.TwoSheetPoleCancellation
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Constructing the regular part at a simple pole

Contract: for an analytic complex numerator `n` at `a`, the native divided
difference `dslope n a` is the analytic remainder of `n(z)/(z-a)` after
subtracting `n(a)/(z-a)`. This supplies the remainder data used by the existing
two-sheet cancellation theorem. Extension is equivalent to `n(a)=0`, and
opposite values of two analytic numerators give an analytic sum at the same
point. Residue balance at different points does not meet this local contract.
-/

noncomputable section

namespace InfoGeometry.Analysis.SimplePoleRegularPart

open Filter Set BipolarSimplePoleResidues
open scoped Topology

/-- The native divided difference supplies an analytic regular part. -/
theorem analytic_regularPart {n : ℂ → ℂ} {a : ℂ} (hn : AnalyticAt ℂ n a) :
    AnalyticAt ℂ (dslope n a) a := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [hn.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (self_mem_nhdsWithin : ∀ᶠ z in 𝓝[≠] a, z ∈ ({a} : Set ℂ)ᶜ)] with z hz hza
    exact (differentiableAt_dslope_of_ne (by simpa using hza)).mpr hz.differentiableAt
  · exact continuousAt_dslope_same.mpr hn.differentiableAt

/-- Exact principal-part decomposition, away from the puncture. -/
theorem quotient_eq_principal_add_regular (n : ℂ → ℂ) (a z : ℂ) (hz : z ≠ a) :
    n z / (z - a) = n a / (z - a) + dslope n a z := by
  rw [dslope_of_ne n hz, slope_def_field]
  ring

/-- The coefficient is computed from the analytic numerator, not assigned. -/
theorem quotient_coefficient {n : ℂ → ℂ} {a : ℂ} (hn : ContinuousAt n a) :
    HasSimplePoleCoefficientAt (fun z => n z / (z - a)) a (n a) := by
  apply (hn.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hza : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
  field_simp

/-- A local analytic extension exists exactly when the principal coefficient
vanishes. The forward implication also rules out merely continuous extensions. -/
theorem analytic_extension_iff {n : ℂ → ℂ} {a : ℂ} (hn : AnalyticAt ℂ n a) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      g =ᶠ[𝓝[≠] a] (fun z => n z / (z - a))) ↔ n a = 0 := by
  constructor
  · rintro ⟨g, hg, he⟩
    by_contra hne
    exact (quotient_coefficient hn.continuousAt).no_continuous_extension hne
      ⟨g, hg.continuousAt, he⟩
  · intro hzero
    refine ⟨dslope n a, analytic_regularPart hn, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    have h := quotient_eq_principal_add_regular n a z (by simpa using hz)
    simpa only [hzero, zero_div, zero_add] using h.symm

/-- The extension's value at the puncture is the derivative of the numerator. -/
theorem regularPart_value {n : ℂ → ℂ} {a c : ℂ} (hn : HasDerivAt n c a) :
    dslope n a a = c := by
  rw [dslope_same, hn.deriv]

/-- Opposite analytic numerator values at a common point construct a regular
sum without assuming the remainder functions in advance. -/
theorem analytic_extension_of_balanced_numerators {n m : ℂ → ℂ} {a : ℂ}
    (hn : AnalyticAt ℂ n a) (hm : AnalyticAt ℂ m a) (hbalance : n a + m a = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      g =ᶠ[𝓝[≠] a] (fun z => n z / (z - a) + m z / (z - a)) := by
  obtain ⟨g, hg, he⟩ := (analytic_extension_iff (hn.add hm)).mpr hbalance
  exact ⟨g, hg, by simpa only [Pi.add_apply, add_div] using he⟩

/-- The existing bipolar counterexample becomes analytic at each pole after
subtracting that pole's own principal part. The other pole remains separate. -/
theorem bipolar_analytic_regular_parts :
    AnalyticAt ℂ (fun z => BipolarLogDifferential.dlog01 z - 1 / z) 0 ∧
    AnalyticAt ℂ (fun z => BipolarLogDifferential.dlog01 z + 1 / (z - 1)) 1 := by
  have h0 : AnalyticAt ℂ (fun z : ℂ => 1 / (1 - z)) 0 :=
    analyticAt_const.div (analyticAt_const.sub analyticAt_id) (by norm_num)
  have h1 : AnalyticAt ℂ (fun z : ℂ => 1 / z) 1 :=
    analyticAt_const.div analyticAt_id (by norm_num)
  constructor
  · convert h0 using 1
    funext z
    simp [BipolarLogDifferential.dlog01]
  · convert h1 using 1
    funext z
    have hneg : (1 : ℂ) - z = -(z - 1) := by ring
    unfold BipolarLogDifferential.dlog01
    rw [hneg, div_neg]
    ring

end InfoGeometry.Analysis.SimplePoleRegularPart
