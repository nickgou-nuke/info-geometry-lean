import InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow
import InfoGeometry.Canonical.ApolloniusSurprisalCriticalLineBridge
import InfoGeometry.Krein.SplitBoost

/-!
# Apollonius critical layer and rapidity--angle flow

This owner records only the native invariant-layer statement.  It does not
identify the flow with a zeta-zero set, nor does it assert finite-time arrival
at the critical layer.
-/

namespace InfoGeometry.Canonical.ApolloniusRapidityFlowBridge

open InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow
open InfoGeometry.Canonical.ApolloniusSurprisalCriticalLineBridge
open InfoGeometry.Canonical.NegativeLogReadoutBridge

theorem flowMap_critical_rapidity_apollonius_zero (γ ω t θ : ℝ) :
    apolloniusRadialNegativeLog
        (flowMap γ ω t (0, θ)).1
        (flowMap γ ω t (0, θ)).2 = 0 := by
  rw [flowMap_critical_rapidity]
  exact apolloniusRadialNegativeLog_zero_scale _

theorem flowMap_critical_layer_apollonius_zero (γ ω t θ : ℝ) :
    flowMap γ ω t (0, θ) = (0, θ + ω * t) ∧
      apolloniusRadialNegativeLog
          (flowMap γ ω t (0, θ)).1
          (flowMap γ ω t (0, θ)).2 = 0 := by
  exact ⟨flowMap_critical_layer γ ω t θ,
    flowMap_critical_rapidity_apollonius_zero γ ω t θ⟩

theorem flowMap_rapidity_zero_iff (γ ω t u θ : ℝ) :
    (flowMap γ ω t (u, θ)).1 = 0 ↔ u = 0 := by
  exact InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow.flowMap_rapidity_zero_iff

theorem flowMap_apollonius_zero_iff (γ ω t u θ : ℝ) :
    apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2 = 0 ↔ u = 0 := by
  rw [apolloniusRadialNegativeLog_eq_zero_iff]
  exact flowMap_rapidity_zero_iff γ ω t u θ

theorem flowMap_apollonius_sign_preserved
    (γ ω t u θ : ℝ) :
    apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2 < 0 ↔ 0 < u := by
  rw [apolloniusRadialNegativeLog_neg_iff, flowMap_rapidity]
  have hexp : 0 < Real.exp (-γ * t) := Real.exp_pos _
  constructor
  · intro h
    have h' : Real.exp (-γ * t) * 0 < Real.exp (-γ * t) * u := by
      simpa using h
    exact lt_of_mul_lt_mul_left h' (le_of_lt hexp)
  · intro h
    exact mul_pos hexp h

theorem flowMap_apollonius_positive_sign_preserved
    (γ ω t u θ : ℝ) :
    0 < apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2 ↔ u < 0 := by
  rw [apolloniusRadialNegativeLog_pos_iff, flowMap_rapidity]
  have hexp : 0 < Real.exp (-γ * t) := Real.exp_pos _
  constructor
  · intro h
    have h' : Real.exp (-γ * t) * u < Real.exp (-γ * t) * 0 := by
      simpa using h
    exact lt_of_mul_lt_mul_left h' (le_of_lt hexp)
  · intro h
    simpa using (mul_lt_mul_of_pos_left h hexp)

theorem flowMap_apollonius_readout_scale
    (γ ω t u θ : ℝ) :
    apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2 =
      Real.exp (-γ * t) * apolloniusRadialNegativeLog u θ := by
  rw [apolloniusRadialNegativeLog_eq, apolloniusRadialNegativeLog_eq,
    flowMap_rapidity]
  ring_nf

theorem flowMap_apollonius_readout_ne_zero_iff
    (γ ω t u θ : ℝ) :
    apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2 ≠ 0 ↔
      apolloniusRadialNegativeLog u θ ≠ 0 := by
  rw [flowMap_apollonius_readout_scale, mul_ne_zero_iff]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨Real.exp_ne_zero _, h⟩

theorem flowMap_apollonius_readout_abs_scale
    (γ ω t u θ : ℝ) :
    |apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2| =
      Real.exp (-γ * t) *
        |apolloniusRadialNegativeLog u θ| := by
  rw [flowMap_apollonius_readout_scale, abs_mul]
  rw [abs_of_pos (Real.exp_pos _)]

theorem flowMap_apollonius_readout_abs_nonincreasing
    {γ ω t u θ : ℝ} (hγt : 0 ≤ γ * t) :
    |apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2| ≤
      |apolloniusRadialNegativeLog u θ| := by
  rw [flowMap_apollonius_readout_abs_scale]
  have hexp : Real.exp (-γ * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  simpa using
    (mul_le_mul_of_nonneg_right hexp
      (abs_nonneg (apolloniusRadialNegativeLog u θ)))

theorem flowMap_apollonius_readout_tendsto_zero
    {γ u θ : ℝ} (hγ : 0 < γ) :
    Filter.Tendsto
      (fun t : ℝ =>
        apolloniusRadialNegativeLog
          (flowMap γ 0 t (u, θ)).1
          (flowMap γ 0 t (u, θ)).2)
      Filter.atTop (nhds 0) := by
  rw [show (fun t : ℝ =>
      apolloniusRadialNegativeLog
        (flowMap γ 0 t (u, θ)).1
        (flowMap γ 0 t (u, θ)).2) =
      (fun t : ℝ => Real.exp (-γ * t) *
        apolloniusRadialNegativeLog u θ) by
        funext t
        exact flowMap_apollonius_readout_scale γ 0 t u θ]
  have hlinear : Filter.Tendsto (fun t : ℝ => γ * t)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hγ Filter.tendsto_id
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-γ * t))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
  simpa using hexp.mul_const (apolloniusRadialNegativeLog u θ)

theorem flowMap_apollonius_readout_semigroup
    (γ ω s t u θ : ℝ) :
    apolloniusRadialNegativeLog
        (flowMap γ ω (s + t) (u, θ)).1
        (flowMap γ ω (s + t) (u, θ)).2 =
      Real.exp (-γ * s) *
        apolloniusRadialNegativeLog
          (flowMap γ ω t (u, θ)).1
          (flowMap γ ω t (u, θ)).2 := by
  rw [flowMap_add, flowMap_apollonius_readout_scale]

theorem flowMap_apollonius_readout_abs_strictDecrease
    {γ ω t u θ : ℝ} (hγt : 0 < γ * t)
    (hreadout : apolloniusRadialNegativeLog u θ ≠ 0) :
    |apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2| <
      |apolloniusRadialNegativeLog u θ| := by
  rw [flowMap_apollonius_readout_abs_scale]
  have hexp : Real.exp (-γ * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have habs : 0 < |apolloniusRadialNegativeLog u θ| :=
    abs_pos.mpr hreadout
  simpa using (mul_lt_mul_of_pos_right hexp habs)

/- The dissipative rapidity readout is the right light-cone coordinate of the
   existing split boost.  This is the canonical Souriau/rapidity transport:
   no second boost carrier is introduced. -/
theorem flowMap_rapidity_eq_splitBoost_rightPart
    (γ t u : ℝ) :
    (flowMap γ 0 t (u, 0)).1 =
    InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.rightPart
        (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.mul
          (InfoGeometry.Krein.SplitBoost.boostElement (γ * t))
          (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.reconstruct 0 u)) := by
  rw [flowMap_rapidity]
  rw [InfoGeometry.Krein.SplitBoost.boost_rightPart_mul]
  rw [InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.rightPart_reconstruct]
  ring_nf

/- The Apollonius radial readout satisfies the same dissipative ODE as the
   rapidity coordinate. -/
theorem hasDerivAt_flowMap_apollonius_readout
    (γ ω t u θ : ℝ) :
    HasDerivAt
      (fun s => apolloniusRadialNegativeLog
        (flowMap γ ω s (u, θ)).1
        (flowMap γ ω s (u, θ)).2)
      (-γ * apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2) t := by
  have h := (hasDerivAt_flowMap γ ω t u θ).hasFDerivAt.fst.hasDerivAt
  simpa [apolloniusRadialNegativeLog_eq, flowMap, totalFlow,
    mul_assoc, mul_comm, mul_left_comm] using h.const_mul (-2)

end InfoGeometry.Canonical.ApolloniusRapidityFlowBridge
