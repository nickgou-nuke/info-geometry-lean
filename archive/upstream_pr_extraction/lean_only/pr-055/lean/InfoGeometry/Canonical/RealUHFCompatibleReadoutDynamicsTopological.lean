import InfoGeometry.Canonical.RealUHFCompatibleReadoutScalarDynamicsBridge

/-!
# Topological scalar dynamics on compatible readout families

The scalar stage flow induces a continuous action on the induced topology of
compatible readout families.  The action is still formulated at the finite
stage/readout level; no completed UHF or KMS structure is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopological

open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit

theorem continuous_scalarDilation_pullback :
    Continuous
      (fun p : ℝ × CompatibleContinuousReadoutFamily =>
        pullback scalarDilationStageFlow p.1 p.2) := by
  apply continuous_induced_rng.mpr
  let f : ℝ × CompatibleContinuousReadoutFamily → ReadoutFamily :=
    fun p => fun n => (Real.exp p.1) • p.2.1 n
  have hf : Continuous f := by
    apply continuous_pi
    intro n
    exact (Real.continuous_exp.comp continuous_fst).smul
      ((continuous_apply n).comp
        (continuous_subtype_val.comp continuous_snd))
  convert hf using 1
  funext p
  funext n
  ext X
  simp [f, pullback, scalarDilationStageFlow]

theorem scalarDilation_pullback_zero_action
    (ρ : CompatibleContinuousReadoutFamily) :
    pullback scalarDilationStageFlow 0 ρ = ρ := by
  exact pullback_zero scalarDilationStageFlow ρ

theorem scalarDilation_pullback_add_action
    (s t : ℝ) (ρ : CompatibleContinuousReadoutFamily) :
    pullback scalarDilationStageFlow (s + t) ρ =
      pullback scalarDilationStageFlow t
        (pullback scalarDilationStageFlow s ρ) := by
  exact pullback_add scalarDilationStageFlow s t ρ

end InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopological

end
