import InfoGeometry.Canonical.RealUHFCompatibleReadoutActionColimitBridge

/-!
# Continuous scalar action on the normalized-trace colimit readout

This owner exposes the time-dependent colimit readout as an actual `TopCat`
morphism.  It is a map into the scalar readout space, not an endomorphism of the
colimit carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutContinuousColimitAction

open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.RealUHFCompatibleReadoutColimitDynamicsBridge
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Clifford.Cl11TensorTower

def normalizedTraceReadoutAction
    (p : ℝ × topologicalColimit) : ℝ :=
  (Real.exp p.1) *
    normalizedTraceTopologicalColimitMap p.2

def finiteStageNormalizedTraceAction
    (n : ℕ) (p : ℝ × MatStage n) : ℝ :=
  (Real.exp p.1) * normalizedTrace n p.2

theorem continuous_normalizedTraceReadoutAction :
    Continuous normalizedTraceReadoutAction := by
  exact (Real.continuous_exp.comp continuous_fst).mul
    (normalizedTraceTopologicalColimitMap.hom.continuous.comp continuous_snd)

theorem continuous_finiteStageNormalizedTraceAction (n : ℕ) :
    Continuous (finiteStageNormalizedTraceAction n) := by
  exact (Real.continuous_exp.comp continuous_fst).mul
    ((normalizedTraceLinear n).continuous_of_finiteDimensional.comp
      continuous_snd)

noncomputable def normalizedTraceReadoutActionTopCat :
    TopCat.of (ℝ × topologicalColimit) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := normalizedTraceReadoutAction
      continuous_toFun := continuous_normalizedTraceReadoutAction }

@[simp] theorem normalizedTraceReadoutActionTopCat_apply
    (t : ℝ) (z : topologicalColimit) :
    normalizedTraceReadoutActionTopCat (t, z) =
      normalizedTraceReadoutAction (t, z) := by
  rfl

theorem normalizedTraceReadoutAction_zero
    (z : topologicalColimit) :
    normalizedTraceReadoutAction (0, z) =
      normalizedTraceTopologicalColimitMap z := by
  simp [normalizedTraceReadoutAction]

theorem normalizedTraceReadoutAction_add
    (s t : ℝ) (z : topologicalColimit) :
    normalizedTraceReadoutAction (s + t, z) =
      scalarValueMap t (normalizedTraceReadoutAction (s, z)) := by
  change (Real.exp (s + t)) *
      normalizedTraceTopologicalColimitMap z =
    (Real.exp t) *
      ((Real.exp s) * normalizedTraceTopologicalColimitMap z)
  rw [Real.exp_add]
  ring

theorem normalizedTraceReadoutAction_stage
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    normalizedTraceReadoutAction
        (t, topologicalInjection n X) =
      normalizedTraceTopologicalColimitMap
        (topologicalInjection n
          (scalarDilationStageFlow.flow n t X)) := by
  simpa [normalizedTraceReadoutAction, scalarValueMap] using
    (normalizedTrace_scalarValueMap_matches_stageFlow t n X)

theorem finiteStageNormalizedTraceAction_matches_global
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    finiteStageNormalizedTraceAction n (t, X) =
      normalizedTraceReadoutAction
        (t, topologicalInjection n X) := by
  change (Real.exp t) * normalizedTrace n X =
    (Real.exp t) *
      normalizedTraceTopologicalColimitMap
        (topologicalInjection n X)
  rw [normalizedTraceTopologicalColimitMap_inclusion]

theorem finiteStageNormalizedTraceAction_matches_stageFlow
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    finiteStageNormalizedTraceAction n (t, X) =
      normalizedTraceTopologicalColimitMap
        (topologicalInjection n
          (scalarDilationStageFlow.flow n t X)) := by
  calc
    finiteStageNormalizedTraceAction n (t, X) =
        normalizedTraceReadoutAction
          (t, topologicalInjection n X) :=
      finiteStageNormalizedTraceAction_matches_global t n X
    _ = normalizedTraceTopologicalColimitMap
          (topologicalInjection n
            (scalarDilationStageFlow.flow n t X)) :=
      normalizedTraceReadoutAction_stage t n X

theorem finiteStageNormalizedTraceAction_transition
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    finiteStageNormalizedTraceAction (n + 1)
        (t, stageEmbed n X) =
      finiteStageNormalizedTraceAction n (t, X) := by
  change (Real.exp t) * normalizedTrace (n + 1) (stageEmbed n X) =
    (Real.exp t) * normalizedTrace n X
  rw [stageEmbed_apply, normalizedTrace_matStageEmbed]

theorem normalizedTraceReadoutAction_injection_transition
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    normalizedTraceReadoutAction
        (t, topologicalInjection (n + 1) (stageEmbed n X)) =
      normalizedTraceReadoutAction
        (t, topologicalInjection n X) := by
  have h := topologicalInjection_transition (m := n) (n := n + 1)
    (Nat.le_succ n) X
  simpa [bondAlgHom_succ, stageEmbed_apply] using
    congrArg (fun z : topologicalColimit =>
      normalizedTraceReadoutAction (t, z)) h

end InfoGeometry.Canonical.RealUHFCompatibleReadoutContinuousColimitAction

end
