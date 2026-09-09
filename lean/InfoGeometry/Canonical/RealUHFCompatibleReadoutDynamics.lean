import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge

/-!
# Dynamics on compatible real UHF readout families

This owner treats a stagewise continuous-linear evolution as a natural
transformation of the finite restriction system.  Its action on readouts is
the contravariant pullback.  No completion, KMS condition, or C*-automorphism
claim is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNet
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNetTopological
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitBridge
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Clifford.Cl11TensorTowerLimit

structure CompatibleStageFlow where
  flow : ∀ n : ℕ, ℝ → MatStage n →L[ℝ] MatStage n
  restrict_naturality : ∀ (n : ℕ) (t : ℝ),
    (stageRestrictCLM n).comp (flow (n + 1) t) =
      (flow n t).comp (stageRestrictCLM n)
  flow_zero : ∀ n : ℕ,
    flow n 0 = ContinuousLinearMap.id ℝ (MatStage n)
  flow_add : ∀ (n : ℕ) (s t : ℝ),
    flow n (s + t) = (flow n s).comp (flow n t)

private theorem flow_restrict_apply
    (D : CompatibleStageFlow) (n : ℕ) (t : ℝ)
    (X : MatStage (n + 1)) :
    D.flow n t (stageRestrict n X) =
      stageRestrict n (D.flow (n + 1) t X) := by
  have h := congrArg
    (fun f : MatStage (n + 1) →L[ℝ] MatStage n => f X)
    (D.restrict_naturality n t)
  simpa [stageRestrictCLM_apply] using h.symm

noncomputable def pullback
    (D : CompatibleStageFlow) (t : ℝ)
    (ρ : CompatibleContinuousReadoutFamily) :
    CompatibleContinuousReadoutFamily :=
  ⟨fun n => (ρ.1 n).comp (D.flow n t), by
    intro n
    ext X
    change ρ.1 n (D.flow n t (stageRestrict n X)) =
      ρ.1 (n + 1) (D.flow (n + 1) t X)
    rw [flow_restrict_apply D n t X]
    exact compatible_apply ρ n (D.flow (n + 1) t X)⟩

@[simp] theorem pullback_apply
    (D : CompatibleStageFlow) (t : ℝ)
    (ρ : CompatibleContinuousReadoutFamily) (n : ℕ) (X : MatStage n) :
    (pullback D t ρ).1 n X = ρ.1 n (D.flow n t X) := rfl

theorem pullback_preserves_compatibility
    (D : CompatibleStageFlow) (t : ℝ)
    (ρ : CompatibleContinuousReadoutFamily) (n : ℕ)
    (X : MatStage (n + 1)) :
    (pullback D t ρ).1 n (stageRestrict n X) =
      (pullback D t ρ).1 (n + 1) X := by
  exact compatible_apply (pullback D t ρ) n X

theorem pullback_zero
    (D : CompatibleStageFlow)
    (ρ : CompatibleContinuousReadoutFamily) :
    pullback D 0 ρ = ρ := by
  apply Subtype.ext
  funext n
  ext X
  change ρ.1 n (D.flow n 0 X) = ρ.1 n X
  rw [D.flow_zero n]
  rfl

theorem pullback_add
    (D : CompatibleStageFlow) (s t : ℝ)
    (ρ : CompatibleContinuousReadoutFamily) :
    pullback D (s + t) ρ = pullback D t (pullback D s ρ) := by
  apply Subtype.ext
  funext n
  ext X
  change ρ.1 n (D.flow n (s + t) X) =
    ρ.1 n (D.flow n s (D.flow n t X))
  rw [D.flow_add n s t]
  rfl

noncomputable def identityStageFlow : CompatibleStageFlow where
  flow := fun n _ => ContinuousLinearMap.id ℝ (MatStage n)
  restrict_naturality := by
    intro n t
    ext X
    rfl
  flow_zero := by
    intro n
    rfl
  flow_add := by
    intro n s t
    ext X
    rfl

noncomputable def scalarDilationStageFlow : CompatibleStageFlow where
  flow := fun n t => (Real.exp t) • ContinuousLinearMap.id ℝ (MatStage n)
  restrict_naturality := by
    intro n t
    ext X
    simp
  flow_zero := by
    intro n
    simp
  flow_add := by
    intro n s t
    ext X
    simp [Real.exp_add, smul_smul, mul_comm]

@[simp] theorem scalarDilationStageFlow_apply
    (n : ℕ) (t : ℝ) (X : MatStage n) :
    scalarDilationStageFlow.flow n t X = (Real.exp t) • X := by
  simp [scalarDilationStageFlow]

@[simp] theorem scalarDilation_pullback_apply
    (t : ℝ) (ρ : CompatibleContinuousReadoutFamily)
    (n : ℕ) (X : MatStage n) :
    (pullback scalarDilationStageFlow t ρ).1 n X =
      (Real.exp t) • ρ.1 n X := by
  simp [pullback, scalarDilationStageFlow]

theorem normalizedTraceReadout_scalarDilation
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    normalizedTraceReadoutFamily.1 n
        (scalarDilationStageFlow.flow n t X) =
      (Real.exp t) • normalizedTraceReadoutFamily.1 n X := by
  change normalizedTraceLinear n (Real.exp t • X) =
    (Real.exp t) • normalizedTraceLinear n X
  exact (normalizedTraceLinear n).map_smul _ _

theorem normalizedTraceColimitMap_scalarDilation_stage
    (t : ℝ) (n : ℕ) (X : MatStage n) :
    normalizedTraceTopologicalColimitMap
        (topologicalInjection n (scalarDilationStageFlow.flow n t X)) =
      (Real.exp t) •
        normalizedTraceTopologicalColimitMap (topologicalInjection n X) := by
  rw [normalizedTraceColimitMap_matches_inverse_family,
    normalizedTraceColimitMap_matches_inverse_family]
  exact normalizedTraceReadout_scalarDilation t n X

theorem continuous_scalarDilation_time_coordinate
    (ρ : CompatibleContinuousReadoutFamily)
    (n : ℕ) (X : MatStage n) :
    Continuous (fun t : ℝ => (pullback scalarDilationStageFlow t ρ).1 n X) := by
  simpa only [scalarDilation_pullback_apply] using
    (Real.continuous_exp.smul
      (continuous_const : Continuous (fun _ : ℝ => ρ.1 n X)))

theorem identityStageFlow_pullback
    (t : ℝ) (ρ : CompatibleContinuousReadoutFamily) :
    pullback identityStageFlow t ρ = ρ := by
  apply Subtype.ext
  funext n
  ext X
  rfl

theorem continuous_identityStageFlow_pullback :
    Continuous
      (fun p : ℝ × CompatibleContinuousReadoutFamily =>
        pullback identityStageFlow p.1 p.2) := by
  simpa [identityStageFlow_pullback] using
    (continuous_snd :
      Continuous (fun p : ℝ × CompatibleContinuousReadoutFamily => p.2))

end InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
