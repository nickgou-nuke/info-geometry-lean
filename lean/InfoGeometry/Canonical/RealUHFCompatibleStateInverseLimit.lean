import InfoGeometry.Canonical.Cl11CompatibleLocalStateNetTopological
import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge

/-!
# Real compatible continuous readouts for the binary Clifford tower

This is the real projective-family carrier for the finite `Cl(1,1)` stages.
Its topology is the induced topology from the product of continuous linear
readout spaces.  The construction is deliberately only a compatible-family
carrier: it does not assert existence of a completed state, positivity, KMS
conditions, or a C*-algebraic inverse-limit theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNet
open InfoGeometry.Canonical.Cl11CompatibleLocalStateNetTopological

def stageRestrictCLM (n : ℕ) : MatStage (n + 1) →L[ℝ] MatStage n :=
  LinearMap.toContinuousLinearMap (stageRestrict n)

@[simp] theorem stageRestrictCLM_apply
    (n : ℕ) (X : MatStage (n + 1)) :
    stageRestrictCLM n X = stageRestrict n X := rfl

abbrev ReadoutFamily : Type _ :=
  ∀ n : ℕ, MatStage n →L[ℝ] ℝ

abbrev CompatibleContinuousReadoutFamily : Type _ :=
  {ρ : ReadoutFamily //
    ∀ n : ℕ,
      (ρ n).comp (stageRestrictCLM n) = ρ (n + 1)}

noncomputable instance : TopologicalSpace CompatibleContinuousReadoutFamily :=
  TopologicalSpace.induced
    (fun ρ : CompatibleContinuousReadoutFamily => ρ.1)
      (inferInstance : TopologicalSpace ReadoutFamily)

theorem compatible_apply
    (ρ : CompatibleContinuousReadoutFamily) (n : ℕ)
    (X : MatStage (n + 1)) :
    ρ.1 n (stageRestrict n X) = ρ.1 (n + 1) X := by
  have h := congrArg (fun f : MatStage (n + 1) →L[ℝ] ℝ => f X) (ρ.2 n)
  simpa [stageRestrictCLM_apply] using h

noncomputable def normalizedTraceReadoutFamily :
    CompatibleContinuousReadoutFamily :=
  ⟨fun n => LinearMap.toContinuousLinearMap (normalizedTraceLinear n), by
    intro n
    ext X
    change normalizedTrace n (stageRestrict n X) =
      normalizedTrace (n + 1) X
    exact normalizedTrace_stageRestrict n X⟩

@[simp] theorem normalizedTraceReadoutFamily_apply
    (n : ℕ) (X : MatStage n) :
    normalizedTraceReadoutFamily.1 n X = normalizedTrace n X := rfl

theorem normalizedTraceReadoutFamily_compatible
    (n : ℕ) (X : MatStage (n + 1)) :
    normalizedTraceReadoutFamily.1 n (stageRestrict n X) =
      normalizedTraceReadoutFamily.1 (n + 1) X := by
  exact compatible_apply normalizedTraceReadoutFamily n X

theorem compatible_family_readout_unique_at_stage
    (ρ : CompatibleContinuousReadoutFamily)
    (hρ : ∀ n : ℕ, ρ.1 n = normalizedTraceReadoutFamily.1 n) :
    ρ.1 0 = normalizedTraceReadoutFamily.1 0 := by
  exact hρ 0

theorem continuous_readout_coordinate
    (n : ℕ) :
    Continuous (fun ρ : CompatibleContinuousReadoutFamily => ρ.1 n) := by
  exact (continuous_apply n).comp continuous_subtype_val

end InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
