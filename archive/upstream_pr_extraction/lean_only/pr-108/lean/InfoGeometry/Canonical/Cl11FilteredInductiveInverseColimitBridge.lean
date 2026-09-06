import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
import InfoGeometry.Canonical.Cl11TensorInductiveLimit
import InfoGeometry.Clifford.Cl11MarkovJonesEngine
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Native filtered and inverse readouts for the `Cl(1,1)` tower

This owner packages the existing finite matrix tower in the repository's
`ModuleCat` filtered-colimit interface.  The normalized trace is recorded as
the corresponding compatible inverse family of dual linear maps.  No analytic
completion, infinite tensor product, or second colimit carrier is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge

open CategoryTheory CategoryTheory.Limits
open FilteredColimit
open FilteredColimit.Native
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
open InfoGeometry.Canonical.Cl11TensorInductiveLimit

abbrev Stage (n : ℕ) : Type := MatStage n
abbrev Limit : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

def directSystem : DirectInductiveSystem ℝ ℕ Stage where
  f := fun {m n} h => (stageEmbedMap h).toLinearMap
  f_id := by
    intro n
    apply LinearMap.ext
    intro x
    exact stageEmbedMap_apply_refl n x
  f_comp := by
    intro m n k hmn hnk
    apply LinearMap.ext
    intro x
    change stageEmbedMap hnk (stageEmbedMap hmn x) =
      stageEmbedMap (hmn.trans hnk) x
    exact congrArg (fun F => F x) (stageEmbedMap_comp hmn hnk)

def colimitCocone : InductiveCocone ℝ directSystem Limit :=
  ⟨fun n => (ofStageAlgHom n).toLinearMap, by
    intro m n h
    ext x
    change ofStage n (stageEmbedMap h x) = ofStage m x
    induction h with
    | refl =>
        simp [stageEmbedMap_refl]
    | @step n h ih =>
        rw [stageEmbedMap_succ h]
        change ofStage (n + 1)
            (stageEmbed n (stageEmbedMap h x)) = ofStage m x
        rw [ofStage_apply_bond]
        exact ih⟩

theorem colimitCocone_eval
    {m n : ℕ} (h : m ≤ n) (x : Stage m) :
    colimitCocone.psi n (directSystem.f h x) =
      colimitCocone.psi m x := by
  exact InductiveCocone.cocone_eval_comm colimitCocone h x

def traceCocone : InductiveCocone ℝ directSystem ℝ :=
  ⟨fun n =>
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n, by
    intro m n h
    ext x
    change normalizedTrace n (stageEmbedMap h x) = normalizedTrace m x
    exact normalizedTrace_stageEmbedMap h x⟩

theorem traceCocone_eval
    {m n : ℕ} (h : m ≤ n) (x : Stage m) :
    traceCocone.psi n (directSystem.f h x) =
      traceCocone.psi m x := by
  exact InductiveCocone.cocone_eval_comm traceCocone h x

noncomputable def nativeModuleColimit : ModuleCat ℝ :=
  colimit (moduleDiagram directSystem)

noncomputable def limitReadout :
    nativeModuleColimit ⟶ ModuleCat.of ℝ Limit :=
  descendModuleCocone directSystem colimitCocone

@[reassoc]
theorem limitReadout_stage (n : ℕ) :
    colimit.ι (moduleDiagram directSystem) n ≫ limitReadout =
      (moduleCocone directSystem colimitCocone).ι.app n := by
  exact moduleColimit_desc_stage directSystem colimitCocone n

theorem limitReadout_stage_apply (n : ℕ) (x : Stage n) :
    limitReadout ((colimit.ι (moduleDiagram directSystem) n).hom x) =
      ofStage n x := by
  have h := congrArg (fun f => f x) (limitReadout_stage n)
  exact h

noncomputable def traceReadout :
    nativeModuleColimit ⟶ ModuleCat.of ℝ ℝ :=
  descendModuleCocone directSystem traceCocone

@[reassoc]
theorem traceReadout_stage (n : ℕ) :
    colimit.ι (moduleDiagram directSystem) n ≫ traceReadout =
      (moduleCocone directSystem traceCocone).ι.app n := by
  exact moduleColimit_desc_stage directSystem traceCocone n

theorem traceReadout_stage_apply (n : ℕ) (x : Stage n) :
    traceReadout ((colimit.ι (moduleDiagram directSystem) n).hom x) =
      normalizedTrace n x := by
  have h := congrArg (fun f => f x) (traceReadout_stage n)
  exact h

def dualTraceTransition {m n : ℕ} (h : m ≤ n) :
    (Stage n →ₗ[ℝ] ℝ) →ₗ[ℝ] (Stage m →ₗ[ℝ] ℝ) :=
  FilteredColimit.InductiveCocone.dualInverseTransition directSystem h

theorem dualTraceTransition_apply
    {m n : ℕ} (h : m ≤ n) (φ : Stage n →ₗ[ℝ] ℝ) (x : Stage m) :
    dualTraceTransition h φ x = φ (directSystem.f h x) := by
  rfl

theorem normalizedTrace_dual_compatibility
    {m n : ℕ} (h : m ≤ n) (x : Stage m) :
    dualTraceTransition h
        (InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n) x =
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear m x := by
  exact normalizedTrace_stageEmbedMap h x

end InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge
