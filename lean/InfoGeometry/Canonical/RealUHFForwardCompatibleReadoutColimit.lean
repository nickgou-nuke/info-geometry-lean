import InfoGeometry.Canonical.RealUHFCompatibleStateObservableTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CliffordCARTopologicalColimit
import InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace

/-!
# Forward-compatible continuous readouts on the real Clifford tower

The projective readout family uses backward restriction maps.  A readout on
the `TopCat` direct colimit requires a separate compatibility condition for
the forward bonding maps.  This owner formalizes that distinction and then
uses the native colimit universal property to construct the readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFForwardCompatibleReadoutColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalTrace
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Clifford.Cl11TensorTower
open FilteredColimit.Native.Topological

abbrev ReadoutFamily :=
  ∀ n : ℕ, MatStage n →L[ℝ] ℝ

def ForwardCompatible (ρ : ReadoutFamily) : Prop :=
  ∀ {m n : ℕ} (hmn : m ≤ n),
    ρ n ∘L bondCLM m n hmn = ρ m

def ForwardCompatibleStageFlow
    (D : InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics.CompatibleStageFlow) : Prop :=
  ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ),
    (D.flow n t).comp (bondCLM m n hmn) =
      (bondCLM m n hmn).comp (D.flow m t)

def forwardPullback
    (D : InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics.CompatibleStageFlow)
    (t : ℝ) (ρ : ReadoutFamily) : ReadoutFamily :=
  fun n => (ρ n).comp (D.flow n t)

theorem scalarDilationStageFlow_forwardCompatible :
    ForwardCompatibleStageFlow
      InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics.scalarDilationStageFlow := by
  intro m n hmn t
  ext X
  simp [InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics.scalarDilationStageFlow]

theorem forwardPullback_preserves_forwardCompatibility
    (D : InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics.CompatibleStageFlow)
    (hD : ForwardCompatibleStageFlow D) (t : ℝ)
    (ρ : ReadoutFamily) (hρ : ForwardCompatible ρ) :
    ForwardCompatible (forwardPullback D t ρ) := by
  intro m n hmn
  ext X
  change ρ n (D.flow n t (bondCLM m n hmn X)) =
    ρ m (D.flow m t X)
  have hflow := congrArg (fun q => q X) (hD hmn t)
  have hflow' : D.flow n t (bondCLM m n hmn X) =
      bondCLM m n hmn (D.flow m t X) := by
    simpa [ContinuousLinearMap.comp_apply] using hflow
  calc
    ρ n (D.flow n t (bondCLM m n hmn X)) =
        ρ n (bondCLM m n hmn (D.flow m t X)) := by
          rw [hflow']
    _ = ρ m (D.flow m t X) := by
      exact congrArg (fun q => q (D.flow m t X)) (hρ hmn)

def readoutTopCatHom (ρ : ReadoutFamily) (n : ℕ) :
    TopCat.of (MatStage n) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    (ContinuousMap.mk (ρ n) (ρ n).continuous)

@[simp] theorem readoutTopCatHom_apply
    (ρ : ReadoutFamily) (n : ℕ) (X : MatStage n) :
    readoutTopCatHom ρ n X = ρ n X :=
  rfl

def forwardReadoutCocone (ρ : ReadoutFamily)
    (hρ : ForwardCompatible ρ) : Cocone topologicalDiagram where
  pt := TopCat.of ℝ
  ι :=
    { app := fun n => readoutTopCatHom ρ n
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro X
        change ρ n (bondCLM m n (leOfHom f) X) = ρ m X
        have h := congrArg (fun q => q X) (hρ (leOfHom f))
        simpa [ContinuousLinearMap.comp_apply] using h }

noncomputable def forwardCompatibleReadoutColimitMap
    (ρ : ReadoutFamily) (hρ : ForwardCompatible ρ) :
    topologicalColimit ⟶ TopCat.of ℝ :=
  colimit.desc topologicalDiagram (forwardReadoutCocone ρ hρ)

theorem forwardCompatibleReadoutColimitMap_stage
    (ρ : ReadoutFamily) (hρ : ForwardCompatible ρ)
    (n : ℕ) (X : MatStage n) :
    forwardCompatibleReadoutColimitMap ρ hρ
        (topologicalInjection n X) = ρ n X := by
  exact topologicalDirectDescend_stage_apply
    topologicalDiagram (forwardReadoutCocone ρ hρ) n X

theorem forwardCompatibleReadoutColimitMap_unique
    (ρ : ReadoutFamily) (hρ : ForwardCompatible ρ)
    (f : topologicalColimit ⟶ TopCat.of ℝ)
    (hf : ∀ (n : ℕ) (X : MatStage n),
      f (topologicalInjection n X) = ρ n X) :
    f = forwardCompatibleReadoutColimitMap ρ hρ := by
  change f = colimit.desc topologicalDiagram
    (forwardReadoutCocone ρ hρ)
  refine topologicalDirectDescend_unique topologicalDiagram
    (forwardReadoutCocone ρ hρ) f ?_
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  exact hf n X

theorem normalizedTraceReadoutFamily_forwardCompatible :
    ForwardCompatible normalizedTraceReadoutFamily.1 := by
  intro m n hmn
  ext X
  change normalizedTrace n (bondAlgHom m n hmn X) = normalizedTrace m X
  exact normalizedTrace_bondAlgHom m n hmn X

theorem normalizedTraceReadoutFamily_colimitMap_eq
    : forwardCompatibleReadoutColimitMap
        normalizedTraceReadoutFamily.1
        normalizedTraceReadoutFamily_forwardCompatible =
      normalizedTraceTopologicalColimitMap := by
  apply normalizedTraceTopologicalColimitMap_unique
  intro n X
  exact forwardCompatibleReadoutColimitMap_stage
    normalizedTraceReadoutFamily.1
    normalizedTraceReadoutFamily_forwardCompatible n X


end InfoGeometry.Canonical.RealUHFForwardCompatibleReadoutColimit
