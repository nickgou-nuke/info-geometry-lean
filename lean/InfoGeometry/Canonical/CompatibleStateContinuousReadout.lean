import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
import InfoGeometry.Canonical.FilteredStarInductiveCoconeTopCat

/-!
# Continuous readouts of compatible filtered states

This is a topological adapter for the native compatible-state family.  It
packages the continuous linear functionals and their restriction equations;
it does not assert that a projective limit of state spaces has been
constructed.
-/

noncomputable section

namespace CStarStateColimit.Native.ContinuousStarInductiveSystem

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

structure CompatibleContinuousStateReadout where
  readout : ∀ i, Stage i →L[ℂ] ℂ
  transition_naturality : ∀ {i j : I} (hij : i ≤ j),
    (readout j).comp (sys.transitionCLM Stage hij) = readout i

namespace CompatibleContinuousStateReadout

variable (ρ : CompatibleContinuousStateReadout Stage sys)

@[simp] theorem apply_transition
    {i j : I} (hij : i ≤ j) (a : Stage i) :
    ρ.readout j (sys.map hij a) = ρ.readout i a := by
  have h := congrArg (fun f : Stage i →L[ℂ] ℂ => f a)
    (ρ.transition_naturality hij)
  exact h

theorem compatible_trans
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    ((ρ.readout k).comp (sys.transitionCLM Stage hjk)).comp
        (sys.transitionCLM Stage hij) = ρ.readout i := by
  ext a
  change ρ.readout k (sys.map hjk (sys.map hij a)) = ρ.readout i a
  rw [CompatibleContinuousStateReadout.apply_transition
    Stage sys ρ hjk (sys.map hij a)]
  exact CompatibleContinuousStateReadout.apply_transition Stage sys ρ hij a

def toTopCatCocone
    (ρ : CompatibleContinuousStateReadout Stage sys) :
    Cocone (topologicalDiagram Stage sys) where
  pt := TopCat.of (ULift ℂ)
  ι :=
    { app := fun i =>
        TopCat.ofHom
          { toFun := fun a => ULift.up (ρ.readout i a)
            continuous_toFun :=
              continuous_uliftUp.comp (ρ.readout i).continuous }
      naturality := by
        intro i j f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro a
        change ULift.up (ρ.readout j (sys.map (leOfHom f) a)) =
          ULift.up (ρ.readout i a)
        rw [CompatibleContinuousStateReadout.apply_transition
          Stage sys ρ (leOfHom f) a] }

@[simp] theorem toTopCatCocone_apply
    (ρ : CompatibleContinuousStateReadout Stage sys) (i : I) (a : Stage i) :
    (ρ.toTopCatCocone Stage sys).ι.app i a = ULift.up (ρ.readout i a) := rfl

def toTopCatNaturalTransformation
    (ρ : CompatibleContinuousStateReadout Stage sys) :
    topologicalDiagram Stage sys ⟶
      (Functor.const I).obj (TopCat.of (ULift ℂ)) :=
  (ρ.toTopCatCocone Stage sys).ι

@[simp] theorem toTopCatNaturalTransformation_apply
    (ρ : CompatibleContinuousStateReadout Stage sys) (i : I) (a : Stage i) :
    (ρ.toTopCatNaturalTransformation Stage sys).app i a =
      ULift.up (ρ.readout i a) := rfl

noncomputable def toTopologicalColimitMap
    (ρ : CompatibleContinuousStateReadout Stage sys) :
    topologicalColimit Stage sys ⟶ TopCat.of (ULift ℂ) :=
  colimit.desc (topologicalDiagram Stage sys) (ρ.toTopCatCocone Stage sys)

theorem toTopologicalColimitMap_naturality
    (ρ : CompatibleContinuousStateReadout Stage sys) (i : I) :
    topologicalInjection Stage sys i ≫
        ρ.toTopologicalColimitMap Stage sys =
      (ρ.toTopCatCocone Stage sys).ι.app i := by
  exact topologicalDirectDescend_stage
    (topologicalDiagram Stage sys) (ρ.toTopCatCocone Stage sys) i

theorem toTopologicalColimitMap_inclusion
    (ρ : CompatibleContinuousStateReadout Stage sys) (i : I) (a : Stage i) :
    ρ.toTopologicalColimitMap Stage sys
        (topologicalInjection Stage sys i a) = ULift.up (ρ.readout i a) := by
  have h := topologicalDirectDescend_stage
    (topologicalDiagram Stage sys) (ρ.toTopCatCocone Stage sys) i
  exact congrArg (fun f => f a) h

theorem toTopologicalColimitMap_unique
    (ρ : CompatibleContinuousStateReadout Stage sys)
    (f : topologicalColimit Stage sys ⟶ TopCat.of (ULift ℂ))
    (hf : ∀ (i : I) (a : Stage i),
      f (topologicalInjection Stage sys i a) = ULift.up (ρ.readout i a)) :
    f = ρ.toTopologicalColimitMap Stage sys := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change f (topologicalInjection Stage sys i a) =
    ρ.toTopologicalColimitMap Stage sys
      (topologicalInjection Stage sys i a)
  rw [hf, ρ.toTopologicalColimitMap_inclusion]

theorem toTopCatNaturalTransformation_eq_of_readout_eq
    {ρ σ : CompatibleContinuousStateReadout Stage sys}
    (h : ∀ i : I, ρ.readout i = σ.readout i) :
    ρ.toTopCatNaturalTransformation Stage sys =
      σ.toTopCatNaturalTransformation Stage sys := by
  apply NatTrans.ext
  funext i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change ULift.up (ρ.readout i a) = ULift.up (σ.readout i a)
  rw [h i]

theorem toTopologicalColimitMap_eq_of_readout_eq
    {ρ σ : CompatibleContinuousStateReadout Stage sys}
    (h : ∀ i : I, ρ.readout i = σ.readout i) :
    ρ.toTopologicalColimitMap Stage sys =
      σ.toTopologicalColimitMap Stage sys := by
  symm
  apply toTopologicalColimitMap_unique (Stage := Stage) (sys := sys) ρ
    (σ.toTopologicalColimitMap Stage sys)
  intro i a
  rw [σ.toTopologicalColimitMap_inclusion]
  change ULift.up (σ.readout i a) = ULift.up (ρ.readout i a)
  exact congrArg ULift.up (congrArg (fun f => f a) (h i).symm)

end CompatibleContinuousStateReadout

def CompatibleStateFamily.toContinuousReadout
    (ω : CompatibleStateFamily Stage sys) :
    CompatibleContinuousStateReadout Stage sys where
  readout := fun i => (ω.state i).toContinuousLinearMap
  transition_naturality := by
    intro i j hij
    exact continuousLinearMap_transition Stage sys ω hij

@[simp] theorem CompatibleStateFamily.toContinuousReadout_apply
    (ω : CompatibleStateFamily Stage sys) (i : I) (a : Stage i) :
    (ω.toContinuousReadout Stage sys).readout i a =
      (ω.state i).functional a := rfl

theorem CompatibleStateFamily.toContinuousReadout_transition
    (ω : CompatibleStateFamily Stage sys)
    {i j : I} (hij : i ≤ j) (a : Stage i) :
    (ω.toContinuousReadout Stage sys).readout j (sys.map hij a) =
      (ω.toContinuousReadout Stage sys).readout i a := by
  exact CompatibleContinuousStateReadout.apply_transition Stage sys
    (ω.toContinuousReadout Stage sys) hij a

def CompatibleStateFamily.toTopCatCocone
    (ω : CompatibleStateFamily Stage sys) :
    Cocone (topologicalDiagram Stage sys) where
  pt := TopCat.of (ULift ℂ)
  ι :=
    { app := fun i =>
        TopCat.ofHom
          { toFun := fun a =>
              ULift.up ((ω.toContinuousReadout Stage sys).readout i a)
            continuous_toFun :=
              continuous_uliftUp.comp
                ((ω.toContinuousReadout Stage sys).readout i).continuous }
      naturality := by
        intro i j f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro a
        change ULift.up
            ((ω.toContinuousReadout Stage sys).readout j
              (sys.map (leOfHom f) a)) =
          ULift.up ((ω.toContinuousReadout Stage sys).readout i a)
        rw [CompatibleContinuousStateReadout.apply_transition
          Stage sys (ω.toContinuousReadout Stage sys) (leOfHom f) a] }

@[simp] theorem CompatibleStateFamily.toTopCatCocone_apply
    (ω : CompatibleStateFamily Stage sys) (i : I) (a : Stage i) :
    (ω.toTopCatCocone Stage sys).ι.app i a =
      ULift.up ((ω.toContinuousReadout Stage sys).readout i a) := rfl

noncomputable def CompatibleStateFamily.toTopologicalColimitMap
    (ω : CompatibleStateFamily Stage sys) :
    topologicalColimit Stage sys ⟶ TopCat.of (ULift ℂ) :=
  colimit.desc (topologicalDiagram Stage sys)
    (ω.toTopCatCocone Stage sys)

theorem CompatibleStateFamily.toTopologicalColimitMap_inclusion
    (ω : CompatibleStateFamily Stage sys) (i : I) (a : Stage i) :
    ω.toTopologicalColimitMap Stage sys
        (topologicalInjection Stage sys i a) =
      ULift.up ((ω.toContinuousReadout Stage sys).readout i a) := by
  have h := topologicalDirectDescend_stage
    (topologicalDiagram Stage sys) (ω.toTopCatCocone Stage sys) i
  exact congrArg (fun f => f a) h

theorem CompatibleStateFamily.toTopologicalColimitMap_unique
    (ω : CompatibleStateFamily Stage sys)
    (f : topologicalColimit Stage sys ⟶ TopCat.of (ULift ℂ))
    (hf : ∀ (i : I) (a : Stage i),
      f (topologicalInjection Stage sys i a) =
        ULift.up ((ω.toContinuousReadout Stage sys).readout i a)) :
    f = ω.toTopologicalColimitMap Stage sys := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change f (topologicalInjection Stage sys i a) =
    ω.toTopologicalColimitMap Stage sys
      (topologicalInjection Stage sys i a)
  rw [hf, ω.toTopologicalColimitMap_inclusion]

theorem StarInductiveCocone.restrictedState_topologicalColimitMap_eq
    {Ainf : Type u}
    [CStarAlgebra Ainf] [PartialOrder Ainf] [StarOrderedRing Ainf]
    (cocone : StarInductiveCocone (Ainf := Ainf) Stage sys)
    (ω : State Ainf) :
    (StarInductiveCocone.restrictStateFamily
      (Stage := Stage) (sys := sys) cocone ω).toTopologicalColimitMap Stage sys =
      StarInductiveCocone.stateTopologicalColimitMap
        sys cocone ω := by
  apply CompatibleStateFamily.toTopologicalColimitMap_unique
    (Stage := Stage) (sys := sys)
    (StarInductiveCocone.restrictStateFamily
      (Stage := Stage) (sys := sys) cocone ω)
    (StarInductiveCocone.stateTopologicalColimitMap sys cocone ω)
  intro i a
  rw [StarInductiveCocone.stateTopologicalColimitMap_inclusion]
  rfl

theorem StarInductiveCocone.restrictedState_naturalTransformation_eq
    {Ainf : Type u}
    [CStarAlgebra Ainf] [PartialOrder Ainf] [StarOrderedRing Ainf]
    (cocone : StarInductiveCocone (Ainf := Ainf) Stage sys)
    (ω : State Ainf) :
    ((StarInductiveCocone.restrictStateFamily
      (Stage := Stage) (sys := sys) cocone ω).toContinuousReadout
        Stage sys).toTopCatNaturalTransformation Stage sys =
      (StarInductiveCocone.stateToTopCatCocone
        sys (cocone := cocone) ω).ι := by
  apply NatTrans.ext
  funext i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rfl


end CStarStateColimit.Native.ContinuousStarInductiveSystem
