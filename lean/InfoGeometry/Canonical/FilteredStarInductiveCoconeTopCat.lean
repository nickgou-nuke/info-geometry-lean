import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# Topological cocones from star-algebraic filtered cocones

This file does not introduce a new completion or a scalar surrogate.  It
forgets only the algebraic structure of an existing star-algebraic cocone and
records its continuous maps into the categorical `TopCat` colimit.
-/

noncomputable section

namespace CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I]
variable {Stage : I → Type u}
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable {Ainf : Type u}
variable [CStarAlgebra Ainf] [PartialOrder Ainf] [StarOrderedRing Ainf]
variable (cocone : StarInductiveCocone (Ainf := Ainf) Stage sys)

def continuousMap (i : I) : ContinuousMap (Stage i) Ainf :=
  { toFun := cocone.ι i
    continuous_toFun :=
      (starAlgHomToContinuousLinearMap (cocone.ι i)).continuous }

omit [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)] [PartialOrder Ainf]
  [StarOrderedRing Ainf] in
@[simp] theorem continuousMap_apply (i : I) (a : Stage i) :
    continuousMap sys cocone i a = cocone.ι i a :=
  rfl

def toTopCatCocone : Cocone (topologicalDiagram Stage sys) where
  pt := TopCat.of Ainf
  ι :=
    { app := fun i => TopCat.ofHom (continuousMap sys cocone i)
      naturality := by
        intro i j f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro a
        change cocone.ι j (sys.map (leOfHom f) a) = cocone.ι i a
        exact congrArg (fun g : Stage i →⋆ₐ[ℂ] Ainf => g a)
          (cocone.ι_comm (leOfHom f)) }

omit [PartialOrder Ainf] [StarOrderedRing Ainf] in
@[simp] theorem toTopCatCocone_app_apply (i : I) (a : Stage i) :
    (toTopCatCocone sys cocone).ι.app i a = cocone.ι i a :=
  rfl

noncomputable def toTopologicalColimitMap :
    topologicalColimit Stage sys ⟶ TopCat.of Ainf :=
  topologicalDirectDescend (topologicalDiagram Stage sys)
    (toTopCatCocone sys cocone)

omit [PartialOrder Ainf] [StarOrderedRing Ainf] in
theorem toTopologicalColimitMap_inclusion (i : I) (a : Stage i) :
    toTopologicalColimitMap sys cocone
        (topologicalInjection Stage sys i a) = cocone.ι i a := by
  have h := topologicalDirectDescend_stage
    (topologicalDiagram Stage sys) (toTopCatCocone sys cocone) i
  exact congrArg (fun f => f a) h

def stateContinuousMap (ω : State Ainf) (i : I) :
    ContinuousMap (Stage i) (ULift ℂ) :=
  { toFun := fun a => ULift.up (ω.functional (cocone.ι i a))
    continuous_toFun :=
      continuous_uliftUp.comp (ω.toContinuousLinearMap.comp
        (starAlgHomToContinuousLinearMap (cocone.ι i))).continuous }

omit [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)] in
@[simp] theorem stateContinuousMap_apply
    (ω : State Ainf) (i : I) (a : Stage i) :
    stateContinuousMap sys cocone ω i a = ULift.up (ω.functional (cocone.ι i a)) :=
  rfl

def stateToTopCatCocone (ω : State Ainf) :
    Cocone (topologicalDiagram Stage sys) where
  pt := TopCat.of (ULift ℂ)
  ι :=
    { app := fun i => TopCat.ofHom (stateContinuousMap sys cocone ω i)
      naturality := by
        intro i j f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro a
        change ULift.up (ω.functional (cocone.ι j (sys.map (leOfHom f) a))) =
          ULift.up (ω.functional (cocone.ι i a))
        exact congrArg ULift.up
          (state_readout_transition Stage sys cocone ω (leOfHom f) a) }

noncomputable def stateTopologicalColimitMap (ω : State Ainf) :
    topologicalColimit Stage sys ⟶ TopCat.of (ULift ℂ) :=
  topologicalDirectDescend (topologicalDiagram Stage sys)
    (stateToTopCatCocone sys (cocone := cocone) ω)

theorem stateTopologicalColimitMap_inclusion
    (ω : State Ainf) (i : I) (a : Stage i) :
    stateTopologicalColimitMap sys cocone ω
        (topologicalInjection Stage sys i a) =
      ULift.up (ω.functional (cocone.ι i a)) := by
  have h := topologicalDirectDescend_stage
    (topologicalDiagram Stage sys)
      (stateToTopCatCocone sys (cocone := cocone) ω) i
  exact congrArg (fun f => f a) h

/-- The state readout is the unique TopCat morphism with the prescribed
finite-stage evaluations. -/
theorem stateTopologicalColimitMap_unique
    (ω : State Ainf)
    (f : topologicalColimit Stage sys ⟶ TopCat.of (ULift ℂ))
    (hf : ∀ (i : I) (a : Stage i),
      f (topologicalInjection Stage sys i a) =
        ULift.up (ω.functional (cocone.ι i a))) :
    f = stateTopologicalColimitMap sys cocone ω := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change f (topologicalInjection Stage sys i a) =
    stateTopologicalColimitMap sys cocone ω
      (topologicalInjection Stage sys i a)
  rw [hf, stateTopologicalColimitMap_inclusion]

/-- The state readout on the topological colimit factors through the
star-algebraic colimit realization.  This is the colimit-level form of the
stage compatibility law, with the scalar codomain lifted to the ambient
`TopCat` universe. -/
def stateOnAinfContinuousMap (ω : State Ainf) :
    ContinuousMap Ainf (ULift ℂ) :=
  { toFun := fun a => ULift.up (ω.functional a)
    continuous_toFun :=
      continuous_uliftUp.comp ω.toContinuousLinearMap.continuous }

@[reassoc]
theorem stateTopologicalColimitMap_factorization
    (ω : State Ainf) :
    stateTopologicalColimitMap sys cocone ω =
      toTopologicalColimitMap sys cocone ≫
        TopCat.ofHom (stateOnAinfContinuousMap ω) := by
  apply colimit.hom_ext
  intro i
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change stateTopologicalColimitMap sys cocone ω
      (topologicalInjection Stage sys i a) =
    ULift.up (ω.functional
      (toTopologicalColimitMap sys cocone
        (topologicalInjection Stage sys i a)))
  rw [stateTopologicalColimitMap_inclusion,
    toTopologicalColimitMap_inclusion]

end CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone
