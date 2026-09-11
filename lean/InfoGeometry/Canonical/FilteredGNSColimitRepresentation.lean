import InfoGeometry.Canonical.FilteredGNSRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Universal representation of a filtered GNS colimit

Mathlib currently supplies the required colimits in `ModuleCat`, but not a
colimit category of C-star algebras whose morphisms are `StarAlgHom`s.
Accordingly, this file does not relabel a ring or module colimit as a C-star
colimit.

Instead, a genuine star-algebraic cocone into a C-star algebra `A∞`, together
with a normalized positive state on `A∞`, induces:

* the compatible inverse family of restricted stage states;
* a cocone from the completed stage GNS spaces to the target GNS space;
* the universal linear map from the native GNS module colimit;
* compatibility of that universal map with every represented stage
  observable.

No commutativity or diagonalization hypothesis is used.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CategoryTheory CategoryTheory.Limits

universe u

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable
  (sys :
    ContinuousStarInductiveSystem Stage)

variable {Ainf : Type u}
variable [CStarAlgebra Ainf] [PartialOrder Ainf] [StarOrderedRing Ainf]
variable
  (cocone :
    ContinuousStarInductiveSystem.StarInductiveCocone
      (Ainf := Ainf) Stage sys)
variable (Ω : State Ainf)

/-- The inverse family of stage states obtained from the target state. -/
abbrev restrictedStateFamily :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys :=
  ContinuousStarInductiveSystem.StarInductiveCocone.restrictStateFamily
    Stage sys cocone Ω

/-- The stage-to-target GNS map induced by the star-cocone leg. -/
def stageTargetGNSMap
    (i : I) :
    ((restrictedStateFamily Stage sys cocone Ω).state i).functional.GNS →
      Ω.functional.GNS :=
  gnsMap (cocone.ι i) Ω

/-- The stage-to-target map agrees with the star-cocone leg on the dense
algebraic GNS vectors. -/
@[simp] theorem stageTargetGNSMap_toPreGNS
    (i : I) (a : Stage i) :
    stageTargetGNSMap Stage sys cocone Ω i
        (((restrictedStateFamily Stage sys cocone Ω).state i).functional.toPreGNS a :
          ((restrictedStateFamily Stage sys cocone Ω).state i).functional.GNS) =
      (Ω.functional.toPreGNS (cocone.ι i a) :
        Ω.functional.GNS) :=
  gnsMap_toPreGNS (cocone.ι i) Ω a

/-- The stage-to-target GNS maps commute with the filtered transitions on the
whole completed spaces. -/
theorem stageTargetGNSMap_transition
    {i j : I} (hij : i ≤ j) :
    stageTargetGNSMap Stage sys cocone Ω j ∘
        filteredGNSMap Stage sys
          (restrictedStateFamily Stage sys cocone Ω) hij =
      stageTargetGNSMap Stage sys cocone Ω i := by
  apply UniformSpace.Completion.denseRange_coe.equalizer
  · exact
      (gnsMap_isometry (cocone.ι j) Ω).continuous.comp
        (filteredGNSMap_isometry Stage sys
          (restrictedStateFamily Stage sys cocone Ω) hij).continuous
  · exact
      (gnsMap_isometry (cocone.ι i) Ω).continuous
  · funext x
    obtain ⟨a, rfl⟩ :=
      (((restrictedStateFamily Stage sys cocone Ω).state i).functional.toPreGNS).surjective x
    change
      stageTargetGNSMap Stage sys cocone Ω j
          (filteredGNSMap Stage sys
            (restrictedStateFamily Stage sys cocone Ω) hij
            ((((restrictedStateFamily Stage sys cocone Ω).state i).functional.toPreGNS a :
              ((restrictedStateFamily Stage sys cocone Ω).state i).functional.PreGNS) :
              ((restrictedStateFamily Stage sys cocone Ω).state i).functional.GNS)) =
        stageTargetGNSMap Stage sys cocone Ω i
          ((((restrictedStateFamily Stage sys cocone Ω).state i).functional.toPreGNS a :
            ((restrictedStateFamily Stage sys cocone Ω).state i).functional.PreGNS) :
            ((restrictedStateFamily Stage sys cocone Ω).state i).functional.GNS)
    rw [
      filteredGNSMap_toPreGNS,
      stageTargetGNSMap_toPreGNS,
      stageTargetGNSMap_toPreGNS]
    have hleg := congrArg
      (fun f : Stage i →⋆ₐ[ℂ] Ainf => f a)
      (cocone.ι_comm hij)
    exact congrArg
      (fun y : Ainf =>
        (Ω.functional.toPreGNS y :
          Ω.functional.GNS))
      hleg

/-- Linear cocone from the completed GNS system to the target GNS space. -/
def gnsTargetInductiveCocone :
    FilteredColimit.InductiveCocone
      ℂ
      (gnsDirectInductiveSystem Stage sys
        (restrictedStateFamily Stage sys cocone Ω))
      Ω.functional.GNS where
  psi := fun i =>
    (gnsMapCLM (cocone.ι i) Ω).toLinearMap
  psi_comm := by
    intro i j hij
    ext x
    change
      gnsMapCLM (cocone.ι j) Ω
          (filteredGNSMapCLM Stage sys
            (restrictedStateFamily Stage sys cocone Ω) hij x) =
        gnsMapCLM (cocone.ι i) Ω x
    rw [filteredGNSMapCLM_apply, gnsMapCLM_apply, gnsMapCLM_apply]
    exact congrFun
      (stageTargetGNSMap_transition
        Stage sys cocone Ω hij) x

/-- The categorical `ModuleCat` cocone induced by the target GNS
representation. -/
def gnsTargetModuleCocone :
    Cocone
      (gnsModuleDiagram Stage sys
        (restrictedStateFamily Stage sys cocone Ω)) where
  pt := ModuleCat.of ℂ Ω.functional.GNS
  ι :=
    { app := fun i =>
        ModuleCat.ofHom
          ((gnsTargetInductiveCocone
            Stage sys cocone Ω).psi i)
      naturality := by
        intro i j f
        ext x
        exact LinearMap.congr_fun
          ((gnsTargetInductiveCocone
            Stage sys cocone Ω).psi_comm
              (leOfHom f)) x }

/-- Bundled categorical universal morphism from the native GNS module colimit
to the target GNS representation. -/
noncomputable def descendGNSColimitHom :
    colimit
        (gnsModuleDiagram Stage sys
          (restrictedStateFamily Stage sys cocone Ω)) ⟶
      (gnsTargetModuleCocone Stage sys cocone Ω).pt :=
  colimit.desc
    (gnsModuleDiagram Stage sys
      (restrictedStateFamily Stage sys cocone Ω))
    (gnsTargetModuleCocone Stage sys cocone Ω)

/-- Universal linear map from the native GNS module colimit to the target GNS
representation. -/
noncomputable def descendGNSColimit :
    GNSModuleColimit Stage sys
        (restrictedStateFamily Stage sys cocone Ω) →ₗ[ℂ]
      Ω.functional.GNS :=
  (descendGNSColimitHom Stage sys cocone Ω).hom

/-- The categorical descent is uniquely determined by its restrictions to all
filtered GNS stages. -/
theorem descendGNSColimitHom_unique
    (T :
      colimit
          (gnsModuleDiagram Stage sys
            (restrictedStateFamily Stage sys cocone Ω)) ⟶
        (gnsTargetModuleCocone Stage sys cocone Ω).pt)
    (hT :
      ∀ i,
        colimit.ι
            (gnsModuleDiagram Stage sys
              (restrictedStateFamily Stage sys cocone Ω)) i ≫ T =
          (gnsTargetModuleCocone Stage sys cocone Ω).ι.app i) :
    T = descendGNSColimitHom Stage sys cocone Ω := by
  apply colimit.hom_ext
  intro i
  rw [hT i]
  exact
    (colimit.ι_desc
      (gnsTargetModuleCocone Stage sys cocone Ω) i).symm

/-- The linear descent is the underlying linear map of the categorical
universal morphism. -/
theorem descendGNSColimit_eq_hom :
    descendGNSColimit Stage sys cocone Ω =
      (descendGNSColimitHom Stage sys cocone Ω).hom :=
  rfl

/-- The universal map agrees with the concrete target GNS map at every
stage. -/
theorem descendGNSColimit_stage
    (i : I)
    (x :
      ((restrictedStateFamily Stage sys cocone Ω).state i).functional.GNS) :
    descendGNSColimit Stage sys cocone Ω
        (gnsColimitInclusion Stage sys
          (restrictedStateFamily Stage sys cocone Ω) i x) =
      stageTargetGNSMap Stage sys cocone Ω i x := by
  have hι :=
    colimit.ι_desc
      (gnsTargetModuleCocone Stage sys cocone Ω) i
  exact congrArg
    (fun f :
      (gnsModuleDiagram Stage sys
        (restrictedStateFamily Stage sys cocone Ω)).obj i ⟶
          (gnsTargetModuleCocone Stage sys cocone Ω).pt =>
      f x)
    hι

/-- The universal colimit map intertwines every represented stage observable
with its image under the star-cocone leg. -/
theorem descendGNSColimit_representation
    (i : I)
    (a : Stage i)
    (x :
      ((restrictedStateFamily Stage sys cocone Ω).state i).functional.GNS) :
    descendGNSColimit Stage sys cocone Ω
        (gnsColimitInclusion Stage sys
          (restrictedStateFamily Stage sys cocone Ω) i
          (((restrictedStateFamily Stage sys cocone Ω).state i).functional.gnsStarAlgHom a x)) =
      Ω.functional.gnsStarAlgHom (cocone.ι i a)
        (descendGNSColimit Stage sys cocone Ω
          (gnsColimitInclusion Stage sys
            (restrictedStateFamily Stage sys cocone Ω) i x)) := by
  rw [descendGNSColimit_stage, descendGNSColimit_stage]
  have hintertwine :=
    congrFun
      (gnsMap_intertwines (cocone.ι i) Ω a) x
  exact hintertwine

end CStarStateColimit.Native.FilteredGNSColimit
