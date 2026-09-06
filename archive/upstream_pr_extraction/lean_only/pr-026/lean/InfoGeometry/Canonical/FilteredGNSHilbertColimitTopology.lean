import InfoGeometry.Canonical.FilteredGNSHilbertColimit
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Topological cocone API for the filtered GNS Hilbert colimit

The Hilbert-colimit owner already supplies stage `LinearIsometry`s, their
filtered transition law, and density of the union of stage images.  This
file exposes exactly that data in Mathlib's continuous-linear-map language.
No coordinates, finite enumeration, or analytic approximation argument is
introduced: continuity is inherited from the isometry and density from the
native completion theorem.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSHilbertColimitTopology

set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CategoryTheory CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

/-- The canonical continuous-linear map from a completed GNS stage into the
global Hilbert colimit. -/
def gnsStageToHilbertColimitContinuousLinearMap (i : I) :
    (ω.state i).functional.GNS →L[ℂ]
      GNSHilbertColimit Stage sys ω :=
  (gnsStageToHilbertColimit Stage sys ω i).toContinuousLinearMap

@[simp] theorem gnsStageToHilbertColimitContinuousLinearMap_apply
    (i : I) (x : (ω.state i).functional.GNS) :
    gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i x =
      gnsStageToHilbertColimit Stage sys ω i x :=
  rfl

/- The continuous maps form the same filtered cocone as the underlying
linear isometries. -/
@[simp] theorem gnsStageToHilbertColimitContinuousLinearMap_transition
    {i j : I} (hij : i ≤ j)
    (x : (ω.state i).functional.GNS) :
    gnsStageToHilbertColimitContinuousLinearMap Stage sys ω j
        ((filteredGNSLinearIsometry Stage sys ω hij).toContinuousLinearMap x) =
      gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i x := by
  change gnsStageToHilbertColimit Stage sys ω j
      (filteredGNSLinearIsometry Stage sys ω hij x) =
    gnsStageToHilbertColimit Stage sys ω i x
  rw [filteredGNSLinearIsometry_apply]
  exact gnsStageToHilbertColimit_transition Stage sys ω hij x

/-- The union of the ranges of the continuous stage maps is dense in the
completed filtered GNS colimit. -/
theorem dense_iUnion_range_gnsStageToHilbertColimitContinuousLinearMap :
    Dense
      (⋃ i : I,
        Set.range
          (gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i)) := by
  simpa [gnsStageToHilbertColimitContinuousLinearMap] using
    dense_iUnion_range_gnsStageToHilbertColimit Stage sys ω

private def gnsTopologicalTransitionMap
    {i j : I} (hij : i ≤ j) :
    ContinuousMap
      (ω.state i).functional.GNS (ω.state j).functional.GNS :=
  { toFun := filteredGNSMapCLM Stage sys ω hij
    continuous_toFun := (filteredGNSMapCLM Stage sys ω hij).continuous }

/-- The completed GNS stages form a genuine `TopCat` diagram. -/
def gnsTopologicalDiagram : I ⥤ TopCat.{u} where
  obj i := TopCat.of ((ω.state i).functional.GNS)
  map f := TopCat.ofHom
    (gnsTopologicalTransitionMap Stage sys ω (leOfHom f))
  map_id i := by
    ext x
    change filteredGNSMapCLM Stage sys ω (le_refl i) x = x
    rw [filteredGNSMapCLM_apply]
    exact congrFun (filteredGNSMap_id Stage sys ω i) x
  map_comp f g := by
    ext x
    simp only [ConcreteCategory.comp_apply]
    simpa [gnsTopologicalTransitionMap, filteredGNSMapCLM_apply] using
      congrFun
        (filteredGNSMap_comp Stage sys ω (leOfHom f) (leOfHom g)).symm x

/-- The canonical continuous stage maps form a topological cocone into the
completed filtered GNS colimit. -/
def gnsTopologicalCocone :
    Cocone (gnsTopologicalDiagram Stage sys ω) where
  pt := TopCat.of (GNSHilbertColimit Stage sys ω)
  ι :=
    { app := fun i => TopCat.ofHom
        { toFun := gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i
          continuous_toFun :=
            (gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i).continuous }
      naturality := by
        intro i j f
        ext x
        change gnsStageToHilbertColimitContinuousLinearMap Stage sys ω j
              (filteredGNSMapCLM Stage sys ω (leOfHom f) x) =
          gnsStageToHilbertColimitContinuousLinearMap Stage sys ω i x
        rw [gnsStageToHilbertColimitContinuousLinearMap_apply,
          filteredGNSMapCLM_apply,
          gnsStageToHilbertColimitContinuousLinearMap_apply]
        exact gnsStageToHilbertColimit_transition
          Stage sys ω (leOfHom f) x }

/-- The universal continuous map from the categorical TopCat colimit of the
GNS stages to the concrete Hilbert colimit. -/
noncomputable def gnsTopologicalColimitToHilbert :
    topologicalDirectColimit (gnsTopologicalDiagram Stage sys ω) ⟶
      (gnsTopologicalCocone Stage sys ω).pt :=
  topologicalDirectDescend
    (gnsTopologicalDiagram Stage sys ω)
    (gnsTopologicalCocone Stage sys ω)

@[reassoc]
theorem gnsTopologicalColimitToHilbert_stage
    (i : I) :
    topologicalDirectInjection
        (gnsTopologicalDiagram Stage sys ω) i ≫
      gnsTopologicalColimitToHilbert Stage sys ω =
      (gnsTopologicalCocone Stage sys ω).ι.app i := by
  exact topologicalDirectDescend_stage
    (gnsTopologicalDiagram Stage sys ω)
    (gnsTopologicalCocone Stage sys ω) i

theorem gnsTopologicalColimitToHilbert_unique
    (f : topologicalDirectColimit (gnsTopologicalDiagram Stage sys ω) ⟶
      (gnsTopologicalCocone Stage sys ω).pt)
    (h : ∀ i : I,
      topologicalDirectInjection (gnsTopologicalDiagram Stage sys ω) i ≫ f =
        (gnsTopologicalCocone Stage sys ω).ι.app i) :
    f = gnsTopologicalColimitToHilbert Stage sys ω := by
  apply topologicalDirectDescend_unique
    (gnsTopologicalDiagram Stage sys ω)
    (gnsTopologicalCocone Stage sys ω) f
  intro i
  exact h i

end CStarStateColimit.Native.FilteredGNSHilbertColimitTopology
