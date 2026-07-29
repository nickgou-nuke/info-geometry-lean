import InfoGeometry.Canonical.FilteredGNSHilbertColimit

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
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
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

end CStarStateColimit.Native.FilteredGNSHilbertColimitTopology
