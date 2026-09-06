import InfoGeometry.Canonical.FilteredGNSRepresentedCStarTopology
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# TopCat form of the represented C-star completion equivalence

The represented completion and its concrete operator closure already carry a
native `ContinuousAlgEquiv`.  This file only packages its two continuous maps
as a categorical `TopCat` isomorphism and records the inverse laws.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarTopCatEquivalence

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSRepresentedCStarTopology
open CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

def completionToClosureTopCatMap :
    TopCat.of (representedAlgebraicRangeCompletion Stage sys ω) ⟶
      TopCat.of (representedCStarClosure Stage sys ω) :=
  TopCat.ofHom
    { toFun := representedRangeCompletionStarAlgEquiv Stage sys ω
      continuous_toFun :=
        (representedRangeCompletionHomeomorph_continuous Stage sys ω) }

def closureToCompletionTopCatMap :
    TopCat.of (representedCStarClosure Stage sys ω) ⟶
      TopCat.of (representedAlgebraicRangeCompletion Stage sys ω) :=
  TopCat.ofHom
    { toFun := (representedRangeCompletionStarAlgEquiv Stage sys ω).symm
      continuous_toFun :=
        (representedRangeCompletionHomeomorph_continuous_inv Stage sys ω) }

theorem completionToClosureTopCatMap_apply (x : representedAlgebraicRangeCompletion Stage sys ω) :
    completionToClosureTopCatMap Stage sys ω x =
      representedRangeCompletionStarAlgEquiv Stage sys ω x :=
  rfl

theorem closureToCompletionTopCatMap_apply (x : representedCStarClosure Stage sys ω) :
    closureToCompletionTopCatMap Stage sys ω x =
      (representedRangeCompletionStarAlgEquiv Stage sys ω).symm x :=
  rfl

/- The categorical hom remembers the verified finite-stage completion readout. -/
@[simp] theorem completionToClosureTopCatMap_stage
    (i : I) (a : Stage i) :
    completionToClosureTopCatMap Stage sys ω
        (algebraicColimitRangeRestrict Stage sys ω
          (algebraicStarDirectLimitOf Stage sys i a)) =
      algebraicColimitToRepresentedClosure Stage sys ω
        (algebraicStarDirectLimitOf Stage sys i a) := by
  simpa [completionToClosureTopCatMap,
    representedRangeCompletionStarAlgEquiv]
    using representedRangeCompletionContinuousAlgEquiv_stage
      Stage sys ω i a

theorem closureToCompletion_comp_completionToClosure :
    completionToClosureTopCatMap Stage sys ω ≫
        closureToCompletionTopCatMap Stage sys ω = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change
    (representedRangeCompletionStarAlgEquiv Stage sys ω).symm
        (representedRangeCompletionStarAlgEquiv Stage sys ω x) = x
  exact (representedRangeCompletionStarAlgEquiv Stage sys ω).left_inv x

theorem completionToClosure_comp_closureToCompletion :
    closureToCompletionTopCatMap Stage sys ω ≫
        completionToClosureTopCatMap Stage sys ω = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change
    representedRangeCompletionStarAlgEquiv Stage sys ω
        ((representedRangeCompletionStarAlgEquiv Stage sys ω).symm x) = x
  exact (representedRangeCompletionStarAlgEquiv Stage sys ω).right_inv x

def completionClosureTopCatIso :
    TopCat.of (representedAlgebraicRangeCompletion Stage sys ω) ≅
      TopCat.of (representedCStarClosure Stage sys ω) where
  hom := completionToClosureTopCatMap Stage sys ω
  inv := closureToCompletionTopCatMap Stage sys ω
  hom_inv_id := closureToCompletion_comp_completionToClosure Stage sys ω
  inv_hom_id := completionToClosure_comp_closureToCompletion Stage sys ω

end CStarStateColimit.Native.FilteredGNSRepresentedCStarTopCatEquivalence
