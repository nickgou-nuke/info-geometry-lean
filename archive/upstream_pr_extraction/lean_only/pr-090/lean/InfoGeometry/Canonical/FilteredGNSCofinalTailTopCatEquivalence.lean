import InfoGeometry.Canonical.FilteredGNSCofinalTailTopology
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# Categorical form of the cofinal GNS-tail equivalence

The cofinal-tail construction already supplies a homeomorphism of the two
completed colimits.  This file exposes that homeomorphism as a `TopCat` iso,
without introducing any additional completion or analytic limit.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSCofinalTailTopCatEquivalence

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSCofinalTail
open CStarStateColimit.Native.FilteredGNSCofinalTailTopology
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSTailStarRepresentation
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
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

def tailToGlobalTopCatMap (i₀ : I) :
    TopCat.of
        (HilbertDirectLimit (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀)) ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω) :=
  TopCat.ofHom
    { toFun := tailHilbertGlobalHomeomorph Stage sys ω i₀
      continuous_toFun := tailHilbertGlobalHomeomorph_continuous Stage sys ω i₀ }

def globalToTailTopCatMap (i₀ : I) :
    TopCat.of (GNSHilbertColimit Stage sys ω) ⟶
      TopCat.of
        (HilbertDirectLimit (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀)) :=
  TopCat.ofHom
    { toFun := (tailHilbertGlobalHomeomorph Stage sys ω i₀).symm
      continuous_toFun :=
        tailHilbertGlobalHomeomorph_continuous_inv Stage sys ω i₀ }

theorem globalToTail_comp_tailToGlobal (i₀ : I) :
    tailToGlobalTopCatMap Stage sys ω i₀ ≫
        globalToTailTopCatMap Stage sys ω i₀ = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change
    (tailHilbertGlobalHomeomorph Stage sys ω i₀).symm
        (tailHilbertGlobalHomeomorph Stage sys ω i₀ x) = x
  exact (tailHilbertGlobalHomeomorph Stage sys ω i₀).left_inv x

theorem tailToGlobal_comp_globalToTail (i₀ : I) :
    globalToTailTopCatMap Stage sys ω i₀ ≫
        tailToGlobalTopCatMap Stage sys ω i₀ = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change
    tailHilbertGlobalHomeomorph Stage sys ω i₀
        ((tailHilbertGlobalHomeomorph Stage sys ω i₀).symm x) = x
  exact (tailHilbertGlobalHomeomorph Stage sys ω i₀).right_inv x

def tailGlobalTopCatIso (i₀ : I) :
    TopCat.of
        (HilbertDirectLimit (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀)) ≅
      TopCat.of (GNSHilbertColimit Stage sys ω) where
  hom := tailToGlobalTopCatMap Stage sys ω i₀
  inv := globalToTailTopCatMap Stage sys ω i₀
  hom_inv_id := globalToTail_comp_tailToGlobal Stage sys ω i₀
  inv_hom_id := tailToGlobal_comp_globalToTail Stage sys ω i₀

@[simp] theorem tailToGlobalTopCatMap_stage
    (i₀ : I) (j : UpperIndex i₀)
    (x : TailGNSStage Stage sys ω i₀ j) :
    tailToGlobalTopCatMap Stage sys ω i₀
        (stageToHilbertDirectLimit
          (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀) j x) =
      gnsStageToHilbertColimit Stage sys ω j.1 x := by
  exact tailHilbertGlobalHomeomorph_stage Stage sys ω i₀ j x

@[simp] theorem globalToTailTopCatMap_stage
    (i₀ : I) (j : UpperIndex i₀)
    (x : TailGNSStage Stage sys ω i₀ j) :
    globalToTailTopCatMap Stage sys ω i₀
        (gnsStageToHilbertColimit Stage sys ω j.1 x) =
      stageToHilbertDirectLimit
        (TailGNSStage Stage sys ω i₀)
        (tailGNSIsometricDirectSystem Stage sys ω i₀) j x := by
  change (tailHilbertGlobalHomeomorph Stage sys ω i₀).symm
      (gnsStageToHilbertColimit Stage sys ω j.1 x) = _
  rw [← tailHilbertGlobalHomeomorph_stage Stage sys ω i₀ j x]
  exact (tailHilbertGlobalHomeomorph Stage sys ω i₀).symm_apply_apply _

end CStarStateColimit.Native.FilteredGNSCofinalTailTopCatEquivalence
