import InfoGeometry.Canonical.FilteredGNSTailRepresentation
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological arrows for filtered GNS tail representations

The tail representation owner already supplies continuous-linear operators and
their exact intertwining law.  This file exposes those maps as `TopCat`
morphisms and records the corresponding commutative square without introducing
coordinates or a new completion.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTailRepresentationTopology

set_option linter.unusedSectionVars false

open CategoryTheory
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTailRepresentation
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

def tailGNSTransitionTopCatHom
    {i₀ : I} {j k : UpperIndex i₀} (hjk : j ≤ k) :
    TopCat.of (TailGNSStage Stage sys ω i₀ j) ⟶
      TopCat.of (TailGNSStage Stage sys ω i₀ k) :=
  TopCat.ofHom
    { toFun := (tailGNSIsometricDirectSystem Stage sys ω i₀).map hjk
      continuous_toFun :=
        ((tailGNSIsometricDirectSystem Stage sys ω i₀).map hjk).continuous }

@[simp] theorem tailGNSTransitionTopCatHom_apply
    {i₀ : I} {j k : UpperIndex i₀} (hjk : j ≤ k)
    (x : TailGNSStage Stage sys ω i₀ j) :
    tailGNSTransitionTopCatHom Stage sys ω hjk x =
      (tailGNSIsometricDirectSystem Stage sys ω i₀).map hjk x :=
  rfl

def tailGNSOperatorTopCatHom
    {i₀ : I} (a : Stage i₀) (j : UpperIndex i₀) :
    TopCat.of (TailGNSStage Stage sys ω i₀ j) ⟶
      TopCat.of (TailGNSStage Stage sys ω i₀ j) :=
  TopCat.ofHom
    { toFun := tailGNSOperator Stage sys ω a j
      continuous_toFun :=
        (tailGNSOperator Stage sys ω a j).continuous }

@[simp] theorem tailGNSOperatorTopCatHom_apply
    {i₀ : I} (a : Stage i₀) (j : UpperIndex i₀)
    (x : TailGNSStage Stage sys ω i₀ j) :
    tailGNSOperatorTopCatHom Stage sys ω a j x =
      tailGNSOperator Stage sys ω a j x :=
  rfl

theorem tailGNSOperatorTopCatHom_intertwines
    {i₀ : I} (a : Stage i₀)
    {j k : UpperIndex i₀} (hjk : j ≤ k) :
    tailGNSTransitionTopCatHom Stage sys ω hjk ≫
        tailGNSOperatorTopCatHom Stage sys ω a k =
      tailGNSOperatorTopCatHom Stage sys ω a j ≫
        tailGNSTransitionTopCatHom Stage sys ω hjk := by
  apply TopCat.hom_ext
  ext x
  simpa [tailGNSTransitionTopCatHom, tailGNSOperatorTopCatHom,
    TopCat.comp_app] using
    (tailGNSOperator_intertwines Stage sys ω a hjk x).symm

def tailCompletedRepresentationTopCatHom
    {i₀ : I} (a : Stage i₀) :
    TopCat.of
        (HilbertDirectLimit
          (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀)) ⟶
      TopCat.of
        (HilbertDirectLimit
          (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀)) :=
  TopCat.ofHom
    { toFun := tailCompletedRepresentation Stage sys ω a
      continuous_toFun :=
        (tailCompletedRepresentation Stage sys ω a).continuous }

@[simp] theorem tailCompletedRepresentationTopCatHom_apply
    {i₀ : I} (a : Stage i₀)
    (x : HilbertDirectLimit
      (TailGNSStage Stage sys ω i₀)
      (tailGNSIsometricDirectSystem Stage sys ω i₀)) :
    tailCompletedRepresentationTopCatHom Stage sys ω a x =
      tailCompletedRepresentation Stage sys ω a x :=
  rfl

end CStarStateColimit.Native.FilteredGNSTailRepresentationTopology
