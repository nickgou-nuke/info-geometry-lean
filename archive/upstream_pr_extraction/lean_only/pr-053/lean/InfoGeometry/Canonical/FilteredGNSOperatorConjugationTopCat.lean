import InfoGeometry.Canonical.FilteredGNSGlobalStageRepresentationTransport
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# TopCat packaging of GNS operator conjugation

The global stage representation transport already gives a homeomorphism of
bounded-operator spaces.  Here it is exposed as a categorical `TopCat` iso;
the underlying operator conjugation remains the existing native
`ContinuousAlgEquiv`.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSOperatorConjugationTopCat

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentationTransport
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSTailStarRepresentation
open CStarStateColimit.Native.FilteredGNSCofinalTail
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

local notation "E" => TailGNSStage Stage sys ω
local notation "S" => tailGNSIsometricDirectSystem Stage sys ω

def operatorConjugationTopCatMap (i₀ : I) :
    TopCat.of
        (HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
          HilbertDirectLimit (E i₀) (S i₀)) ⟶
      TopCat.of
        (GNSHilbertColimit Stage sys ω →L[ℂ]
          GNSHilbertColimit Stage sys ω) :=
  TopCat.ofHom
    { toFun := globalStageOperatorConjugationHomeomorph Stage sys ω i₀
      continuous_toFun :=
        globalStageOperatorConjugationHomeomorph_continuous Stage sys ω i₀ }

def operatorConjugationInverseTopCatMap (i₀ : I) :
    TopCat.of
        (GNSHilbertColimit Stage sys ω →L[ℂ]
          GNSHilbertColimit Stage sys ω) ⟶
      TopCat.of
        (HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
          HilbertDirectLimit (E i₀) (S i₀)) :=
  TopCat.ofHom
    { toFun := (globalStageOperatorConjugationHomeomorph Stage sys ω i₀).symm
      continuous_toFun :=
        globalStageOperatorConjugationHomeomorph_continuous_inv
          Stage sys ω i₀ }

theorem operatorConjugationInverse_comp_operatorConjugation (i₀ : I) :
    operatorConjugationTopCatMap Stage sys ω i₀ ≫
        operatorConjugationInverseTopCatMap Stage sys ω i₀ = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro T
  change
    (globalStageOperatorConjugationHomeomorph Stage sys ω i₀).symm
        (globalStageOperatorConjugationHomeomorph Stage sys ω i₀ T) = T
  exact (globalStageOperatorConjugationHomeomorph Stage sys ω i₀).left_inv T

theorem operatorConjugation_comp_operatorConjugationInverse (i₀ : I) :
    operatorConjugationInverseTopCatMap Stage sys ω i₀ ≫
        operatorConjugationTopCatMap Stage sys ω i₀ = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro T
  change
    globalStageOperatorConjugationHomeomorph Stage sys ω i₀
        ((globalStageOperatorConjugationHomeomorph Stage sys ω i₀).symm T) = T
  exact (globalStageOperatorConjugationHomeomorph Stage sys ω i₀).right_inv T

def operatorConjugationTopCatIso (i₀ : I) :
    TopCat.of
        (HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
          HilbertDirectLimit (E i₀) (S i₀)) ≅
      TopCat.of
        (GNSHilbertColimit Stage sys ω →L[ℂ]
          GNSHilbertColimit Stage sys ω) where
  hom := operatorConjugationTopCatMap Stage sys ω i₀
  inv := operatorConjugationInverseTopCatMap Stage sys ω i₀
  hom_inv_id := operatorConjugationInverse_comp_operatorConjugation Stage sys ω i₀
  inv_hom_id := operatorConjugation_comp_operatorConjugationInverse Stage sys ω i₀

@[simp] theorem operatorConjugationTopCatMap_apply (i₀ : I)
    (T : HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
      HilbertDirectLimit (E i₀) (S i₀)) :
    operatorConjugationTopCatMap Stage sys ω i₀ T =
      globalStageOperatorConjugationHomeomorph Stage sys ω i₀ T :=
  rfl

end CStarStateColimit.Native.FilteredGNSOperatorConjugationTopCat
