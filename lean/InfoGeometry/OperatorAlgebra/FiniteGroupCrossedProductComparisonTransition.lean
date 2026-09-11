import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductComparisonPacket
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTransitionLaws

/-!
# Compatibility of crossed-product comparison with stage transitions

These lemmas combine the equivariant transition laws with the coefficientwise
comparison packet.  They are the cocone-level coherence statements needed
before constructing any universal comparison morphism.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductComparisonTransition

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductComparisonPacket
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTransitionLaws

noncomputable section

universe u

variable {I G : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [Group G] [Fintype G] [DecidableEq G]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (A : CompatibleStarGroupAction I G Stage sys)

structure CoefficientwiseComparisonCocone where
  map : ∀ i : I, stageCrossedProduct I G Stage i →
    (G → limitCoefficient Stage sys)
  map_transition : ∀ {i j : I} (hij : i ≤ j)
    (F : stageCrossedProduct I G Stage i),
    map j (stageCrossedProductTransition Stage sys hij F) = map i F
  map_convolution : ∀ (i : I)
    (F K : stageCrossedProduct I G Stage i),
    map i (stageConvolution I G Stage sys A i F K) =
      limitConvolution I G Stage sys A (map i F) (map i K)
  map_star : ∀ (i : I) (F : stageCrossedProduct I G Stage i),
    map i (stageConvolutionStar I G Stage sys A i F) =
      limitConvolutionStar I G Stage sys A (map i F)

noncomputable def coefficientwiseComparisonCocone :
    CoefficientwiseComparisonCocone Stage sys A where
  map := coefficientwiseComparison I G Stage sys
  map_transition := by
    intro i j hij F
    simpa [coefficientwiseComparisonFamily, stageCrossedProductTransition] using
      (coefficientwiseComparisonFamily_transition Stage sys hij F).symm
  map_convolution := by
    intro i F K
    exact coefficientwiseComparisonPacket_convolution Stage sys A i F K
  map_star := by
    intro i F
    exact coefficientwiseComparisonPacket_star Stage sys A i F

theorem coefficientwiseComparisonCocone_transition
    (Cocone : CoefficientwiseComparisonCocone Stage sys A)
    {i j : I} (hij : i ≤ j)
    (F : stageCrossedProduct I G Stage i) :
    Cocone.map j (stageCrossedProductTransition Stage sys hij F) =
      Cocone.map i F :=
  Cocone.map_transition hij F

@[simp] theorem coefficientwiseComparisonCocone_apply
    (i : I) (F : stageCrossedProduct I G Stage i) (g : G) :
    (coefficientwiseComparisonCocone Stage sys A).map i F g =
      algebraicStarDirectLimitOf Stage sys i (F g) := by
  rfl

theorem coefficientwiseComparisonFamily_map_unique
    (m : ∀ i : I, stageCrossedProduct I G Stage i →
      (G → limitCoefficient Stage sys))
    (hm : ∀ (i : I) (F : stageCrossedProduct I G Stage i) (g : G),
      m i F g = algebraicStarDirectLimitOf Stage sys i (F g)) :
    m = (coefficientwiseComparisonCocone Stage sys A).map := by
  funext i F g
  exact (hm i F g).trans
    (coefficientwiseComparisonCocone_apply Stage sys A i F g).symm

theorem comparison_transition_convolution
    {i j : I} (hij : i ≤ j)
    (F K : stageCrossedProduct I G Stage i) :
    coefficientwiseComparison I G Stage sys j
        (stageCrossedProductTransition Stage sys hij
          (stageConvolution I G Stage sys A i F K)) =
      limitConvolution I G Stage sys A
        (coefficientwiseComparison I G Stage sys i F)
        (coefficientwiseComparison I G Stage sys i K) := by
  rw [stageCrossedProductTransition_convolution Stage sys A hij F K]
  rw [coefficientwiseComparisonPacket_convolution Stage sys A j
    (stageCrossedProductTransition Stage sys hij F)
    (stageCrossedProductTransition Stage sys hij K)]
  have hF :
      coefficientwiseComparison I G Stage sys j
          (stageCrossedProductTransition Stage sys hij F) =
        coefficientwiseComparison I G Stage sys i F := by
    simpa [coefficientwiseComparisonFamily, stageCrossedProductTransition] using
      (coefficientwiseComparisonFamily_transition Stage sys hij F).symm
  have hK :
      coefficientwiseComparison I G Stage sys j
          (stageCrossedProductTransition Stage sys hij K) =
        coefficientwiseComparison I G Stage sys i K := by
    simpa [coefficientwiseComparisonFamily, stageCrossedProductTransition] using
      (coefficientwiseComparisonFamily_transition Stage sys hij K).symm
  rw [hF, hK]

theorem comparison_transition_star
    {i j : I} (hij : i ≤ j)
    (F : stageCrossedProduct I G Stage i) :
    coefficientwiseComparison I G Stage sys j
        (stageCrossedProductTransition Stage sys hij
          (stageConvolutionStar I G Stage sys A i F)) =
      limitConvolutionStar I G Stage sys A
        (coefficientwiseComparison I G Stage sys i F) := by
  rw [stageCrossedProductTransition_star Stage sys A hij F]
  rw [coefficientwiseComparisonPacket_star Stage sys A j
    (stageCrossedProductTransition Stage sys hij F)]
  have hF :
      coefficientwiseComparison I G Stage sys j
          (stageCrossedProductTransition Stage sys hij F) =
        coefficientwiseComparison I G Stage sys i F := by
    simpa [coefficientwiseComparisonFamily, stageCrossedProductTransition] using
      (coefficientwiseComparisonFamily_transition Stage sys hij F).symm
  rw [hF]

end

end InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductComparisonTransition
