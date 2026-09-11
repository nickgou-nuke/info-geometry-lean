import InfoGeometry.OperatorAlgebra.D4StarCrossedProductCoefficientLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductComparisonTransition

/-!
# D₄ specialization of the coefficient-limit comparison packet

This file only specializes the generic coefficientwise comparison cocone to
the native constant D₄ observable system.  It does not assert a universal
crossed-product/direct-limit isomorphism or install an algebra structure on a
function carrier.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductCoefficientLimitComparison

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit
open InfoGeometry.Canonical
open InfoGeometry.Canonical.D4StarObservableDirectLimitAction
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductComparisonTransition
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductTransitionLaws

noncomputable section

abbrev D4StarCoefficientComparisonCocone :=
  CoefficientwiseComparisonCocone
    ObservableStage constantObservableSystem observableAction

noncomputable def d4StarCoefficientComparisonCocone :
  D4StarCoefficientComparisonCocone :=
  coefficientwiseComparisonCocone
    ObservableStage constantObservableSystem observableAction

@[simp] theorem d4StarCoefficientComparisonCocone_apply
    (i : ℕ) (F : stageCrossedProduct ℕ (Equiv.Perm ColorChannel)
      ObservableStage i) (g : Equiv.Perm ColorChannel) :
    d4StarCoefficientComparisonCocone.map i F g =
      algebraicStarDirectLimitOf ObservableStage
        constantObservableSystem i (F g) := by
  exact coefficientwiseComparisonCocone_apply
    ObservableStage constantObservableSystem observableAction i F g

theorem d4StarCoefficientComparisonCocone_transition
    {i j : ℕ} (hij : i ≤ j)
    (F : stageCrossedProduct ℕ (Equiv.Perm ColorChannel)
      ObservableStage i) :
    d4StarCoefficientComparisonCocone.map j
        (stageCrossedProductTransition ObservableStage
          constantObservableSystem hij F) =
      d4StarCoefficientComparisonCocone.map i F := by
  exact coefficientwiseComparisonCocone_transition
    ObservableStage constantObservableSystem observableAction
    d4StarCoefficientComparisonCocone hij F

theorem d4StarCoefficientComparison_transition_convolution
    {i j : ℕ} (hij : i ≤ j)
    (F K : stageCrossedProduct ℕ (Equiv.Perm ColorChannel)
      ObservableStage i) :
    coefficientwiseComparison ℕ (Equiv.Perm ColorChannel)
        ObservableStage constantObservableSystem j
        (stageCrossedProductTransition ObservableStage
          constantObservableSystem hij
          (stageConvolution ℕ (Equiv.Perm ColorChannel)
            ObservableStage constantObservableSystem observableAction i F K)) =
      limitConvolution ℕ (Equiv.Perm ColorChannel) ObservableStage
        constantObservableSystem observableAction
        (coefficientwiseComparison ℕ (Equiv.Perm ColorChannel)
          ObservableStage constantObservableSystem i F)
        (coefficientwiseComparison ℕ (Equiv.Perm ColorChannel)
          ObservableStage constantObservableSystem i K) := by
  exact comparison_transition_convolution
    ObservableStage constantObservableSystem observableAction hij F K

theorem d4StarCoefficientComparison_transition_star
    {i j : ℕ} (hij : i ≤ j)
    (F : stageCrossedProduct ℕ (Equiv.Perm ColorChannel)
      ObservableStage i) :
    coefficientwiseComparison ℕ (Equiv.Perm ColorChannel)
        ObservableStage constantObservableSystem j
        (stageCrossedProductTransition ObservableStage
          constantObservableSystem hij
          (stageConvolutionStar ℕ (Equiv.Perm ColorChannel)
            ObservableStage constantObservableSystem observableAction i F)) =
      limitConvolutionStar ℕ (Equiv.Perm ColorChannel) ObservableStage
        constantObservableSystem observableAction
        (coefficientwiseComparison ℕ (Equiv.Perm ColorChannel)
          ObservableStage constantObservableSystem i F) := by
  exact comparison_transition_star
    ObservableStage constantObservableSystem observableAction hij F

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductCoefficientLimitComparison
