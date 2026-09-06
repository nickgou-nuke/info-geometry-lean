import InfoGeometry.Canonical.PauliJungTrialityD4Synthesis
import InfoGeometry.Canonical.D4StarObservableDirectLimitAction
import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution
import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductCoefficientLimit

/-!
# D₄-star coefficient-limit crossed-product carrier

This file specializes the generic coefficient-limit crossed-product packet to
the constant D₄ observable system.  It does not claim a crossed-product
completion or any new colimit theorem; it only exposes the D₄ indexing data
at the coefficient-limit layer.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductCoefficientLimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit
open InfoGeometry.Canonical
open InfoGeometry.Canonical.D4StarObservableDirectLimitAction
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution
open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductCoefficientLimit

/-- The D₄ specialization of the generic coefficient-limit crossed-product carrier. -/
abbrev D4StarCoefficientLimitCrossedProduct :=
  CoefficientLimitCrossedProduct ℕ (Equiv.Perm ColorChannel)
    ObservableStage constantObservableSystem observableAction

/-- The D₄ coefficient-limit crossed-product carrier. -/
def d4StarCoefficientLimitCrossedProduct :
    D4StarCoefficientLimitCrossedProduct :=
  coefficientLimitCrossedProduct ℕ (Equiv.Perm ColorChannel)
    ObservableStage constantObservableSystem observableAction

@[simp] theorem d4StarCoefficientLimitCrossedProduct_mul
    (F K : Equiv.Perm ColorChannel → limitCoefficient ObservableStage
      constantObservableSystem) :
    (d4StarCoefficientLimitCrossedProduct).mul F K =
      limitConvolution ℕ (Equiv.Perm ColorChannel) ObservableStage
        constantObservableSystem observableAction F K := rfl

@[simp] theorem d4StarCoefficientLimitCrossedProduct_one :
    (d4StarCoefficientLimitCrossedProduct).one =
      limitConvolutionOne ℕ (Equiv.Perm ColorChannel) ObservableStage
        constantObservableSystem := rfl

@[simp] theorem d4StarCoefficientLimitCrossedProduct_star
    (F : Equiv.Perm ColorChannel → limitCoefficient ObservableStage
      constantObservableSystem) :
    (d4StarCoefficientLimitCrossedProduct).star F =
      limitConvolutionStar ℕ (Equiv.Perm ColorChannel) ObservableStage
        constantObservableSystem observableAction F := rfl

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductCoefficientLimit
