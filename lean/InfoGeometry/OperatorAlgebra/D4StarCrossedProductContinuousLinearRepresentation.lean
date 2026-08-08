import InfoGeometry.OperatorAlgebra.D4StarCrossedProductLinearRepresentation

/-!
# Continuous-linear packaging of the finite D₄ crossed-product action

This is the bounded-operator-ready interface: a supplied continuity property
turns each algebraic left-regular linear map into a `ContinuousLinearMap`.
No norm estimate or C*-completion is asserted by this owner.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductContinuousLinearRepresentation

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductLinearRepresentation

noncomputable section

structure ContinuousLeftRegularLinearRepresentation where
  continuous_left : ∀ F : D4StarCrossedProduct,
    Continuous (leftRegularLinearMap F)

variable (W : ContinuousLeftRegularLinearRepresentation)

def leftRegularContinuousLinearMap (F : D4StarCrossedProduct) :
    D4StarCrossedProduct →L[ℂ] D4StarCrossedProduct :=
  ContinuousLinearMap.mk (leftRegularLinearMap F) (W.continuous_left F)

@[simp] theorem leftRegularContinuousLinearMap_apply
    (F K : D4StarCrossedProduct) :
    leftRegularContinuousLinearMap W F K = crossedProductMul F K := rfl

theorem leftRegularContinuousLinearMap_comp
    (F K : D4StarCrossedProduct) :
    leftRegularContinuousLinearMap W (crossedProductMul F K) =
      (leftRegularContinuousLinearMap W F).comp
        (leftRegularContinuousLinearMap W K) := by
  apply ContinuousLinearMap.ext
  intro L
  exact crossedProductMul_assoc F K L

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductContinuousLinearRepresentation
