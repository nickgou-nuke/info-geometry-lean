import InfoGeometry.OperatorAlgebra.D4StarCrossedProductLinearRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical finite-dimensional continuity for D₄ crossed-product operators

The finite coefficient carrier has a native finite-dimensional complex-vector
space instance.  Consequently Mathlib supplies continuity of every linear
left-regular operator; no extra continuity ax!om is needed in this finite
stage.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductFiniteDimensionalContinuity

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductLinearRepresentation

noncomputable section

def canonicalLeftRegularContinuousLinearMap
    (F : D4StarCrossedProduct) :
    D4StarCrossedProduct →L[ℂ] D4StarCrossedProduct :=
  ContinuousLinearMap.mk (leftRegularLinearMap F)
    (LinearMap.continuous_of_finiteDimensional (leftRegularLinearMap F))

@[simp] theorem canonicalLeftRegularContinuousLinearMap_apply
    (F K : D4StarCrossedProduct) :
    canonicalLeftRegularContinuousLinearMap F K = crossedProductMul F K := rfl

theorem canonicalLeftRegularContinuousLinearMap_comp
    (F K : D4StarCrossedProduct) :
    canonicalLeftRegularContinuousLinearMap (crossedProductMul F K) =
      (canonicalLeftRegularContinuousLinearMap F).comp
        (canonicalLeftRegularContinuousLinearMap K) := by
  apply ContinuousLinearMap.ext
  intro L
  exact crossedProductMul_assoc F K L

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductFiniteDimensionalContinuity
