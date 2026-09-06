import InfoGeometry.OperatorAlgebra.D4StarCrossedProductLeftRegularAction

/-!
# Linear left-regular operators for the finite D₄ crossed-product carrier

The convolution formula is linear in its right coefficient.  This file
packages that fact as a native `ℂ`-linear map.  No norm, boundedness, or
C*-completion is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductLinearRepresentation

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductLeftRegularAction

noncomputable section

def leftRegularLinearMap (F : D4StarCrossedProduct) :
    D4StarCrossedProduct →ₗ[ℂ] D4StarCrossedProduct where
  toFun := leftRegularAction F
  map_add' := by
    intro K L
    funext r v
    simp [leftRegularAction, crossedProductMul, Finset.sum_add_distrib,
      mul_add]
  map_smul' := by
    intro a K
    funext r v
    simp [leftRegularAction, crossedProductMul, Finset.smul_sum,
      smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    rw [Finset.mul_sum]

@[simp] theorem leftRegularLinearMap_apply
    (F K : D4StarCrossedProduct) :
    leftRegularLinearMap F K = crossedProductMul F K := rfl

theorem leftRegularLinearMap_comp
    (F K : D4StarCrossedProduct) :
    leftRegularLinearMap (crossedProductMul F K) =
      (leftRegularLinearMap F).comp (leftRegularLinearMap K) := by
  apply LinearMap.ext
  intro L
  exact crossedProductMul_assoc F K L

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductLinearRepresentation
