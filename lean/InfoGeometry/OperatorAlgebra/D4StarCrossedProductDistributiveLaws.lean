import InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Distributive laws for the finite D₄ crossed-product convolution

These are the algebraic laws needed before a ring instance or represented
algebra can be considered.  Unit laws and any normed completion remain
separate obligations.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductDistributiveLaws

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

noncomputable section

theorem crossedProductMul_add_right
    (F K L : D4StarCrossedProduct) :
    crossedProductMul F (K + L) =
      crossedProductMul F K + crossedProductMul F L := by
  funext r v
  simp [crossedProductMul, Finset.sum_add_distrib, mul_add]

theorem crossedProductMul_add_left
    (F K L : D4StarCrossedProduct) :
    crossedProductMul (F + K) L =
      crossedProductMul F L + crossedProductMul K L := by
  funext r v
  simp [crossedProductMul, Finset.sum_add_distrib, add_mul]

theorem crossedProductMul_zero_right
    (F : D4StarCrossedProduct) :
    crossedProductMul F 0 = 0 := by
  funext r v
  simp [crossedProductMul]

theorem crossedProductMul_zero_left
    (F : D4StarCrossedProduct) :
    crossedProductMul 0 F = 0 := by
  funext r v
  simp [crossedProductMul]

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductDistributiveLaws
