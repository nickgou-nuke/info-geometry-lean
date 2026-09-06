import InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarLaws
import InfoGeometry.OperatorAlgebra.D4StarCrossedProductAlgebraicSurface

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductNonUnitalStarSurface

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductDistributiveLaws
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductStarLaws

noncomputable section

/-!
# Native algebraic structure for the finite convolution carrier

The finite crossed-product carrier already has kernel-checked associativity,
distributivity, zero, unit, and involution laws.  This owner installs only the
corresponding non-unital algebraic structures.  It deliberately does not
assert a norm, C*-identity, or completion.
-/

instance : NonUnitalNonAssocSemiring D4StarCrossedProduct where
  left_distrib := crossedProductMul_add_right
  right_distrib := crossedProductMul_add_left
  zero_mul := crossedProductMul_zero_left
  mul_zero := crossedProductMul_zero_right

instance : NonUnitalNonAssocRing D4StarCrossedProduct where
  left_distrib := crossedProductMul_add_right
  right_distrib := crossedProductMul_add_left
  zero_mul := crossedProductMul_zero_left
  mul_zero := crossedProductMul_zero_right

instance : Star D4StarCrossedProduct :=
  ⟨crossedProductStar⟩

instance : StarRing D4StarCrossedProduct where
  star_involutive := by
    intro F
    exact crossedProductStar_star F
  star_mul := by
    intro F K
    exact crossedProductStar_mul F K
  star_add := by
    intro F K
    funext r
    change colorPullback r (star (F r.symm + K r.symm)) =
      colorPullback r (star (F r.symm)) +
        colorPullback r (star (K r.symm))
    rw [star_add, map_add]

@[simp] theorem star_apply
    (F : D4StarCrossedProduct) :
    star F = crossedProductStar F :=
  rfl

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductNonUnitalStarSurface
