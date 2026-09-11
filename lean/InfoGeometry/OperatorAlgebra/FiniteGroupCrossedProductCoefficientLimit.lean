import InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductComparisonPacket
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Coefficient-limit crossed-product carrier

This file packages the descended convolution, unit, and involution on the
native star-algebra direct limit.  The operations live in an explicit local
carrier structure; no global algebra instance is installed on a function
type, and no universal crossed-product/direct-limit isomorphism is claimed.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductCoefficientLimit

open InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductDirectLimitConvolution
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit

noncomputable section

universe u

variable {I G : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [Group G] [Fintype G] [DecidableEq G]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (A : CompatibleStarGroupAction I G Stage sys)

structure CoefficientLimitCrossedProduct
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] [Fintype G] [DecidableEq G]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) where
  carrier : Type u
  mul : carrier → carrier → carrier
  one : carrier
  star : carrier → carrier
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x
  star_star : ∀ x, star (star x) = x
  star_mul : ∀ x y, star (mul x y) = mul (star y) (star x)

def coefficientLimitCrossedProduct
    (I G : Type u) [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [Group G] [Fintype G] [DecidableEq G]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (A : CompatibleStarGroupAction I G Stage sys) :
    CoefficientLimitCrossedProduct I G Stage sys A where
  carrier := G → limitCoefficient Stage sys
  mul := limitConvolution I G Stage sys A
  one := limitConvolutionOne I G Stage sys
  star := limitConvolutionStar I G Stage sys A
  mul_assoc := by
    intro F K L
    exact limitConvolution_assoc (Stage := Stage) (sys := sys) (A := A) F K L
  one_mul := by
    intro F
    exact limitConvolution_one_left (Stage := Stage) (sys := sys) (A := A) F
  mul_one := by
    intro F
    exact limitConvolution_one_right (Stage := Stage) (sys := sys) (A := A) F
  star_star := by
    intro F
    exact limitConvolutionStar_star (Stage := Stage) (sys := sys) (A := A) F
  star_mul := by
    intro F K
    exact limitConvolutionStar_mul (Stage := Stage) (sys := sys) (A := A) F K

@[simp] theorem coefficientLimitCrossedProduct_mul
    (F K : G → limitCoefficient Stage sys) :
    (coefficientLimitCrossedProduct I G Stage sys A).mul F K =
      limitConvolution I G Stage sys A F K := rfl

@[simp] theorem coefficientLimitCrossedProduct_one :
    (coefficientLimitCrossedProduct I G Stage sys A).one =
      limitConvolutionOne I G Stage sys := rfl

@[simp] theorem coefficientLimitCrossedProduct_star
    (F : G → limitCoefficient Stage sys) :
    (coefficientLimitCrossedProduct I G Stage sys A).star F =
      limitConvolutionStar I G Stage sys A F := rfl

end

end InfoGeometry.OperatorAlgebra.FiniteGroupCrossedProductCoefficientLimit
