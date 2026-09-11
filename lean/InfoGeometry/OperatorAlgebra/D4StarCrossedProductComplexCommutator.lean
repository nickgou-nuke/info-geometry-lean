import InfoGeometry.OperatorAlgebra.D4StarCrossedProductContinuousLinearRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Complex commutator bridge for the D₄ crossed-product operators

The existing generic spectral-triple owner is real-linear and requires a ring
representation.  The finite D₄ carrier is not yet equipped with a proved
ring instance, so this file records only the complex bounded-operator
commutator that is already meaningful for the property-gated left action.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductComplexCommutator

open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductContinuousLinearRepresentation

noncomputable section

def complexCommutator
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D T : H →L[ℂ] H) : H →L[ℂ] H :=
  D.comp T - T.comp D

@[simp] theorem complexCommutator_self
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D : H →L[ℂ] H) :
    complexCommutator D D = 0 := by
  ext x
  simp [complexCommutator]

theorem complexCommutator_swap
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D T : H →L[ℂ] H) :
    complexCommutator T D = -complexCommutator D T := by
  ext x
  simp [complexCommutator, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc]

def leftRegularCommutator
    (W : ContinuousLeftRegularLinearRepresentation)
    (D : D4StarCrossedProduct →L[ℂ] D4StarCrossedProduct)
    (F : D4StarCrossedProduct) :
    D4StarCrossedProduct →L[ℂ] D4StarCrossedProduct :=
  complexCommutator D (leftRegularContinuousLinearMap W F)

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductComplexCommutator
