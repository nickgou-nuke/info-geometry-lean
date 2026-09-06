import InfoGeometry.Physics.OperatorZornMatrixAlgebra

/-!
# Operator Zorn quadratic null readout

This file records the algebraic null implication available on the existing
associative operator-valued Zorn carrier.  The readout is a quadratic Peirce
coordinate expression; it is not promoted here to a central Casimir or to a
Majorana-mode predicate without an additional representation contract.
-/

namespace InfoGeometry.Physics.OperatorZornCasimirNullReadout

open InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

def operatorZornQuadraticReadout (M : OperatorZornMatrix A) : A :=
  M.n_plus_op * M.n_minus_op - M.sigma_plus_op * M.sigma_minus_op

theorem operatorZornQuadraticReadout_eq_zero_iff
    (M : OperatorZornMatrix A) :
    operatorZornQuadraticReadout M = 0 ↔
      M.n_plus_op * M.n_minus_op =
        M.sigma_plus_op * M.sigma_minus_op := by
  unfold operatorZornQuadraticReadout
  exact sub_eq_zero

theorem null_readout_boundary_implies_sigma_product_zero
    (M : OperatorZornMatrix A)
    (hnull : operatorZornQuadraticReadout M = 0)
    (hboundary : M.n_plus_op = 0 ∧ M.n_minus_op = 0) :
    M.sigma_plus_op * M.sigma_minus_op = 0 := by
  have hdiag : M.n_plus_op * M.n_minus_op = 0 := by
    rw [hboundary.1, zero_mul]
  have hreadout :
      M.n_plus_op * M.n_minus_op -
          M.sigma_plus_op * M.sigma_minus_op = 0 := by
    exact hnull
  rw [hdiag, zero_sub] at hreadout
  exact neg_eq_zero.mp hreadout

end InfoGeometry.Physics.OperatorZornCasimirNullReadout
