import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzWeylUHFBridge

/-!
# Square-Zero Weyl Data and Trace Evaluations

This module packages square-zero equations for the two operators in a
`CuntzWeylSystem`-shaped carrier and derives their linear trace readouts.
Square-zero equations alone do not encode a Klein quadric, Plücker relation,
on-shell factorization, or Cuntz relations.

The base `CuntzWeylSystem` in the imported owner contains reflection data; this
extension adds square-zero hypotheses and does not assert that they follow from
that reflection data.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzWeylNilpotentBoundary

open InfoGeometry.Canonical.CuntzWeylUHFBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## 1. Square-Zero Operator Data

We extend the Weyl reflection data with explicit square-zero hypotheses.
-/

/-- 
The square-zero property of an operator. It has no geometric interpretation
without additional structure connecting this operator to a geometric carrier.
-/
def IsSquareZeroOperator (S : H →L[ℂ] H) : Prop :=
  S ∘L S = 0

/-- 
A Weyl reflection system equipped with square-zero hypotheses on its two
distinguished operators.
-/
structure SquareZeroWeylSystem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] extends CuntzWeylSystem H where
  square_zero_SL : IsSquareZeroOperator S_L
  square_zero_SR : IsSquareZeroOperator S_R

variable (ncws : SquareZeroWeylSystem H)

/-!
## 2. Linear Trace Readouts

Linearity sends each square-zero operator equation to a zero trace.
-/

variable (trace : (H →L[ℂ] H) →ₗ[ℂ] ℂ)

/-- 
The trace of the square of the left distinguished operator is zero by its
square-zero hypothesis.
-/
theorem trace_square_zero_left_sq :
    trace (ncws.S_L ∘L ncws.S_L) = 0 := by
  have h : ncws.S_L ∘L ncws.S_L = 0 := ncws.square_zero_SL
  rw [h]
  exact map_zero trace

/-- 
The corresponding trace statement for the right distinguished operator.
-/
theorem trace_square_zero_right_sq :
    trace (ncws.S_R ∘L ncws.S_R) = 0 := by
  have h : ncws.S_R ∘L ncws.S_R = 0 := ncws.square_zero_SR
  rw [h]
  exact map_zero trace

/-!
## 3. Formal Evaluation Identities

When the boundary chiral generator is intertwined with the grading, 
the trace of the squared combined operator evaluates to zero.
-/

/-- 
The trace of the square of the conjugated left operator equals the trace of
the square of the right operator, by the supplied reflection identity.
-/
theorem reflected_square_trace_identity :
    trace ((ncws.cell.e_plus ∘L ncws.S_L ∘L ncws.cell.e_plus) ∘L 
           (ncws.cell.e_plus ∘L ncws.S_L ∘L ncws.cell.e_plus)) = 0 := by
  have h_SR : ncws.cell.e_plus ∘L ncws.S_L ∘L ncws.cell.e_plus = ncws.S_R := ncws.J_swap
  rw [h_SR]
  exact trace_square_zero_right_sq ncws trace

end InfoGeometry.Canonical.CuntzWeylNilpotentBoundary
