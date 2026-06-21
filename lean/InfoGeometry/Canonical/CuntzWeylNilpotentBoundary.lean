import Mathlib
import InfoGeometry.Canonical.CuntzWeylUHFBridge

/-!
# Cuntz-Weyl Nilpotent Boundary and Trace Evaluations

This module bridges the nilpotency boundary constraints (from the Klein 
quadric on-shell factorization) natively into the Cuntz/Weyl traces, and 
establishes the formal evaluation identities.

Per the Categorical Synthesis Dictionary:
- On-Shell Factorization = The Klein quadric boundary (Q = 0) represented 
  by nilpotent chiral Cuntz generators (S_±² = 0).
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzWeylNilpotentBoundary

open InfoGeometry.Canonical.CuntzWeylUHFBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## 1. Nilpotent Boundary Constraints (Chiral Cuntz Generators)

We define the chiral generators `S_plus` and `S_minus` from the Weyl/Cuntz 
system grading, and enforce the nilpotent Klein quadric constraint natively.
-/

/-- 
The nilpotent boundary constraint explicitly enforces the on-shell 
factorization geometry `S_±² = 0` on a given operator. 
-/
def IsNilpotentBoundary (S : H →L[ℂ] H) : Prop :=
  S ∘L S = 0

/-- 
A Cuntz/Weyl system upgraded with strict chiral nilpotency constraints 
on its primary shift generator (interpreted as the chiral operator).
-/
structure NilpotentCuntzWeylSystem (H : Type*) [NormedAddCommGroup H] 
    [InnerProductSpace ℂ H] [CompleteSpace H] extends CuntzWeylSystem H where
  nilpotent_SL : IsNilpotentBoundary S_L
  nilpotent_SR : IsNilpotentBoundary S_R

variable (ncws : NilpotentCuntzWeylSystem H)

/-!
## 2. Bridging Nilpotency into the Cuntz/Weyl Traces

Since `S_L^2 = 0`, the trace of any operator containing this boundary 
constraint evaluates strictly to zero.
-/

variable (trace : (H →L[ℂ] H) →ₗ[ℂ] ℂ)

/-- 
The trace evaluation of the unperturbed chiral generator squared is 
strictly null due to the Klein quadric boundary constraint.
-/
theorem trace_nilpotent_boundary_SL_sq :
    trace (ncws.S_L ∘L ncws.S_L) = 0 := by
  have h : ncws.S_L ∘L ncws.S_L = 0 := ncws.nilpotent_SL
  rw [h]
  exact map_zero trace

/-- 
The trace evaluation of the dual chiral generator squared is also 
strictly null.
-/
theorem trace_nilpotent_boundary_SR_sq :
    trace (ncws.S_R ∘L ncws.S_R) = 0 := by
  have h : ncws.S_R ∘L ncws.S_R = 0 := ncws.nilpotent_SR
  rw [h]
  exact map_zero trace

/-!
## 3. Formal Evaluation Identities

When the boundary chiral generator is intertwined with the grading, 
the trace of the squared combined operator evaluates to zero.
-/

/-- 
The trace of the Weyl-reflection generator squared evaluates to zero natively, 
because the chiral shift operator itself is nilpotent.
-/
theorem weyl_cuntz_formal_evaluation_identity :
    trace ((ncws.cell.e_plus ∘L ncws.S_L ∘L ncws.cell.e_plus) ∘L 
           (ncws.cell.e_plus ∘L ncws.S_L ∘L ncws.cell.e_plus)) = 0 := by
  have h_SR : ncws.cell.e_plus ∘L ncws.S_L ∘L ncws.cell.e_plus = ncws.S_R := ncws.J_swap
  rw [h_SR]
  exact trace_nilpotent_boundary_SR_sq ncws trace

end InfoGeometry.Canonical.CuntzWeylNilpotentBoundary
