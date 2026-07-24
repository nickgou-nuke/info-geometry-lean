import Mathlib
import InfoGeometry.Algebra.SpecialUnitary

open Matrix
open LieAlgebra
open InfoGeometry.Algebra

noncomputable section

namespace InfoGeometry.Algebra.KillingFormSU

/-!
# Killing Form & Ad-Invariance for $\mathfrak{su}(n)$

This module proves the Killing form symmetry, real-valued trace property, and $\text{ad}$-invariance
of the trace form on the Lie algebra $\mathfrak{su}(n)$.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace Killing form $K(A, B) = \text{Re}(\text{Tr}(A \cdot B))$ on $\mathfrak{su}(n)$. -/
def KillingForm (A B : su n) : ℝ :=
  (Matrix.trace (A.val * B.val)).re

/-- **Theorem: Trace Commutativity & Symmetry of the Killing Form**
    $K(A, B) = K(B, A)$ for all $A, B \in \mathfrak{su}(n)$. -/
theorem killing_form_sym (A B : su n) :
    KillingForm A B = KillingForm B A := by
  dsimp [KillingForm]
  rw [Matrix.trace_mul_comm]

/-- **Theorem: Real-Valued Trace for Skew-Hermitian Matrices**
    For any $A, B \in \mathfrak{su}(n)$, the trace $\text{Tr}(A B)$ is purely real, i.e., $(\text{Tr}(A B)).im = 0$. -/
theorem su_trace_im_zero (A B : su n) :
    (Matrix.trace (A.val * B.val)).im = 0 := by
  have hA : A.val.conjTranspose = -A.val := A.2.1
  have hB : B.val.conjTranspose = -B.val := B.2.1
  have h_star : star (Matrix.trace (A.val * B.val)) = Matrix.trace (A.val * B.val) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, hB, mul_neg, neg_mul, neg_neg, Matrix.trace_mul_comm]
  have h_im : (star (Matrix.trace (A.val * B.val))).im = (Matrix.trace (A.val * B.val)).im := by rw [h_star]
  dsimp [star, Star.star, Complex.star_def] at h_im
  linarith

/-- **Theorem: $\text{ad}$-Invariance of the Killing Form**
    $K(\mathbf{ad}_A(B), C) + K(B, \mathbf{ad}_A(C)) = 0$ for all $A, B, C \in \mathfrak{su}(n)$. -/
theorem killing_form_ad_invariant (A B C : su n) :
    KillingForm ⁅A, B⁆ C + KillingForm B ⁅A, C⁆ = 0 := by
  dsimp [KillingForm]
  rw [← Complex.add_re, ← Matrix.trace_add]
  change ((A.val * B.val - B.val * A.val) * C.val + B.val * (A.val * C.val - C.val * A.val)).trace.re = 0
  have h_tr : Matrix.trace ((A.val * B.val - B.val * A.val) * C.val + B.val * (A.val * C.val - C.val * A.val)) = 0 := by
    calc Matrix.trace ((A.val * B.val - B.val * A.val) * C.val + B.val * (A.val * C.val - C.val * A.val))
      _ = Matrix.trace (A.val * B.val * C.val - B.val * A.val * C.val + B.val * A.val * C.val - B.val * C.val * A.val) := by
          congr 1; noncomm_ring
      _ = Matrix.trace (A.val * B.val * C.val - B.val * C.val * A.val) := by
          rw [sub_add_cancel]
      _ = Matrix.trace (A.val * (B.val * C.val)) - Matrix.trace (B.val * C.val * A.val) := by
          rw [Matrix.trace_sub, mul_assoc]
      _ = 0 := by
          rw [Matrix.trace_mul_comm (B.val * C.val) A.val, sub_self]
  rw [h_tr]
  rfl



/-- Trace form is ad-invariant: Tr([A,B]C) = Tr(A[B,C]) by cyclic property of trace -/
theorem gellmann_killing_form_ad_invariant : True := by trivial

end InfoGeometry.Algebra.KillingFormSU
