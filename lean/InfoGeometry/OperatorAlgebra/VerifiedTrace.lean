/-
InfoGeometry/OperatorAlgebra/VerifiedTrace.lean

The individuation of finite matrix trace.

This module kills the shadow:

  is_trace_invariant : Prop

For finite matrices the trace is the sum of diagonal entries.  Its cyclicity
implies similarity invariance:

  tr(U A U^{-1}) = tr(A)

whenever `U` has a two-sided inverse.

No vacuous trace-invariance certificate is used.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.IndividuatedCasimir
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.VerifiedTrace

open InfoGeometry.OperatorAlgebra.IndividuatedCasimir
open scoped Matrix BigOperators

/-! ## 1. Constructive cyclicity and invariance -/

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/--
Finite matrix trace is invariant under conjugation by a two-sided inverse.

The two-sided inverse is part of the public theorem boundary.  The proof uses
trace cyclicity and the left inverse law after cycling the final factor.
-/
theorem matrix_trace_conjugation_invariant
    (A : Matrix n n R)
    (U U_inv : Matrix n n R)
    (_h_right : U * U_inv = 1)
    (h_left : U_inv * U = 1) :
    Matrix.trace (U * A * U_inv) = Matrix.trace A := by
  calc
    Matrix.trace (U * A * U_inv)
        = Matrix.trace ((U * A) * U_inv) := by
            rw [mul_assoc]
    _ = Matrix.trace (U_inv * (U * A)) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((U_inv * U) * A) := by
            rw [← mul_assoc]
    _ = Matrix.trace (1 * A) := by
            rw [h_left]
    _ = Matrix.trace A := by
            simp

/--
Trace invariance for an `InvertibleTransport` of a finite matrix algebra.
-/
theorem matrix_trace_invariant_under_transport
    (A : Matrix n n R)
    (U : InvertibleTransport (Matrix n n R)) :
    Matrix.trace (U.conjugate A) = Matrix.trace A := by
  dsimp [InvertibleTransport.conjugate]
  exact matrix_trace_conjugation_invariant A U.val U.inv U.val_inv U.inv_val

/-! ## 2. Verified trace readout -/

set_option linter.dupNamespace false

/--
A verified trace is an operator-to-scalar map with a proved conjugation
invariance law.
-/
structure VerifiedTrace
    (Op Scalar : Type*) [Monoid Op] where
  tr : Op → Scalar
  invariant :
    ∀ (A : Op) (U : InvertibleTransport Op),
      tr (U.conjugate A) = tr A

namespace VerifiedTrace

variable {Op Scalar : Type*} [Monoid Op]
variable (T : VerifiedTrace Op Scalar)

/--
Re-export trace invariance.
-/
theorem conjugation_invariant
    (A : Op)
    (U : InvertibleTransport Op) :
    T.tr (U.conjugate A) = T.tr A :=
  T.invariant A U

end VerifiedTrace

/--
Construction of a verified trace for finite matrix algebras over a commutative
ring.
-/
def matrixVerifiedTrace
    (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R] :
    VerifiedTrace (Matrix n n R) R where
  tr := Matrix.trace
  invariant := by
    intro A U
    exact matrix_trace_invariant_under_transport A U

/-! ## 3. Real finite matrix specialization -/

/--
Verified real trace on `Fin n` matrices.
-/
def realMatrixVerifiedTrace
    (n : ℕ) :
    VerifiedTrace (Matrix (Fin n) (Fin n) ℝ) ℝ :=
  matrixVerifiedTrace (Fin n) ℝ

/--
Real finite matrix trace is invariant under invertible conjugation.
-/
theorem real_matrix_trace_invariant_under_transport
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (U : InvertibleTransport (Matrix (Fin n) (Fin n) ℝ)) :
    Matrix.trace (U.conjugate A) = Matrix.trace A :=
  matrix_trace_invariant_under_transport A U

/-! ## 4. Owner target discharged constructively -/

/--
Owner target for raw finite trace conjugation invariance.
-/
@[owner_target_tag]
def FiniteTraceConjugationOwnerTarget : Prop :=
  ∀ (n : Type*) [Fintype n] [DecidableEq n],
  ∀ (R : Type*) [CommRing R],
  ∀ (A U U_inv : Matrix n n R),
    U * U_inv = 1 →
    U_inv * U = 1 →
      Matrix.trace (U * A * U_inv) = Matrix.trace A

/--
Constructive proof of raw finite trace conjugation invariance.
-/
theorem finiteTraceConjugationOwnerTarget :
    FiniteTraceConjugationOwnerTarget := by
  intro n _ _ R _ A U U_inv h_right h_left
  exact matrix_trace_conjugation_invariant A U U_inv h_right h_left

/--
Owner target for finite matrix trace conjugation invariance through
`InvertibleTransport`.
-/
@[owner_target_tag]
def FiniteMatrixTraceInvariantOwnerTarget : Prop :=
  ∀ (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R],
  ∀ (A : Matrix n n R),
  ∀ U : InvertibleTransport (Matrix n n R),
    Matrix.trace (U.conjugate A) = Matrix.trace A

/--
Constructive proof of finite matrix trace conjugation invariance.
-/
theorem finiteMatrixTraceInvariantOwnerTarget :
    FiniteMatrixTraceInvariantOwnerTarget := by
  intro n R _ _ _ A U
  exact matrix_trace_invariant_under_transport A U

end InfoGeometry.OperatorAlgebra.VerifiedTrace
