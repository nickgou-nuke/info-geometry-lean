/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.IndividuatedCasimir

/-!
# The Individuation of Finite Matrix Trace and Cyclic Ring Traces

For finite matrices or any non-commutative ring `[Ring B]` equipped with a cyclic
additive trace `τ : B →+ M`, cyclicity implies similarity invariance:
`τ(U * A * U⁻¹) = τ(A)` whenever `U_inv * U = 1`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.VerifiedTrace

open InfoGeometry.OperatorAlgebra.IndividuatedCasimir
open InfoGeometry.Algebra.FiniteSpin
open scoped Matrix BigOperators

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

/-! ## 0. Non-Commutative Ring Cyclic Trace Invariance -/

/-- Over any non-commutative ring `[Ring B]`, a cyclic additive trace `τ : B →+ M`
(`∀ x y, τ (x * y) = τ (y * x)`) is invariant under conjugation by any left-invertible
pair `(U, U_inv)` (`U_inv * U = 1`). -/
theorem cyclic_trace_conjugation_invariant_ring {B M : Type*} [Ring B] [AddCommMonoid M]
    (τ : B →+ M) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (A U U_inv : B) (h_left : U_inv * U = 1) :
    τ (U * A * U_inv) = τ A := by
  calc
    τ (U * A * U_inv) = τ ((U * A) * U_inv) := rfl
    _ = τ (U_inv * (U * A)) := h_cyc (U * A) U_inv
    _ = τ ((U_inv * U) * A) := by rw [mul_assoc]
    _ = τ A := by rw [h_left, one_mul]

/-- Over any non-commutative ring `[Ring B]`, a cyclic trace `τ : B → M` is invariant
under every `InvertibleTransport B`. -/
theorem cyclic_trace_invariant_under_transport_ring {B M : Type*} [Ring B]
    (τ : B → M) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (A : B) (U : InvertibleTransport B) :
    τ (U.conjugate A) = τ A := by
  dsimp [InvertibleTransport.conjugate]
  calc
    τ ((U : B) * A * (↑U⁻¹ : B)) = τ (↑U⁻¹ * ((U : B) * A)) := h_cyc ((U : B) * A) (↑U⁻¹ : B)
    _ = τ ((↑U⁻¹ * (U : B)) * A) := by rw [mul_assoc]
    _ = τ A := by rw [Units.inv_mul U, one_mul]

/-! ## 1. Constructive cyclicity and invariance -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Over a non-commutative ring `[Ring R]`, conjugation of `A : Matrix n n R` by a
left-invertible pair `(U, U_inv)` (`U_inv * U = 1`) shifts `Matrix.trace` by the
exact matrix commutator trace `Matrix.trace ((U * A) * U_inv - U_inv * (U * A))`. -/
theorem matrix_trace_conjugation_defect {R : Type*} [Ring R]
    (A U U_inv : Matrix n n R)
    (h_left : U_inv * U = 1) :
    Matrix.trace (U * A * U_inv) - Matrix.trace A =
      Matrix.trace ((U * A) * U_inv - U_inv * (U * A)) := by
  have hA : Matrix.trace A = Matrix.trace (U_inv * (U * A)) := by
    rw [← mul_assoc, h_left, one_mul]
  rw [hA, ← Matrix.trace_sub]

variable {R : Type*} [CommRing R]

/--
Finite matrix trace is invariant under conjugation by a two-sided inverse.

The two-sided inverse is part of the public theorem boundary.  The proof uses
trace cyclicity and the left inverse law after cycling the final factor.
-/
theorem matrix_trace_conjugation_invariant
    (A : Matrix n n R)
    (U U_inv : Matrix n n R)
    (h_right : U * U_inv = 1)
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
    _ = Matrix.trace ((U * U_inv) * A) := by
            rw [h_left, h_right]
    _ = Matrix.trace (1 * A) := by
            rw [h_right]
    _ = Matrix.trace A := by
            simp

/--
Trace invariance for an `InvertibleTransport` of a finite matrix algebra.
-/
theorem matrix_trace_invariant_under_transport
    (A : Matrix n n R)
    (U : InvertibleTransport (Matrix n n R)) :
    Matrix.trace (U.conjugate A) = Matrix.trace A := by
  simpa [InvertibleTransport.conjugate] using Matrix.trace_units_conj U A

/-! ## 2. Verified trace readout -/

set_option linter.dupNamespace false

/-!
A verified trace is an operator-to-scalar map with a proved conjugation
invariance law.  The subtype is the native proof-carrying carrier.
-/
def VerifiedTrace
    (Op Scalar : Type*) [Monoid Op] :=
  {tr : Op → Scalar //
    ∀ (A : Op) (U : InvertibleTransport Op),
      tr (U.conjugate A) = tr A}

namespace VerifiedTrace

variable {Op Scalar : Type*} [Monoid Op]
variable (T : VerifiedTrace Op Scalar)

abbrev tr : Op → Scalar :=
  T.1

theorem invariant
    (A : Op) (U : InvertibleTransport Op) :
    T.tr (U.conjugate A) = T.tr A :=
  T.2 A U

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
    VerifiedTrace (Matrix n n R) R :=
  ⟨Matrix.trace, by
    intro A U
    exact matrix_trace_invariant_under_transport A U⟩

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

end InfoGeometry.OperatorAlgebra.VerifiedTrace
