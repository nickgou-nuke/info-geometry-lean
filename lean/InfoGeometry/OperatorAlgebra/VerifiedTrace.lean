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

/-- A cyclic additive real trace vanishes on an element conjugated to its
negative. The cyclicity and involution hypotheses are explicit: no trace
functional is assumed to exist on an arbitrary ring. -/
theorem cyclic_real_trace_eq_zero_of_involutive_anticommutation
    {B : Type*} [Ring B] (τ : B →+ ℝ)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (J K : B) (hK : K * K = 1) (hKJ : K * J = -(J * K)) :
    τ J = 0 := by
  have hconj : τ (K * J * K) = τ J :=
    cyclic_trace_conjugation_invariant_ring τ h_cyc J K K hK
  have hneg : K * J * K = -J := by
    calc
      K * J * K = (K * J) * K := by rw [mul_assoc]
      _ = (-(J * K)) * K := by rw [hKJ]
      _ = -((J * K) * K) := by rw [neg_mul]
      _ = -(J * (K * K)) := by rw [mul_assoc]
      _ = -J := by rw [hK, mul_one]
  rw [hneg, map_neg] at hconj
  linarith

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

variable {R : Type*} [Ring R]

/-- A cyclic matrix trace over a possibly noncommutative coefficient ring is
invariant under conjugation whenever the conjugating pair has a left inverse.
The cyclicity condition is explicit because the ordinary matrix trace is not
cyclic for arbitrary noncommutative coefficients. -/
theorem matrix_trace_conjugation_invariant
    (A : Matrix n n R)
    (U U_inv : Matrix n n R)
    (h_trace_cyclic : ∀ X Y : Matrix n n R,
      Matrix.trace (X * Y) = Matrix.trace (Y * X))
    (h_left : U_inv * U = 1) :
    Matrix.trace (U * A * U_inv) = Matrix.trace A := by
  calc
    Matrix.trace (U * A * U_inv)
        = Matrix.trace ((U * A) * U_inv) := by
            rw [mul_assoc]
    _ = Matrix.trace (U_inv * (U * A)) := by
            exact h_trace_cyclic (U * A) U_inv
    _ = Matrix.trace ((U_inv * U) * A) := by
            rw [← mul_assoc]
    _ = Matrix.trace (1 * A) := by
            rw [h_left]
    _ = Matrix.trace A := by
            simp

/-! ## 2. The ordinary matrix trace need not be cyclic over noncommutative coefficients -/

/-- Two noncommuting coefficient operators in `Mat₂(ℤ)`. -/
private def traceWitnessA : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![0, 1], ![0, 0]]

private def traceWitnessB : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![0, 0], ![1, 0]]

/-- Outer matrix units with noncommuting operator-valued coefficients. -/
private def traceWitnessX :
    Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ) :=
  ![![0, traceWitnessA], ![0, 0]]

private def traceWitnessY :
    Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ) :=
  ![![0, 0], ![traceWitnessB, 0]]

/-- The usual diagonal-sum matrix trace is not cyclic when its entries lie in
a noncommutative operator ring: the off-diagonal matrix units expose the
coefficient commutator. -/
theorem matrix_trace_not_cyclic_over_operator_coefficients :
    Matrix.trace (traceWitnessX * traceWitnessY) ≠
      Matrix.trace (traceWitnessY * traceWitnessX) := by
  decide

theorem cyclic_trace_invariant_under_transport_ring {B M : Type*} [Ring B]
    (τ : B → M) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (A : B) (U : InvertibleTransport B) :
    τ (U.conjugate A) = τ A := by
  dsimp [InvertibleTransport.conjugate]
  calc
    τ ((U : B) * A * (↑U⁻¹ : B)) = τ (↑U⁻¹ * ((U : B) * A)) := h_cyc ((U : B) * A) (↑U⁻¹ : B)
    _ = τ ((↑U⁻¹ * (U : B)) * A) := by rw [mul_assoc]
    _ = τ A := by rw [Units.inv_mul U, one_mul]

theorem matrix_trace_invariant_under_transport
    (A : Matrix n n R)
    (U : InvertibleTransport (Matrix n n R)) :
    Matrix.trace (U.conjugate A) = Matrix.trace A := by
  simpa [InvertibleTransport.conjugate] using Matrix.trace_units_conj U A

def VerifiedTrace
    (Op Scalar : Type*) [Monoid Op] :=
  {tr : Op → Scalar //
    ∀ (A : Op) (U : InvertibleTransport Op),
      tr (U.conjugate A) = tr A}


abbrev tr : Op → Scalar :=
  T.1


theorem invariant
    (A : Op) (U : InvertibleTransport Op) :
    T.tr (U.conjugate A) = T.tr A :=
  T.2 A U

theorem conjugation_invariant
    (A : Op)
    (U : InvertibleTransport Op) :
    T.tr (U.conjugate A) = T.tr A :=
  T.invariant A U

def matrixVerifiedTrace
    (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R] :
    VerifiedTrace (Matrix n n R) R :=
  ⟨Matrix.trace, by
    intro A U
    exact matrix_trace_invariant_under_transport A U⟩

def realMatrixVerifiedTrace
    (n : ℕ) :
    VerifiedTrace (Matrix (Fin n) (Fin n) ℝ) ℝ :=
  matrixVerifiedTrace (Fin n) ℝ

theorem real_matrix_trace_invariant_under_transport
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (U : InvertibleTransport (Matrix (Fin n) (Fin n) ℝ)) :
    Matrix.trace (U.conjugate A) = Matrix.trace A :=
  matrix_trace_invariant_under_transport A U

end InfoGeometry.OperatorAlgebra.VerifiedTrace
