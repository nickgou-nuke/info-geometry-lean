import InfoGeometry.Canonical.SpinorialCore.Algebra

/-!
# Tensor-factor order one and polynomial gauge invariance

The right-even hypothesis is retained explicitly. No spectral-triple,
continuum-action, or singularity-resolution claim is inferred here.
-/

namespace InfoGeometry.Canonical.SpinorialCore

section Tensor
open scoped TensorProduct
variable {R A B : Type*} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]

/-- Algebra commutator. -/
def commutator {C : Type*} [Ring C] (x y : C) : C := x * y - y * x

/-- The two-factor operator with a right grading. -/
def bipartiteDirac (DL : A) (beta DR : B) : A ⊗[R] B :=
  DL ⊗ₜ[R] beta + (1 : A) ⊗ₜ[R] DR

/-- Exact factorization, before imposing any evenness restriction. -/
theorem order_one_factorization (DL a : A) (beta DR b : B) :
    commutator (commutator (bipartiteDirac (R := R) DL beta DR)
      (a ⊗ₜ[R] (1 : B))) ((1 : A) ⊗ₜ[R] b) =
      commutator DL a ⊗ₜ[R] commutator beta b := by
  simp only [commutator, bipartiteDirac, add_mul, mul_add, sub_mul, mul_sub,
    Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.sub_tmul,
    TensorProduct.tmul_sub, one_mul, mul_one]
  abel

theorem order_one_even (DL a : A) (beta DR b : B)
    (heven : beta * b = b * beta) :
    commutator (commutator (bipartiteDirac (R := R) DL beta DR)
      (a ⊗ₜ[R] (1 : B))) ((1 : A) ⊗ₜ[R] b) = 0 := by
  rw [order_one_factorization]
  simp [commutator, heven]

end Tensor

section Gauge
variable {A : Type*} [Ring A]

/-- Conjugation commutes with powers in an arbitrary associative ring. -/
theorem conjugation_pow (u : Aˣ) (X : A) (n : ℕ) :
    ((u : A) * X * (↑(u⁻¹) : A)) ^ n =
      (u : A) * X ^ n * (↑(u⁻¹) : A) := by
  have hui : (↑(u⁻¹) : A) * (u : A) = 1 := u.inv_val
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    calc
      (u : A) * X ^ n * ↑(u⁻¹) * ((u : A) * X * ↑(u⁻¹)) =
          (u : A) * (X ^ n * ((↑(u⁻¹) : A) * ↑u) * X) * ↑(u⁻¹) := by
        noncomm_ring
      _ = (u : A) * X ^ (n + 1) * ↑(u⁻¹) := by
        rw [hui]
        simp [pow_succ, mul_assoc]

end Gauge

section Trace
variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem trace_conjugation (u : (Matrix n n R)ˣ) (X : Matrix n n R) :
    Matrix.trace ((u : Matrix n n R) * X * ↑(u⁻¹)) = Matrix.trace X := by
  have hui : (↑(u⁻¹) : Matrix n n R) * (u : Matrix n n R) = 1 := u.inv_val
  calc
    Matrix.trace ((u : Matrix n n R) * X * ↑(u⁻¹)) =
        Matrix.trace ((↑(u⁻¹) : Matrix n n R) * ((u : Matrix n n R) * X)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace X := by rw [← mul_assoc, hui, one_mul]

/-- Finite polynomial trace action, with all coefficients explicit. -/
def polynomialTrace (N : ℕ) (c : Fin (N + 1) → R) (X : Matrix n n R) : R :=
  ∑ i, c i * Matrix.trace (X ^ (i : ℕ))

theorem polynomialTrace_conjugation (N : ℕ) (c : Fin (N + 1) → R)
    (u : (Matrix n n R)ˣ) (X : Matrix n n R) :
    polynomialTrace N c ((u : Matrix n n R) * X * ↑(u⁻¹)) =
      polynomialTrace N c X := by
  unfold polynomialTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [conjugation_pow, trace_conjugation]

end Trace
end InfoGeometry.Canonical.SpinorialCore
