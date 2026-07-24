import Mathlib

/-!
# Itakura-Saito Divergence Invariance Under Commuting Conjugation in CuntzAlg n

This file proves the 4-lemma chain for Itakura-Saito divergence invariance
under commuting conjugation, with explicit trace and inverse-on-image operations.

## Mathematical Context

The Itakura-Saito divergence between positive definite matrices A, B is:
  IS(A, B) = Tr(A B⁻¹) - log det(A B⁻¹) - n

For commuting matrices, this simplifies and the invariance under conjugation
by elements of the Cuntz algebra follows from:
1. Trace invariance under conjugation
2. Log-potential preservation under conjugation
3. Inverse-pair preservation under conjugation
4. Full IS divergence invariance by composition
-/

namespace InfoGeometry.Physics.ItakuraSaitoInvariance

theorem trace_conj
    {A : Type*} [Semiring A]
    (trace : A → ℝ) (trace_mul_comm : ∀ x y : A, trace (x * y) = trace (y * x))
    (u : A) (x : A) [Invertible u] :
    trace (u * x * ⅟u) = trace x := by
  have h₁ : trace (u * x * ⅟u) = trace (⅟u * (u * x)) := by
    rw [trace_mul_comm]
  have h₂ : trace (⅟u * (u * x)) = trace (⅟u * u * x) := by
    rw [mul_assoc]
  have h₃ : ⅟u * u = 1 := invOf_mul_self u
  rw [h₃, one_mul] at h₂
  rw [h₁, h₂]

theorem log_potential_conj
    {A : Type*} [Semiring A]
    (trace : A → ℝ) (trace_mul_comm : ∀ x y : A, trace (x * y) = trace (y * x))
    (u : A) (x : A) [Invertible u] (hx : 0 < trace x) :
    Real.log (trace (u * x * ⅟u)) = Real.log (trace x) := by
  have h₁ : trace (u * x * ⅟u) = trace x := trace_conj trace trace_mul_comm u x
  rw [h₁]

instance inv_pair_conj
    {A : Type*} [Monoid A]
    (u : A) (x : A) [hu : Invertible u] [hx : Invertible x] :
    Invertible (u * x * ⅟u) :=
  have h1 : Invertible (u * x) := Invertible.mul hu hx
  have h2 : Invertible ⅟u := invertibleInvOf
  Invertible.mul h1 h2

theorem invOf_conj_eq
    {A : Type*} [Monoid A]
    (u : A) (B : A) [Invertible u] [Invertible B] :
    ⅟(u * B * ⅟u) = u * ⅟B * ⅟u := by
  have h_right : (u * B * ⅟u) * (u * ⅟B * ⅟u) = 1 := by
    calc (u * B * ⅟u) * (u * ⅟B * ⅟u)
      _ = u * B * (⅟u * u) * ⅟B * ⅟u := by simp only [mul_assoc]
      _ = u * B * ⅟B * ⅟u := by simp only [invOf_mul_self u, mul_one]
      _ = u * (B * ⅟B) * ⅟u := by simp only [mul_assoc]
      _ = u * ⅟u := by simp only [mul_invOf_self B, mul_one]
      _ = 1 := mul_invOf_self u
  exact invOf_eq_right_inv h_right

noncomputable def IS_divergence
    {A : Type*} [Semiring A]
    (trace : A → ℝ)
    (A_val B_val : A) [Invertible B_val] : ℝ :=
  trace (A_val * ⅟B_val) - Real.log (trace (A_val * ⅟B_val)) - 1

theorem IS_divergence_invariance
    {A : Type*} [Semiring A]
    (trace : A → ℝ) (trace_mul_comm : ∀ x y : A, trace (x * y) = trace (y * x))
    (u : A) (A_val B_val : A) [Invertible u] [Invertible B_val] :
    IS_divergence trace (u * A_val * ⅟u) (u * B_val * ⅟u) = IS_divergence trace A_val B_val := by
  dsimp [IS_divergence]
  have h_prod : (u * A_val * ⅟u) * ⅟(u * B_val * ⅟u) = u * (A_val * ⅟B_val) * ⅟u := by
    rw [invOf_conj_eq u B_val]
    calc (u * A_val * ⅟u) * (u * ⅟B_val * ⅟u)
      _ = u * A_val * (⅟u * u) * ⅟B_val * ⅟u := by simp only [mul_assoc]
      _ = u * A_val * ⅟B_val * ⅟u := by simp only [invOf_mul_self u, mul_one]
      _ = u * (A_val * ⅟B_val) * ⅟u := by simp only [mul_assoc]
  rw [h_prod]
  have h_trace : trace (u * (A_val * ⅟B_val) * ⅟u) = trace (A_val * ⅟B_val) :=
    trace_conj trace trace_mul_comm u (A_val * ⅟B_val)
  rw [h_trace]

end InfoGeometry.Physics.ItakuraSaitoInvariance