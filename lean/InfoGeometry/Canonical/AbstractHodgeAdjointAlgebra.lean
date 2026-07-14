import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Abstract Hodge Adjoint Algebra

This file proves finite algebraic Hodge identities from explicit theorem
hypotheses: a symmetric positive definite bilinear form `B` and an adjoint pair
of linear maps `d` and `delt`. It does not assert a manifold, differential
forms, elliptic regularity, or analytic Hodge decomposition.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `B_zero_left`, `B_delt_left`, `B_d_d_eq_B_delt_delt`,
  `delt_comp_delt_zero`, `L`, `harmonic_iff_closed_and_coclosed`,
  `exact_coexact_orthogonal`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES:
  The theorems are conditional on their explicitly named bilinear-form laws,
  definiteness, and adjoint equation. `delt_comp_delt_zero` and
  `exact_coexact_orthogonal` additionally assume `d.comp d = 0`.
- BUCKET 3: OPEN CLOSURE DEBT:
  Analytic Hodge decomposition and geometric realization of these operators are
  not asserted here.
-/

namespace AbstractHodgeAdjointAlgebra

variable {V : Type*} [AddCommGroup V]

/-- Left evaluation of the bilinear form at zero vanishes. -/
theorem B_zero_left
    (B : V → V → ℝ)
    (B_add_left : ∀ x y z, B (x + y) z = B x z + B y z)
    (x : V) :
    B 0 x = 0 := by
  have h : B 0 x = B 0 x + B 0 x := by
    calc
      B 0 x = B (0 + 0) x := by rw [add_zero]
      _ = B 0 x + B 0 x := B_add_left 0 0 x
  linarith

variable [Module ℝ V]

/-- The coderivative is the adjoint of `d` on the left argument as well. -/
theorem B_delt_left
    (B : V → V → ℝ)
    (B_comm : ∀ x y, B x y = B y x)
    (d delt : V →ₗ[ℝ] V)
    (h_adj : ∀ x y, B (d x) y = B x (delt y))
    (u v : V) :
    B (delt u) v = B u (d v) := by
  rw [B_comm (delt u) v]
  rw [← h_adj v u]
  rw [B_comm (d v) u]

/-- Double-adjoint transport identity. -/
theorem B_d_d_eq_B_delt_delt
    (B : V → V → ℝ)
    (d delt : V →ₗ[ℝ] V)
    (h_adj : ∀ x y, B (d x) y = B x (delt y))
    (u v : V) :
    B (d (d u)) v = B u (delt (delt v)) := by
  calc
    B (d (d u)) v = B (d u) (delt v) := h_adj (d u) v
    _ = B u (delt (delt v)) := h_adj u (delt v)

/-- If `d² = 0`, then `delt² = 0` under the definite adjoint pairing. -/
theorem delt_comp_delt_zero
    (B : V → V → ℝ)
    (B_add_left : ∀ x y z, B (x + y) z = B x z + B y z)
    (B_zero : ∀ x, B x x = 0 ↔ x = 0)
    (d delt : V →ₗ[ℝ] V)
    (h_adj : ∀ x y, B (d x) y = B x (delt y))
    (hd2 : d.comp d = 0)
    (v : V) :
    delt (delt v) = 0 := by
  have h_comp : ∀ u, d (d u) = 0 := by
    intro u
    have h_eq : d (d u) = (d.comp d) u := rfl
    rw [h_eq, hd2]
    rfl
  have h_self : B (delt (delt v)) (delt (delt v)) = 0 := by
    have h_double :
        B (delt (delt v)) (delt (delt v)) = B (d (d (delt (delt v)))) v := by
      exact (B_d_d_eq_B_delt_delt B d delt h_adj (delt (delt v)) v).symm
    rw [h_double]
    rw [h_comp]
    exact B_zero_left B B_add_left v
  exact (B_zero (delt (delt v))).mp h_self

/-- The abstract Hodge Laplacian `d ∘ delt + delt ∘ d`. -/
def L (d delt : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (d.comp delt) + (delt.comp d)

/-- Harmonic vectors are exactly closed and coclosed vectors in this finite algebraic setting. -/
theorem harmonic_iff_closed_and_coclosed
    (B : V → V → ℝ)
    (B_comm : ∀ x y, B x y = B y x)
    (B_add_left : ∀ x y z, B (x + y) z = B x z + B y z)
    (B_nonneg : ∀ x, 0 ≤ B x x)
    (B_zero : ∀ x, B x x = 0 ↔ x = 0)
    (d delt : V →ₗ[ℝ] V)
    (h_adj : ∀ x y, B (d x) y = B x (delt y))
    (x : V) :
    L d delt x = 0 ↔ d x = 0 ∧ delt x = 0 := by
  constructor
  · intro h
    have h_sum :
        B (L d delt x) x = B (delt x) (delt x) + B (d x) (d x) := by
      have h1 : L d delt x = d (delt x) + delt (d x) := rfl
      rw [h1]
      rw [B_add_left]
      have h_first : B (d (delt x)) x = B (delt x) (delt x) := h_adj (delt x) x
      have h_second : B (delt (d x)) x = B (d x) (d x) :=
        B_delt_left B B_comm d delt h_adj (d x) x
      rw [h_first, h_second]
    have h_eq : B (delt x) (delt x) + B (d x) (d x) = 0 := by
      rw [← h_sum]
      rw [h]
      exact B_zero_left B B_add_left x
    have h_nonneg_delt : 0 ≤ B (delt x) (delt x) := B_nonneg (delt x)
    have h_nonneg_d : 0 ≤ B (d x) (d x) := B_nonneg (d x)
    have h_delt_zero : B (delt x) (delt x) = 0 := by linarith
    have h_d_zero : B (d x) (d x) = 0 := by linarith
    exact ⟨(B_zero (d x)).mp h_d_zero, (B_zero (delt x)).mp h_delt_zero⟩
  · rintro ⟨h1, h2⟩
    have hL : L d delt x = d (delt x) + delt (d x) := rfl
    simp [hL, h1, h2]

/-- Exact and coexact components are orthogonal when `d² = 0`. -/
theorem exact_coexact_orthogonal
    (B : V → V → ℝ)
    (B_comm : ∀ x y, B x y = B y x)
    (B_add_left : ∀ x y z, B (x + y) z = B x z + B y z)
    (B_zero : ∀ x, B x x = 0 ↔ x = 0)
    (d delt : V →ₗ[ℝ] V)
    (h_adj : ∀ x y, B (d x) y = B x (delt y))
    (hd2 : d.comp d = 0)
    (u v : V) :
    B (d u) (delt v) = 0 := by
  have h_delt_delt : delt (delt v) = 0 :=
    delt_comp_delt_zero B B_add_left B_zero d delt h_adj hd2 v
  calc
    B (d u) (delt v) = B u (delt (delt v)) := h_adj u (delt v)
    _ = B u 0 := by rw [h_delt_delt]
    _ = B 0 u := B_comm u 0
    _ = 0 := B_zero_left B B_add_left u

end AbstractHodgeAdjointAlgebra
