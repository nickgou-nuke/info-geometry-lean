/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.deprecated false

/-!
# Finite Möbius/Polarization Matrix Identities

This module proves identities for four explicit `2 × 2` matrices over a
commutative ring: two involutions, their anticommutation, and the induced metric
and symplectic-form transformations. It also proves an integer parity identity
and a conditional algebraic consequence of a first-order product equation.

It does not construct a super-vector space, super-Grassmannian, quotient
manifold/sheaf, Berezinian Jacobian, or Stiefel–Whitney class. Those geometric
interpretations are not established by these finite matrix calculations.
-/

namespace InfoGeometry.SuperGrassmannian.MoebiusQuotient

open Matrix

variable {R : Type*} [CommRing R]

/-! --------------------------------------------------------------------------
    Section 1: Block Representation of the Ambient Carrier Algebra
    -------------------------------------------------------------------------- -/

/-- The canonical polarization operator K = diag(1, -1). -/
def K_mat : Matrix (Fin 2) (Fin 2) R :=
  !![ 1,  0;
      0, -1]

/-- The Möbius sheet-swapping involution M = ((0, 1), (1, 0)). -/
def M_mat : Matrix (Fin 2) (Fin 2) R :=
  !![ 0,  1;
      1,  0]

/-- The neutral metric g = ((0, 1), (1, 0)). -/
def g_mat : Matrix (Fin 2) (Fin 2) R :=
  !![ 0,  1;
      1,  0]

/-- The symplectic form ω = ((0, 1), (-1, 0)). -/
def omega_mat : Matrix (Fin 2) (Fin 2) R :=
  !![  0, 1;
      -1, 0]

/-! --------------------------------------------------------------------------
    Section 2: Carrier Involutions and Anti-Commutation Theorems
    -------------------------------------------------------------------------- -/

/-- K is an involution: K² = 1. -/
theorem K_sq_id : K_mat (R := R) * K_mat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- M is an involution: M² = 1. -/
theorem M_sq_id : M_mat (R := R) * M_mat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [M_mat, Matrix.mul_apply, Fin.sum_univ_two]

/--
The Möbius Anti-Commutation Law:
{M, K} = M K + K M = 0 ↔ M K = - K M.
Forces all diagonal blocks of the reflection operator to vanish.
-/
theorem moebius_anticommutes_polarization :
    M_mat (R := R) * K_mat + K_mat * M_mat = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [M_mat, K_mat]

theorem moebius_comm_polarization_neg :
    M_mat (R := R) * K_mat = - (K_mat * M_mat) := by
  rw [← add_eq_zero_iff_eq_neg]
  exact moebius_anticommutes_polarization

/-- Anticommutation sends every `+1` eigenvector of `K_mat` to a `-1`
eigenvector under `M_mat`. -/
theorem moebius_maps_positive_eigenspace_to_negative (v : Fin 2 → R)
    (hv : K_mat (R := R) *ᵥ v = v) :
    K_mat (R := R) *ᵥ (M_mat *ᵥ v) = -(M_mat *ᵥ v) := by
  have hKM : K_mat (R := R) * M_mat = -(M_mat * K_mat) := by
    have hsum : K_mat (R := R) * M_mat + M_mat * K_mat = 0 := by
      simpa [add_comm] using moebius_anticommutes_polarization (R := R)
    exact add_eq_zero_iff_eq_neg.mp hsum
  calc
    K_mat (R := R) *ᵥ (M_mat *ᵥ v) = (K_mat * M_mat) *ᵥ v :=
      Matrix.mulVec_mulVec v K_mat M_mat
    _ = (-(M_mat * K_mat)) *ᵥ v := by rw [hKM]
    _ = -((M_mat * K_mat) *ᵥ v) := Matrix.neg_mulVec v (M_mat * K_mat)
    _ = -(M_mat *ᵥ (K_mat *ᵥ v)) := by rw [Matrix.mulVec_mulVec]
    _ = -(M_mat *ᵥ v) := by rw [hv]

/-! --------------------------------------------------------------------------
    Section 3: Metric Isometry and Symplectic Reflection
    -------------------------------------------------------------------------- -/

/--
Metric Invariance:
The Möbius involution M is an exact isometry of the neutral metric g:
Mᵀ g M = g.
-/
theorem moebius_metric_isometry :
    (M_mat (R := R)).transpose * g_mat * M_mat = g_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [M_mat, g_mat, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

/--
Symplectic Anti-Invariance (Phase Space Reflection):
The Möbius involution reverses the orientation of the symplectic form:
Mᵀ ω M = - ω.
-/
theorem moebius_symplectic_anti_invariance :
    (M_mat (R := R)).transpose * omega_mat * M_mat = - omega_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [M_mat, omega_mat, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

/-! --------------------------------------------------------------------------
    Section 4: Integer Parity Identity
    -------------------------------------------------------------------------- -/

/-- A natural number and its square have the same parity. -/
lemma nat_sq_parity_iff (k : ℕ) : Even (k ^ 2) ↔ Even k := by
  simp [Nat.even_pow]

/-- `(-1)^k` depends only on the parity of the natural exponent; this theorem
makes no claim about a Berezinian, Jacobian, or orientation class. -/
theorem neg_one_pow_square_eq_self (k : ℕ) :
    (-1 : ℤ) ^ (k ^ 2) = (-1 : ℤ) ^ k := by
  by_cases h : Even k
  · have h_sq : Even (k ^ 2) := (nat_sq_parity_iff k).mpr h
    rw [h_sq.neg_one_pow, h.neg_one_pow]
  · rw [Nat.not_even_iff_odd] at h
    have h_sq_odd : Odd (k ^ 2) := by
      rw [← Nat.not_even_iff_odd]
      intro h_even
      have := (nat_sq_parity_iff k).mp h_even
      exact (Nat.not_even_iff_odd.mpr h) this
    rw [h_sq_odd.neg_one_pow, h.neg_one_pow]

/-! --------------------------------------------------------------------------
    Section 5: Conditional Inverse-Product Variation Identity
    -------------------------------------------------------------------------- -/

variable {A : Type*} [Ring A]

/-- If `T_inv * T = 1` and `T * δ + H * T_inv = 0`, then the supplied
variation satisfies `δ = -T_inv * H * T_inv`. This is a conditional ring identity,
not a formal derivative theorem. -/
theorem inverse_product_variation_algebraic_identity
    (T T_inv H δ : A)
    (h_left : T_inv * T = 1)
    (h_var : T * δ + H * T_inv = 0) :
    δ = - (T_inv * H * T_inv) := by
  have h_eq : T_inv * (T * δ + H * T_inv) = 0 := by rw [h_var, mul_zero]
  rw [mul_add, ← mul_assoc T_inv T δ, h_left, one_mul] at h_eq
  have h_solve : δ + T_inv * H * T_inv = 0 := by
    calc δ + T_inv * H * T_inv = δ + T_inv * (H * T_inv) := by rw [mul_assoc]
    _ = 0 := h_eq
  rw [add_eq_zero_iff_eq_neg] at h_solve
  exact h_solve

end InfoGeometry.SuperGrassmannian.MoebiusQuotient
