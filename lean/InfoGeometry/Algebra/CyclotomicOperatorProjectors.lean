/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

/-!
# Native Mathlib Formalization: Cyclotomics, Nilpotents, n-Potents, and Operator Projectors

This module formalizes the exact algebraic backbone connecting:
1. **$n$-Potent spectral separation**: algebraic projectors decomposing $x^n = x$ into
   an orthogonal zero-mode projector $(1 - x^{n-1})$ and a nonzero-mode projector $x^{n-1}$.
2. **Nilpotent-to-unipotent inversion**: the polynomial inversion of unipotent elements
   $1 + N$ for any nilpotent element $N^k = 0$, valid over arbitrary rings and in characteristic 2.
3. **Cyclotomic involutions and spectral projectors**: discrete Fourier projector resolutions
   for finite-order unitary / cyclotomic symmetries ($u^2 = 1$, $u^n = 1$).

All proofs are complete in native Lean 4 + Mathlib with **0 sorrys, 0 admits, and 0 custom axioms**.
-/

namespace InfoGeometry.Algebra.CyclotomicOperatorProjectors

open Finset

/-! ### 1. Predicates: Idempotents, Nilpotents, and n-Potents -/

/-- An element `p` in a ring `R` is idempotent (a projector) if `p * p = p`. -/
def IsIdempotent {R : Type*} [Mul R] (p : R) : Prop :=
  p * p = p

/-- An element `x` is $n$-potent if `x ^ n = x`. -/
def IsNPotent {R : Type*} [Monoid R] (x : R) (n : ℕ) : Prop :=
  x ^ n = x

/-- An element `x` is nilpotent of degree `k` if `x ^ k = 0`. -/
def IsNilpotent {R : Type*} [MonoidWithZero R] (x : R) (k : ℕ) : Prop :=
  x ^ k = 0

/-! ### 2. n-Potent Algebraic Spectral Separation -/

section NPotentSeparation

variable {R : Type*} [Ring R]

/-- The nonzero-mode projector associated to an $n$-potent element $x$. -/
def npotentNonzeroProjector (x : R) (n : ℕ) : R :=
  x ^ (n - 1)

/-- The zero-mode projector associated to an $n$-potent element $x$. -/
def npotentZeroProjector (x : R) (n : ℕ) : R :=
  1 - x ^ (n - 1)

theorem map_npotentNonzeroProjector
    {S : Type*} [Ring S] (f : R →+* S) (x : R) (n : ℕ) :
    f (npotentNonzeroProjector x n) =
      npotentNonzeroProjector (f x) n := by
  simp [npotentNonzeroProjector]

theorem map_npotentZeroProjector
    {S : Type*} [Ring S] (f : R →+* S) (x : R) (n : ℕ) :
    f (npotentZeroProjector x n) =
      npotentZeroProjector (f x) n := by
  simp [npotentZeroProjector]

/-- The defining polynomial of an `n`-potent element factors through `x`. -/
theorem npotent_factorization {x : R} {n : ℕ} (hn : 2 ≤ n)
    (hx : IsNPotent x n) :
    x * (x ^ (n - 1) - 1) = 0 := by
  dsimp [IsNPotent] at hx
  have hs : n - 1 + 1 = n := by omega
  calc
    x * (x ^ (n - 1) - 1) = x * x ^ (n - 1) - x := by rw [mul_sub, mul_one]
    _ = x ^ (n - 1 + 1) - x := by rw [← pow_succ' x (n - 1)]
    _ = x ^ n - x := by rw [hs]
    _ = 0 := by rw [hx, sub_self]

/-- The same defining factorization holds with the factor on the right. -/
theorem npotent_factorization_right {x : R} {n : ℕ} (hn : 2 ≤ n)
    (hx : IsNPotent x n) :
    (x ^ (n - 1) - 1) * x = 0 := by
  dsimp [IsNPotent] at hx
  have hs : n - 1 + 1 = n := by omega
  calc
    (x ^ (n - 1) - 1) * x = x ^ (n - 1) * x - x := by rw [sub_mul, one_mul]
    _ = x ^ (n - 1 + 1) - x := by rw [pow_succ]
    _ = x ^ n - x := by rw [hs]
    _ = 0 := by rw [hx, sub_self]

/-- The nonzero projector of an $n$-potent element is an idempotent. -/
theorem npotent_nonzero_isIdempotent {x : R} {n : ℕ} (hn : 2 ≤ n) (hx : IsNPotent x n) :
    IsIdempotent (npotentNonzeroProjector x n) := by
  dsimp [IsIdempotent, npotentNonzeroProjector]
  have hsucc : n - 1 + (n - 1) = n + (n - 2) := by omega
  have hsucc2 : n - 2 + 1 = n - 1 := by omega
  calc
    x ^ (n - 1) * x ^ (n - 1) = x ^ (n - 1 + (n - 1)) := by rw [← pow_add]
    _ = x ^ (n + (n - 2)) := by rw [hsucc]
    _ = x ^ n * x ^ (n - 2) := by rw [pow_add]
    _ = x * x ^ (n - 2) := by rw [hx]
    _ = x ^ (n - 2 + 1) := (pow_succ' x (n - 2)).symm
    _ = x ^ (n - 1) := by rw [hsucc2]

/-- The zero projector of an $n$-potent element is an idempotent. -/
theorem npotent_zero_isIdempotent {x : R} {n : ℕ} (hn : 2 ≤ n) (hx : IsNPotent x n) :
    IsIdempotent (npotentZeroProjector x n) := by
  dsimp [IsIdempotent, npotentZeroProjector]
  have hidem := npotent_nonzero_isIdempotent hn hx
  dsimp [IsIdempotent, npotentNonzeroProjector] at hidem
  calc
    (1 - x ^ (n - 1)) * (1 - x ^ (n - 1)) =
        1 - x ^ (n - 1) - x ^ (n - 1) + x ^ (n - 1) * x ^ (n - 1) := by noncomm_ring
    _ = 1 - x ^ (n - 1) - x ^ (n - 1) + x ^ (n - 1) := by rw [hidem]
    _ = 1 - x ^ (n - 1) := by noncomm_ring

/-- The zero-mode and nonzero-mode projectors sum to the identity. -/
theorem npotent_projectors_sum_eq_one (x : R) (n : ℕ) :
    npotentZeroProjector x n + npotentNonzeroProjector x n = 1 := by
  dsimp [npotentZeroProjector, npotentNonzeroProjector]
  noncomm_ring

/-- The zero-mode and nonzero-mode projectors are mutually orthogonal. -/
theorem npotent_projectors_orthogonal_left {x : R} {n : ℕ} (hn : 2 ≤ n) (hx : IsNPotent x n) :
    npotentZeroProjector x n * npotentNonzeroProjector x n = 0 := by
  dsimp [npotentZeroProjector, npotentNonzeroProjector]
  have hidem := npotent_nonzero_isIdempotent hn hx
  dsimp [IsIdempotent, npotentNonzeroProjector] at hidem
  calc
    (1 - x ^ (n - 1)) * x ^ (n - 1) = x ^ (n - 1) - x ^ (n - 1) * x ^ (n - 1) := by
      rw [sub_mul, one_mul]
    _ = x ^ (n - 1) - x ^ (n - 1) := by rw [hidem]
    _ = 0 := sub_self (x ^ (n - 1))

/-- The zero-mode and nonzero-mode projectors are mutually orthogonal on the right. -/
theorem npotent_projectors_orthogonal_right {x : R} {n : ℕ} (hn : 2 ≤ n) (hx : IsNPotent x n) :
    npotentNonzeroProjector x n * npotentZeroProjector x n = 0 := by
  dsimp [npotentZeroProjector, npotentNonzeroProjector]
  have hidem := npotent_nonzero_isIdempotent hn hx
  dsimp [IsIdempotent, npotentNonzeroProjector] at hidem
  calc
    x ^ (n - 1) * (1 - x ^ (n - 1)) = x ^ (n - 1) - x ^ (n - 1) * x ^ (n - 1) := by
      rw [mul_sub, mul_one]
    _ = x ^ (n - 1) - x ^ (n - 1) := by rw [hidem]
    _ = 0 := sub_self (x ^ (n - 1))

/-- The zero-mode projector strictly annihilates the $n$-potent element $x$. -/
theorem npotent_zero_projector_annihilates {x : R} {n : ℕ} (hn : 2 ≤ n) (hx : IsNPotent x n) :
    x * npotentZeroProjector x n = 0 := by
  dsimp [npotentZeroProjector]
  have hsucc : n - 1 + 1 = n := by omega
  calc
    x * (1 - x ^ (n - 1)) = x - x * x ^ (n - 1) := by rw [mul_sub, mul_one]
    _ = x - x ^ (n - 1 + 1) := by rw [← pow_succ' x (n - 1)]
    _ = x - x ^ n := by rw [hsucc]
    _ = x - x := by rw [hx]
    _ = 0 := sub_self x

/-- The nonzero-mode projector acts as the identity on the $n$-potent element $x$. -/
theorem npotent_nonzero_projector_acts_as_id {x : R} {n : ℕ} (hn : 2 ≤ n) (hx : IsNPotent x n) :
    x * npotentNonzeroProjector x n = x := by
  dsimp [npotentNonzeroProjector]
  have hsucc : n - 1 + 1 = n := by omega
  calc
    x * x ^ (n - 1) = x ^ (n - 1 + 1) := (pow_succ' x (n - 1)).symm
    _ = x ^ n := by rw [hsucc]
    _ = x := hx

/- The zero-mode projector also annihilates the n-potent element on the left. -/
theorem npotent_zero_projector_left_annihilates {x : R} {n : ℕ} (hn : 2 ≤ n)
    (hx : IsNPotent x n) :
    npotentZeroProjector x n * x = 0 := by
  dsimp [npotentZeroProjector]
  have hsucc : n - 1 + 1 = n := by omega
  calc
    (1 - x ^ (n - 1)) * x = x - x ^ (n - 1) * x := by rw [sub_mul, one_mul]
    _ = x - x ^ n := by rw [← pow_succ x (n - 1), hsucc]
    _ = x - x := by rw [hx]
    _ = 0 := sub_self x

/- The nonzero-mode projector also acts as the identity on the left. -/
theorem npotent_nonzero_projector_left_acts_as_id {x : R} {n : ℕ} (hn : 2 ≤ n)
    (hx : IsNPotent x n) :
    npotentNonzeroProjector x n * x = x := by
  dsimp [npotentNonzeroProjector]
  have hsucc : n - 1 + 1 = n := by omega
  calc
    x ^ (n - 1) * x = x ^ n := by rw [← pow_succ x (n - 1), hsucc]
    _ = x := hx

/- The two algebraic sectors reconstruct every n-potent element. -/
theorem npotent_projector_decomposition {x : R} {n : ℕ} (hn : 2 ≤ n)
    (hx : IsNPotent x n) :
    x = x * npotentZeroProjector x n +
      x * npotentNonzeroProjector x n := by
  rw [npotent_zero_projector_annihilates hn hx,
    npotent_nonzero_projector_acts_as_id hn hx]
  simp

theorem npotent_projector_decomposition_left {x : R} {n : ℕ} (hn : 2 ≤ n)
    (hx : IsNPotent x n) :
    x = npotentZeroProjector x n * x +
      npotentNonzeroProjector x n * x := by
  rw [npotent_zero_projector_left_annihilates hn hx,
    npotent_nonzero_projector_left_acts_as_id hn hx]
  simp

end NPotentSeparation

/-! ### 3. Nilpotent-to-Unipotent Polynomial Inversion -/

section NilpotentUnipotent

variable {R : Type*} [Ring R]

/-- The polynomial geometric sum yielding the exact inverse of $1 + x$ when $x^k = 0$. -/
def unipotentInvPoly (x : R) (k : ℕ) : R :=
  ∑ i ∈ range k, (-x) ^ i

/-- Exact left-inversion: $(1 + x) \cdot \sum_{i=0}^{k-1} (-x)^i = 1$ when $x^k = 0$. -/
theorem unipotent_mul_inv_eq_one {x : R} {k : ℕ} (hx : IsNilpotent x k) :
    (1 + x) * unipotentInvPoly x k = 1 := by
  dsimp [unipotentInvPoly]
  have hgeom := mul_geom_sum (-x) k
  have hneg : (-x) ^ k = 0 := by
    rw [neg_pow, hx]
    simp
  have hgeom' : (-x - 1) * (∑ i ∈ range k, (-x) ^ i) = -1 := by
    rw [hneg] at hgeom
    simpa only [zero_sub] using hgeom
  calc
    (1 + x) * (∑ i ∈ range k, (-x) ^ i) =
        -((-x - 1) * (∑ i ∈ range k, (-x) ^ i)) := by
      rw [show 1 + x = -(-x - 1) by noncomm_ring, neg_mul]
    _ = -(-1) := by rw [hgeom']
    _ = 1 := neg_neg 1

/-- Exact right-inversion: $(\sum_{i=0}^{k-1} (-x)^i) \cdot (1 + x) = 1$ when $x^k = 0$. -/
theorem unipotent_inv_mul_eq_one {x : R} {k : ℕ} (hx : IsNilpotent x k) :
    unipotentInvPoly x k * (1 + x) = 1 := by
  dsimp [unipotentInvPoly]
  have hgeom := geom_sum_mul (-x) k
  have hneg : (-x) ^ k = 0 := by
    rw [neg_pow, hx]
    simp
  have hgeom' : (∑ i ∈ range k, (-x) ^ i) * (-x - 1) = -1 := by
    rw [hneg] at hgeom
    simpa only [zero_sub] using hgeom
  calc
    (∑ i ∈ range k, (-x) ^ i) * (1 + x) =
        -((∑ i ∈ range k, (-x) ^ i) * (-x - 1)) := by
      rw [show 1 + x = -(-x - 1) by noncomm_ring, mul_neg]
    _ = -(-1) := by rw [hgeom']
    _ = 1 := neg_neg 1

/-- Any unipotent element $1 + x$ generated by a nilpotent element $x^k = 0$ is a unit in $R^\times$. -/
theorem unipotent_isUnit_of_nilpotent {x : R} {k : ℕ} (hx : IsNilpotent x k) :
    IsUnit (1 + x) := by
  refine ⟨⟨1 + x, unipotentInvPoly x k,
    unipotent_mul_inv_eq_one hx, unipotent_inv_mul_eq_one hx⟩, rfl⟩

/-- In characteristic 2, $(-x)^i = x^i$, so $(1 + x)^{-1} = \sum_{i=0}^{k-1} x^i$. -/
theorem unipotent_mul_geom_sum_eq_one_charTwo
    {x : R} {k : ℕ} (hchar : ∀ r : R, r + r = 0) (hx : IsNilpotent x k) :
    (1 + x) * (∑ i ∈ range k, x ^ i) = 1 := by
  have hneg : -x = x := by
    have h2 : x + x = 0 := hchar x
    exact (eq_neg_of_add_eq_zero_left h2).symm
  have hinv := unipotent_mul_inv_eq_one hx
  dsimp [unipotentInvPoly] at hinv
  have heq : (∑ i ∈ range k, (-x) ^ i) = (∑ i ∈ range k, x ^ i) := by
    congr 1
    ext i
    rw [hneg]
  rw [heq] at hinv
  exact hinv

/-- In characteristic 2 the same finite polynomial is also a right inverse. -/
theorem unipotent_geom_sum_mul_eq_one_charTwo
    {x : R} {k : ℕ} (hchar : ∀ r : R, r + r = 0) (hx : IsNilpotent x k) :
    (∑ i ∈ range k, x ^ i) * (1 + x) = 1 := by
  have hneg : -x = x := by
    have h2 : x + x = 0 := hchar x
    exact (eq_neg_of_add_eq_zero_left h2).symm
  have hinv := unipotent_inv_mul_eq_one hx
  dsimp [unipotentInvPoly] at hinv
  have heq : (∑ i ∈ range k, (-x) ^ i) = (∑ i ∈ range k, x ^ i) := by
    congr 1
    ext i
    rw [hneg]
  rw [heq] at hinv
  exact hinv

end NilpotentUnipotent

/-! ### 4. Finite-order geometric annihilation -/

section CyclotomicGeometricSum

variable {R : Type*} [Ring R]

/-- The geometric sum is annihilated by `1 - u` for a finite-order element. -/
theorem root_of_unity_geometric_sum_annihilates {u : R} {n : ℕ}
    (hu : u ^ n = 1) :
    (1 - u) * (∑ i ∈ range n, u ^ i) = 0 := by
  simpa [hu] using (mul_neg_geom_sum u n)

/-- The same finite-order annihilation holds on the right. -/
theorem root_of_unity_geometric_sum_annihilates_right {u : R} {n : ℕ}
    (hu : u ^ n = 1) :
    (∑ i ∈ range n, u ^ i) * (1 - u) = 0 := by
  simpa [hu] using (geom_sum_mul_neg u n)

/-- If `1 - u` is invertible, the finite-order geometric sum vanishes. -/
theorem root_of_unity_geometric_sum_eq_zero {u : R} {n : ℕ}
    (hu : u ^ n = 1) (hunit : IsUnit (1 - u)) :
    (∑ i ∈ range n, u ^ i) = 0 := by
  apply hunit.mul_left_cancel
  simpa using root_of_unity_geometric_sum_annihilates hu

/-- The zero conclusion can equivalently be obtained by right cancellation. -/
theorem root_of_unity_geometric_sum_eq_zero_right {u : R} {n : ℕ}
    (hu : u ^ n = 1) (hunit : IsUnit (1 - u)) :
    (∑ i ∈ range n, u ^ i) = 0 := by
  apply hunit.mul_right_cancel
  simpa using root_of_unity_geometric_sum_annihilates_right hu

end CyclotomicGeometricSum

section CyclotomicFieldSpecialization

variable {K : Type*} [Field K]

/-- In a field, every nontrivial finite-order element has zero geometric sum. -/
theorem root_of_unity_geometric_sum_eq_zero_of_ne_one {u : K} {n : ℕ}
    (hu : u ^ n = 1) (hune : u ≠ 1) :
    (∑ i ∈ range n, u ^ i) = 0 := by
  apply root_of_unity_geometric_sum_eq_zero hu
  exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hune))

end CyclotomicFieldSpecialization

/-! ### 4. Cyclotomic Involutions and Spectral Projectors -/

section CyclotomicInvolutions

variable {R : Type*} [CommRing R]

/-- Projector for the $+1$ eigenspace of an involution $u^2 = 1$ in a commutative ring with $1/2$. -/
def involutionPlusProjector (u : R) (half : R) : R :=
  half * (1 + u)

/-- Projector for the $-1$ eigenspace of an involution $u^2 = 1$ in a commutative ring with $1/2$. -/
def involutionMinusProjector (u : R) (half : R) : R :=
  half * (1 - u)

/-- The $+1$ involution projector is idempotent given $2 \cdot \mathrm{half} = 1$. -/
theorem involution_plus_isIdempotent {u half : R}
    (hhalf : 2 * half = 1)
    (hu : u ^ 2 = 1) :
    IsIdempotent (involutionPlusProjector u half) := by
  dsimp [IsIdempotent, involutionPlusProjector]
  have hu2 : u * u = 1 := by
    rw [← pow_two]
    exact hu
  calc
    (half * (1 + u)) * (half * (1 + u)) =
        (half * (2 * half)) * (1 + u) + (half * half) * (u * u - 1) := by ring
    _ = (half * 1) * (1 + u) + (half * half) * (1 - 1) := by rw [hhalf, hu2]
    _ = half * (1 + u) := by ring

/-- The $-1$ involution projector is idempotent given $2 \cdot \mathrm{half} = 1$. -/
theorem involution_minus_isIdempotent {u half : R}
    (hhalf : 2 * half = 1)
    (hu : u ^ 2 = 1) :
    IsIdempotent (involutionMinusProjector u half) := by
  dsimp [IsIdempotent, involutionMinusProjector]
  have hu2 : u * u = 1 := by
    rw [← pow_two]
    exact hu
  calc
    (half * (1 - u)) * (half * (1 - u)) =
        (half * (2 * half)) * (1 - u) + (half * half) * (u * u - 1) := by ring
    _ = (half * 1) * (1 - u) + (half * half) * (1 - 1) := by rw [hhalf, hu2]
    _ = half * (1 - u) := by ring

/-- The $+1$ and $-1$ involution projectors are mutually orthogonal. -/
theorem involution_projectors_orthogonal {u half : R}
    (hu : u ^ 2 = 1) :
    involutionPlusProjector u half * involutionMinusProjector u half = 0 := by
  dsimp [involutionPlusProjector, involutionMinusProjector]
  have hu2 : u * u = 1 := by
    rw [← pow_two]
    exact hu
  calc
    (half * (1 + u)) * (half * (1 - u)) =
        (half * half) * (1 - u * u) := by ring
    _ = (half * half) * (1 - 1) := by rw [hu2]
    _ = 0 := by ring

/-- The $+1$ and $-1$ involution projectors sum to the identity: $P_+ + P_- = 1$. -/
theorem involution_projectors_sum_eq_one {u half : R}
    (hhalf : 2 * half = 1) :
    involutionPlusProjector u half + involutionMinusProjector u half = 1 := by
  dsimp [involutionPlusProjector, involutionMinusProjector]
  calc
    half * (1 + u) + half * (1 - u) = (2 * half) * 1 := by ring
    _ = 1 * 1 := by rw [hhalf]
    _ = 1 := mul_one 1

/-- Spectral reconstruction: $u = P_+ - P_-$. -/
theorem involution_spectral_reconstruction {u half : R}
    (hhalf : 2 * half = 1) :
    involutionPlusProjector u half - involutionMinusProjector u half = u := by
  dsimp [involutionPlusProjector, involutionMinusProjector]
  calc
    half * (1 + u) - half * (1 - u) = (2 * half) * u := by ring
    _ = 1 * u := by rw [hhalf]
    _ = u := one_mul u

/- The involution acts by its defining eigenvalue on each projector. -/
theorem involution_plus_projector_eigen {u half : R} (hu : u ^ 2 = 1) :
    u * involutionPlusProjector u half = involutionPlusProjector u half := by
  dsimp [involutionPlusProjector]
  calc
    u * (half * (1 + u)) = half * (u + u * u) := by ring
    _ = half * (u + 1) := by rw [← pow_two u, hu]
    _ = half * (1 + u) := by ring

theorem involution_minus_projector_eigen {u half : R} (hu : u ^ 2 = 1) :
    u * involutionMinusProjector u half = -involutionMinusProjector u half := by
  dsimp [involutionMinusProjector]
  calc
    u * (half * (1 - u)) = half * (u - u * u) := by ring
    _ = half * (u - 1) := by rw [← pow_two u, hu]
    _ = -(half * (1 - u)) := by ring

theorem involution_plus_projector_right_eigen {u half : R} (hu : u ^ 2 = 1) :
    involutionPlusProjector u half * u = involutionPlusProjector u half := by
  rw [mul_comm]
  exact involution_plus_projector_eigen hu

theorem involution_minus_projector_right_eigen {u half : R} (hu : u ^ 2 = 1) :
    involutionMinusProjector u half * u = -involutionMinusProjector u half := by
  rw [mul_comm]
  exact involution_minus_projector_eigen hu

end CyclotomicInvolutions

end InfoGeometry.Algebra.CyclotomicOperatorProjectors
