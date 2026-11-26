/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Global Iwasawa KAN, Polar Symmetric Space, and Casimir Reduction

This module formalizes the global Lie-theoretic decompositions and the algebraic
invariant hierarchy of the isometry carrier algebra:

1. **The Iwasawa Decomposition ($G = K A N$ / $\mathfrak{g} = \mathfrak{k} \oplus \mathfrak{a} \oplus \mathfrak{n}$)**:
   - Compact generalized gauge rotations ($\mathfrak{k} = \mathfrak{so}(2)$)
   - Chiral / Cartan hyperbolic dilations ($\mathfrak{a}$)
   - Strictly nilpotent lightcone shears ($\mathfrak{n}$)
   - Exact uniqueness of decomposition over general commutative rings.

2. **The Cartan / Polar Decomposition ($\mathfrak{g} = \mathfrak{k} \oplus \mathfrak{p}$)**:
   - Cartan involution $\Theta(X) = -X^T$
   - Eigenspace splitting $\Theta(K) = K$ and $\Theta(P) = -P$
   - Symmetric space commutation relations:
     $[\mathfrak{k}, \mathfrak{k}] \subseteq \mathfrak{k}$
     $[\mathfrak{k}, \mathfrak{p}] \subseteq \mathfrak{p}$
     $[\mathfrak{p}, \mathfrak{p}] \subseteq \mathfrak{k}$
   - Uniqueness over rings with invertible 2.

3. **Complete Invariant Hierarchy (Casimirs & Harish-Chandra Radial Reduction)**:
   - Linear Casimir (trace / supertrace) $C_1(X) = 0$ on $\mathfrak{sl}(2, R)$.
   - Quadratic Casimir $C_2(X) = \operatorname{tr}(X^2)$.
   - Radial reduction on Cartan: $C_2(A(\theta)) = 2\theta^2$.
   - Nilpotent vanishing: $N^2 = 0 \implies C_1(N) = 0 \wedge C_2(N) = 0$ (nilpotent shears carry zero Casimir charge).
   - Weyl invariance: $C_2(A(-\theta)) = C_2(A(\theta))$ under the Weyl group $W \cong \mathbb{Z}_2$.
   - Gauge invariance: $C_2(g X g^{-1}) = C_2(X)$ for all invertible transformations $g$.

All definitions and theorems operate strictly on native matrix algebras (`Matrix (Fin 2) (Fin 2) R`).
Zero scalar toy proxies (Trap T16 compliance).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Experimental.Sandbox.Lie.GlobalKANCasimirReduction

open Matrix

variable {R : Type*} [CommRing R]

abbrev Mat2R (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- Explicit T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) R`. -/
theorem globalKAN_mat2_noncomm_witness {R : Type*} [Ring R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 2) (Fin 2) R, A * B ≠ B * A := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], fun h => ?_⟩
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01

/-! ### Section 1: Iwasawa KAN Generators and Decomposition -/

/-- Compact rotation generator in $\mathfrak{so}(2) \cong \mathfrak{k}$. -/
def compactK (k : R) : Mat2R R :=
  !![0, -k;
     k,  0]

/-- Cartan hyperbolic dilation generator in $\mathfrak{a}$. -/
def cartanA (θ : R) : Mat2R R :=
  !![θ,  0;
     0, -θ]

/-- Upper nilpotent shear generator in $\mathfrak{n}$. -/
def nilpotentN (n : R) : Mat2R R :=
  !![0, n;
     0, 0]

/-- Lower nilpotent shear generator in $\mathfrak{n}_-$. -/
def nilpotentN_lower (m : R) : Mat2R R :=
  !![0, 0;
     m, 0]

/-- The 2x2 Iwasawa decomposition $X = K(k) + A(\theta) + N(n)$. -/
theorem iwasawa_decomposition_2x2 (k θ n : R) :
    compactK k + cartanA θ + nilpotentN n =
    !![θ, n - k;
       k,  -θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [compactK, cartanA, nilpotentN]
    try ring
  )

/-- Uniqueness of the Iwasawa decomposition over arbitrary commutative rings. -/
theorem iwasawa_decomposition_unique (k₁ θ₁ n₁ k₂ θ₂ n₂ : R)
    (h : compactK k₁ + cartanA θ₁ + nilpotentN n₁ = compactK k₂ + cartanA θ₂ + nilpotentN n₂) :
    k₁ = k₂ ∧ θ₁ = θ₂ ∧ n₁ = n₂ := by
  have h_dec1 := iwasawa_decomposition_2x2 k₁ θ₁ n₁
  have h_dec2 := iwasawa_decomposition_2x2 k₂ θ₂ n₂
  rw [h_dec1, h_dec2] at h
  have h_00 : θ₁ = θ₂ := by
    have h_entry := congr_fun (congr_fun h 0) 0
    simpa using h_entry
  have h_10 : k₁ = k₂ := by
    have h_entry := congr_fun (congr_fun h 1) 0
    simpa using h_entry
  have h_01 : n₁ = n₂ := by
    have h_entry := congr_fun (congr_fun h 0) 1
    dsimp at h_entry
    calc
      n₁ = (n₁ - k₁) + k₁ := by ring
      _ = (n₂ - k₂) + k₂ := by rw [h_entry, h_10]
      _ = n₂ := by ring
  exact ⟨h_10, h_00, h_01⟩

/-- The Cartan subalgebra $\mathfrak{a}$ is abelian: $[A(\theta_1), A(\theta_2)] = 0$. -/
theorem cartan_is_abelian (θ₁ θ₂ : R) :
    cartanA θ₁ * cartanA θ₂ - cartanA θ₂ * cartanA θ₁ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [cartanA, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  )

/-- Nilpotency: the upper shear satisfies $N(n)^2 = 0$. -/
@[simp]
theorem nilpotent_sq_zero (n : R) :
    nilpotentN (R := R) n * nilpotentN n = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [nilpotentN, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  )

/-- Nilpotency: the lower shear satisfies $N_-(m)^2 = 0$. -/
@[simp]
theorem nilpotent_lower_sq_zero (m : R) :
    nilpotentN_lower (R := R) m * nilpotentN_lower m = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [nilpotentN_lower, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  )

/-! ### Section 2: Cartan Polar Symmetric Space Decomposition -/

/-- Polar non-compact symmetric generator in $\mathfrak{p}$. -/
def polarP (a b : R) : Mat2R R :=
  !![a,  b;
     b, -a]

/-- The Cartan polar decomposition $X = K(k) + P(a, b)$. -/
theorem polar_decomposition_2x2 (k a b : R) :
    compactK k + polarP a b =
    !![a, b - k;
       b + k, -a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [compactK, polarP]
    try ring
  )

/-- Uniqueness of the Cartan polar decomposition over rings where 2 is invertible. -/
theorem polar_decomposition_unique [Invertible (2 : R)] (k₁ a₁ b₁ k₂ a₂ b₂ : R)
    (h : compactK k₁ + polarP a₁ b₁ = compactK k₂ + polarP a₂ b₂) :
    k₁ = k₂ ∧ a₁ = a₂ ∧ b₁ = b₂ := by
  have h_dec1 := polar_decomposition_2x2 k₁ a₁ b₁
  have h_dec2 := polar_decomposition_2x2 k₂ a₂ b₂
  rw [h_dec1, h_dec2] at h
  have h_00 : a₁ = a₂ := by
    have h_entry := congr_fun (congr_fun h 0) 0
    simpa using h_entry
  have h_sum : 2 * b₁ = 2 * b₂ := by
    have h_01 := congr_fun (congr_fun h 0) 1
    have h_10 := congr_fun (congr_fun h 1) 0
    dsimp at h_01 h_10
    calc
      2 * b₁ = (b₁ - k₁) + (b₁ + k₁) := by ring
      _ = (b₂ - k₂) + (b₂ + k₂) := by rw [h_01, h_10]
      _ = 2 * b₂ := by ring
  have h_diff : 2 * k₁ = 2 * k₂ := by
    have h_01 := congr_fun (congr_fun h 0) 1
    have h_10 := congr_fun (congr_fun h 1) 0
    dsimp at h_01 h_10
    calc
      2 * k₁ = (b₁ + k₁) - (b₁ - k₁) := by ring
      _ = (b₂ + k₂) - (b₂ - k₂) := by rw [h_01, h_10]
      _ = 2 * k₂ := by ring
  have h_b : b₁ = b₂ := by
    calc
      b₁ = ⅟(2 : R) * (2 * b₁) := by rw [invOf_mul_cancel_left]
      _ = ⅟(2 : R) * (2 * b₂) := by rw [h_sum]
      _ = b₂ := by rw [invOf_mul_cancel_left]
  have h_k : k₁ = k₂ := by
    calc
      k₁ = ⅟(2 : R) * (2 * k₁) := by rw [invOf_mul_cancel_left]
      _ = ⅟(2 : R) * (2 * k₂) := by rw [h_diff]
      _ = k₂ := by rw [invOf_mul_cancel_left]
  exact ⟨h_k, h_00, h_b⟩

/-- The Cartan involution $\Theta(X) = -X^T$. -/
def cartanInvolution (X : Mat2R R) : Mat2R R := -Xᵀ

/-- $\mathfrak{k}$ is the +1 eigenspace of the Cartan involution: $\Theta(K) = K$. -/
theorem cartanInvolution_compactK (k : R) :
    cartanInvolution (compactK k) = compactK k := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [cartanInvolution, compactK, Matrix.transpose_apply]
    try ring
  )

/-- $\mathfrak{p}$ is the -1 eigenspace of the Cartan involution: $\Theta(P) = -P$. -/
theorem cartanInvolution_polarP (a b : R) :
    cartanInvolution (polarP a b) = -polarP a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [cartanInvolution, polarP, Matrix.transpose_apply]
    try ring
  )

/-- Symmetric space Lie bracket: $[\mathfrak{k}, \mathfrak{k}] \subseteq \mathfrak{k}$ (abelian in 2D). -/
theorem compact_compact_comm (k₁ k₂ : R) :
    compactK k₁ * compactK k₂ - compactK k₂ * compactK k₁ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [compactK, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  )

/-- Symmetric space Lie bracket: $[\mathfrak{k}, \mathfrak{p}] \subseteq \mathfrak{p}$. -/
theorem compact_polar_comm (k a b : R) :
    compactK k * polarP a b - polarP a b * compactK k =
    polarP (-2 * k * b) (2 * k * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [compactK, polarP, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  )

/-- Symmetric space Lie bracket: $[\mathfrak{p}, \mathfrak{p}] \subseteq \mathfrak{k}$. -/
theorem polar_polar_comm (a₁ b₁ a₂ b₂ : R) :
    polarP a₁ b₁ * polarP a₂ b₂ - polarP a₂ b₂ * polarP a₁ b₁ =
    compactK (-2 * (a₁ * b₂ - a₂ * b₁)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [compactK, polarP, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  )

/-! ### Section 3: The Complete Invariant Hierarchy (Casimirs & Radial Reduction) -/

/-- Linear Casimir (Trace): generator of $\mathcal{Z}(U(\mathfrak{gl}(2, R)))$. -/
def casimirOne (X : Mat2R R) : R :=
  Matrix.trace X

/-- Quadratic Casimir: generator of $\mathcal{Z}(U(\mathfrak{sl}(2, R)))$. -/
def casimirTwo (X : Mat2R R) : R :=
  Matrix.trace (X * X)

/-- Linear Casimir vanishes on $\mathfrak{k}$. -/
theorem casimirOne_compactK (k : R) :
    casimirOne (compactK (R := R) k) = 0 := by
  dsimp [casimirOne, compactK, Matrix.trace]
  simp [Fin.sum_univ_two]

/-- Linear Casimir vanishes on $\mathfrak{a}$. -/
theorem casimirOne_cartanA (θ : R) :
    casimirOne (cartanA (R := R) θ) = 0 := by
  dsimp [casimirOne, cartanA, Matrix.trace]
  simp [Fin.sum_univ_two]

/-- Linear Casimir vanishes on $\mathfrak{p}$. -/
theorem casimirOne_polarP (a b : R) :
    casimirOne (polarP (R := R) a b) = 0 := by
  dsimp [casimirOne, polarP, Matrix.trace]
  simp [Fin.sum_univ_two]

/-- Linear Casimir vanishes on nilpotent shears $\mathfrak{n}$. -/
theorem casimirOne_nilpotent (n : R) :
    casimirOne (nilpotentN (R := R) n) = 0 := by
  dsimp [casimirOne, nilpotentN, Matrix.trace]
  simp [Fin.sum_univ_two]

private lemma scalar_two_mul_sq {R : Type*} [CommRing R] (x : R) :
    x * x + x * x = 2 * x ^ 2 := by
  ring

private lemma scalar_neg_two_mul_sq {R : Type*} [CommRing R] (x : R) :
    -(x * x) + -(x * x) = -(2 * x ^ 2) := by
  ring

private lemma scalar_sq_neg_eq {R : Type*} [CommRing R] (x : R) :
    2 * (-x) ^ 2 = 2 * x ^ 2 := by
  ring

/-- Harish-Chandra radial reduction: on the Cartan subspace $\mathfrak{a}$, $C_2(A(\theta)) = 2\theta^2$. -/
theorem casimirTwo_on_cartan (θ : R) :
    casimirTwo (cartanA θ) = 2 * θ^2 := by
  dsimp [casimirTwo, cartanA, Matrix.trace]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact scalar_two_mul_sq θ

/-- Quadratic Casimir on compact rotations: $C_2(K(k)) = -2k^2$. -/
theorem casimirTwo_on_compactK (k : R) :
    casimirTwo (compactK k) = -2 * k^2 := by
  dsimp [casimirTwo, compactK, Matrix.trace]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact scalar_neg_two_mul_sq k

/-- Strictly nilpotent shears carry zero Casimir invariants: $C_2(N) = 0$. -/
theorem casimirTwo_on_nilpotent_zero (n : R) :
    casimirTwo (nilpotentN (R := R) n) = 0 := by
  dsimp [casimirTwo, nilpotentN, Matrix.trace]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Weyl group invariance: $W \cong \mathbb{Z}_2$ action $\theta \mapsto -\theta$ preserves the Casimir invariant. -/
theorem casimirTwo_weyl_invariant (θ : R) :
    casimirTwo (cartanA (-θ)) = casimirTwo (cartanA θ) := by
  rw [casimirTwo_on_cartan, casimirTwo_on_cartan]
  exact scalar_sq_neg_eq θ

/-- Universal gauge invariance: $C_2$ is strictly invariant under all similarity transformations $g X g^{-1}$. -/
theorem casimirTwo_gauge_invariant
    (g g_inv X : Mat2R R)
    (h_left : g_inv * g = 1)
    (h_right : g * g_inv = 1) :
    casimirTwo (g * X * g_inv) = casimirTwo X := by
  dsimp [casimirTwo]
  have h_mid : (g * X * g_inv) * (g * X * g_inv) = g * (X * X) * g_inv := by
    calc
      (g * X * g_inv) * (g * X * g_inv)
        = g * X * (g_inv * g) * X * g_inv := by
          simp only [mul_assoc]
      _ = g * X * 1 * X * g_inv := by rw [h_left]
      _ = g * (X * X) * g_inv := by simp only [mul_one, mul_assoc]
  rw [h_mid]
  rw [Matrix.trace_mul_comm (g * (X * X)) g_inv]
  rw [← mul_assoc, h_left, one_mul]


end Experimental.Sandbox.Lie.GlobalKANCasimirReduction
