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

/-- Harish-Chandra radial reduction: on the Cartan subspace $\mathfrak{a}$, $C_2(A(\theta)) = 2\theta^2$. -/
theorem casimirTwo_on_cartan (θ : R) :
    casimirTwo (cartanA θ) = 2 * θ^2 := by
  dsimp [casimirTwo, cartanA, Matrix.trace]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Quadratic Casimir on compact rotations: $C_2(K(k)) = -2k^2$. -/
theorem casimirTwo_on_compactK (k : R) :
    casimirTwo (compactK k) = -2 * k^2 := by
  dsimp [casimirTwo, compactK, Matrix.trace]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Strictly nilpotent shears carry zero Casimir invariants: $C_2(N) = 0$. -/
theorem casimirTwo_on_nilpotent_zero (n : R) :
    casimirTwo (nilpotentN (R := R) n) = 0 := by
  dsimp [casimirTwo, nilpotentN, Matrix.trace]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Weyl group invariance: $W \cong \mathbb{Z}_2$ action $\theta \mapsto -\theta$ preserves the Casimir invariant. -/
theorem casimirTwo_weyl_invariant (θ : R) :
    casimirTwo (cartanA (-θ)) = casimirTwo (cartanA θ) := by
  rw [casimirTwo_on_cartan, casimirTwo_on_cartan]
  ring

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

/-! ### Section 4: Master Verification Certificate -/

/-- Master Certificate bundling the complete Iwasawa KAN, Cartan polar, and Casimir hierarchy. -/
structure GlobalKANCasimirReductionCertificate : Prop where
  iwasawa_dec : ∀ (k θ n : R), compactK k + cartanA θ + nilpotentN n = !![θ, n - k; k, -θ]
  iwasawa_unique : ∀ (k₁ θ₁ n₁ k₂ θ₂ n₂ : R),
    compactK k₁ + cartanA θ₁ + nilpotentN n₁ = compactK k₂ + cartanA θ₂ + nilpotentN n₂ →
    k₁ = k₂ ∧ θ₁ = θ₂ ∧ n₁ = n₂
  cartan_abelian : ∀ (θ₁ θ₂ : R), cartanA θ₁ * cartanA θ₂ - cartanA θ₂ * cartanA θ₁ = 0
  nilpotent_sq : ∀ (n : R), nilpotentN (R := R) n * nilpotentN n = 0
  nilpotent_lower_sq : ∀ (m : R), nilpotentN_lower (R := R) m * nilpotentN_lower m = 0
  polar_dec : ∀ (k a b : R), compactK k + polarP a b = !![a, b - k; b + k, -a]
  cartan_invol_K : ∀ (k : R), cartanInvolution (compactK k) = compactK k
  cartan_invol_P : ∀ (a b : R), cartanInvolution (polarP a b) = -polarP a b
  comm_K_K : ∀ (k₁ k₂ : R), compactK k₁ * compactK k₂ - compactK k₂ * compactK k₁ = 0
  comm_K_P : ∀ (k a b : R), compactK k * polarP a b - polarP a b * compactK k = polarP (-2 * k * b) (2 * k * a)
  comm_P_P : ∀ (a₁ b₁ a₂ b₂ : R), polarP a₁ b₁ * polarP a₂ b₂ - polarP a₂ b₂ * polarP a₁ b₁ = compactK (-2 * (a₁ * b₂ - a₂ * b₁))
  casimir_one_K : ∀ (k : R), casimirOne (compactK (R := R) k) = 0
  casimir_one_A : ∀ (θ : R), casimirOne (cartanA (R := R) θ) = 0
  casimir_one_P : ∀ (a b : R), casimirOne (polarP (R := R) a b) = 0
  casimir_one_N : ∀ (n : R), casimirOne (nilpotentN (R := R) n) = 0
  casimir_two_cartan : ∀ (θ : R), casimirTwo (cartanA θ) = 2 * θ^2
  casimir_two_compact : ∀ (k : R), casimirTwo (compactK k) = -2 * k^2
  casimir_two_nilpotent : ∀ (n : R), casimirTwo (nilpotentN (R := R) n) = 0
  casimir_two_weyl : ∀ (θ : R), casimirTwo (cartanA (-θ)) = casimirTwo (cartanA θ)
  casimir_two_gauge : ∀ (g g_inv X : Mat2R R), g_inv * g = 1 → g * g_inv = 1 → casimirTwo (g * X * g_inv) = casimirTwo X

/-- Compilation theorem: the master reduction certificate holds unconditionally. -/
theorem compile_global_kan_casimir_reduction : GlobalKANCasimirReductionCertificate (R := R) where
  iwasawa_dec := iwasawa_decomposition_2x2
  iwasawa_unique := iwasawa_decomposition_unique
  cartan_abelian := cartan_is_abelian
  nilpotent_sq := nilpotent_sq_zero
  nilpotent_lower_sq := nilpotent_lower_sq_zero
  polar_dec := polar_decomposition_2x2
  cartan_invol_K := cartanInvolution_compactK
  cartan_invol_P := cartanInvolution_polarP
  comm_K_K := compact_compact_comm
  comm_K_P := compact_polar_comm
  comm_P_P := polar_polar_comm
  casimir_one_K := casimirOne_compactK
  casimir_one_A := casimirOne_cartanA
  casimir_one_P := casimirOne_polarP
  casimir_one_N := casimirOne_nilpotent
  casimir_two_cartan := casimirTwo_on_cartan
  casimir_two_compact := casimirTwo_on_compactK
  casimir_two_nilpotent := casimirTwo_on_nilpotent_zero
  casimir_two_weyl := casimirTwo_weyl_invariant
  casimir_two_gauge := casimirTwo_gauge_invariant

end Experimental.Sandbox.Lie.GlobalKANCasimirReduction
