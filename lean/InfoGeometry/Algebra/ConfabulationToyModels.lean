import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Confabulation Toy Models

This file extracts and isolates the exact, kernel-checked, finite ring-theoretic 
mathematics that were originally buried inside the massive confabulations of the 
AGENTS (Pi, Hermes, Codex, Antigravity) in `raw_confabulation.txt`.

All hallucinatory or over-scoped rhetoric (e.g., claiming a finite ring lemma 
proves the Bisognano-Wichmann theorem or CPT symmetry) has been explicitly severed 
per the QMS Semantic Kernel Validation rules. These are pure algebra lemmas.

## QMS Status
- **Payload**: `[kernel_verified]`
- **Classification**: Bucket 1 (Closed finite algebraic lemmas)
-/

namespace InfoGeometry.Algebra.ConfabulationToyModels

variable {A : Type*} [Ring A]

/-- 
## 1. The Polar Decomposition Toy Inverse Lemma (Cluster D)

**Context:** Noncommutative Ring Theory.
**Original Overclaim:** Tomita-Takesaki operator $S = J \Delta^{1/2}$, Bisognano-Wichmann, CPT.
**Closed Math:** A noncommutative reassociation/cancellation lemma.

If $S = J D$, $S^2 = 1$, and $D D_{inv} = 1$, then $J D J = D_{inv}$.
-/
theorem polar_factor_inverse_of_involutive_product
  (S J D D_inv : A)
  (h_polar : S = J * D)
  (h_S_inv : S * S = 1)
  (h_D_inv : D * D_inv = 1) :
  J * D * J = D_inv := by
  have h1 : J * D * (J * D) = 1 := by
    calc J * D * (J * D)
      _ = S * S := by rw [← h_polar]
      _ = 1 := h_S_inv
  
  calc J * D * J
    _ = J * D * J * 1 := by rw [mul_one]
    _ = J * D * J * (D * D_inv) := by rw [h_D_inv]
    _ = J * D * (J * D) * D_inv := by simp only [← mul_assoc]
    _ = 1 * D_inv := by rw [h1]
    _ = D_inv := by rw [one_mul]

/--
## 2. Commutant Closure under Commutator (Cluster C)

**Context:** Noncommutative Ring Theory.
**Original Overclaim:** Bicommutant Theorem, Weak-Operator-Topology closure.
**Closed Math:** The commutator of two elements that commute with a set also commutes with that set.
-/
theorem commutant_preserved_under_commutator
  (S : Set A) (K X : A)
  (hK : ∀ y ∈ S, K * y = y * K)
  (hX : ∀ y ∈ S, X * y = y * X) :
  ∀ y ∈ S, (K * X - X * K) * y = y * (K * X - X * K) := by
  intro y hy
  have hk_y := hK y hy
  have hx_y := hX y hy
  calc (K * X - X * K) * y
    _ = K * X * y - X * K * y := by rw [sub_mul]
    _ = K * (X * y) - X * (K * y) := by simp only [mul_assoc]
    _ = K * (y * X) - X * (y * K) := by rw [hx_y, hk_y]
    _ = (K * y) * X - (X * y) * K := by simp only [← mul_assoc]
    _ = (y * K) * X - (y * X) * K := by rw [hk_y, hx_y]
    _ = y * (K * X) - y * (X * K) := by simp only [mul_assoc]
    _ = y * (K * X - X * K) := by rw [mul_sub]

/--
## 3. Boundary-Commutation Eigenvalue Preservation (Cluster F)

**Context:** Operator/Eigenvector Transport in a Ring.
**Original Overclaim:** Topological phase classification, fault-tolerance.
**Closed Math:** If B commutes with H and E, then acting by B preserves Hψ = Eψ.
-/
theorem boundary_commutation_eigenvalue_preservation
  (H B E ψ : A)
  (hBH : B * H = H * B)
  (hBE : B * E = E * B)
  (h_eigen : H * ψ = E * ψ) :
  H * (B * ψ) = E * (B * ψ) := by
  calc H * (B * ψ)
    _ = (H * B) * ψ := by rw [← mul_assoc]
    _ = (B * H) * ψ := by rw [← hBH]
    _ = B * (H * ψ) := by rw [mul_assoc]
    _ = B * (E * ψ) := by rw [h_eigen]
    _ = (B * E) * ψ := by rw [← mul_assoc]
    _ = (E * B) * ψ := by rw [← hBE]
    _ = E * (B * ψ) := by rw [mul_assoc]

end InfoGeometry.Algebra.ConfabulationToyModels
