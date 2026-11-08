/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing

/-!
# Chern–Simons Temperley–Lieb Algebra, Kauffman Skein Relation, & Yang–Baxter Braiding

Target: `InfoGeometry/Topology/ChernSimonsTemperleyLiebYangBaxter.lean`

This module epistemically compiles Wave 17 Partition P3 from
`1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or` (Turn 323) over an arbitrary non-commutative
ring `M` (`[Ring M]`):

1. **Kauffman Braid Generators & Inverses (`kauffmanBraid`, `kauffmanBraidInv`):**
   - Given a Temperley–Lieb generator $e_i \in M$ satisfying
     $e_i^2 = (-A^2 - A^{-2}) e_i$ and central Kauffman phase $A, A^{-1} \in M$
     satisfying $A A^{-1} = A^{-1} A = 1$, defines the forward crossing
     $B_i = A + A^{-1} e_i$ and inverse crossing $B_i^{-1} = A^{-1} + A e_i$.
2. **Reidemeister Move II (Two-Sided Unitarity) & Kauffman Skein Relation:**
   - Proves $B_i B_i^{-1} = 1$ and $B_i^{-1} B_i = 1$
     (`kauffmanBraid_reidemeister_two_unitarity`), together with the linear
     skein identity $A B_i - A^{-1} B_i^{-1} = (A^2 - A^{-2})\cdot 1$
     (`kauffmanBraid_linear_skein_identity`).
3. **Reidemeister Move III / Yang–Baxter Equation (`chern_simons_temperley_lieb_yang_baxter`):**
   - Reduces both $B_1 B_2 B_1$ and $B_2 B_1 B_2$ to the canonical symmetric
     polynomial $A^3 + A e_1 + A e_2 + A^{-1}(e_1 e_2 + e_2 e_1)$ using
     $e_1 e_2 e_1 = e_1$ and $e_2 e_1 e_2 = e_2$, proving
     $$B_1 B_2 B_1 = B_2 B_1 B_2.$$

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Non-Commutative Braid Theorems (`[kernel_verified]`):**
  - `kauffmanBraid_reidemeister_two_unitarity`, `kauffmanBraid_linear_skein_identity`,
    `kauffmanBraid_121_eq_symmetric`, `kauffmanBraid_212_eq_symmetric`, and
    `chern_simons_temperley_lieb_yang_baxter`.
* **BUCKET 2 — Eliminated Certificate Wrappers (Zero Remaining):**
  - `ChernSimonsYangBaxterCertificate : Prop` from Turn 323 is eliminated.
* **BUCKET 3 — 3-Manifold Reshetikhin–Turaev Surgery Invariants (`[bucket_3_open_debt]`):**
  - Root-of-unity modular tensor category truncations and Kirby-calculus Dehn surgery
    sums over 3-manifolds remain outside this non-commutative ring presentation.
-/

namespace InfoGeometry.Topology.ChernSimons

variable {M : Type*} [Ring M]

/-- Positive Kauffman braid crossing generator $B_i = A + A^{-1} e_i$ in `M`. -/
def kauffmanBraid (A A_inv e : M) : M :=
  A + A_inv * e

/-- Negative (inverse) Kauffman braid crossing generator $B_i^{-1} = A^{-1} + A e_i$ in `M`. -/
def kauffmanBraidInv (A A_inv e : M) : M :=
  A_inv + A * e

/-- Canonical symmetric 3-strand polynomial
$$P_{\mathrm{sym}}(A, A^{-1}, e_1, e_2) = A^3 + A e_1 + A e_2 + A^{-1}(e_1 e_2 + e_2 e_1).$$ -/
def symmetricBraidPoly (A A_inv e₁ e₂ : M) : M :=
  A * A * A + A * e₁ + A * e₂ + A_inv * (e₁ * e₂ + e₂ * e₁)

/-- **Reidemeister Move II — Two-Sided Unitarity of Kauffman Braid Generators
(`kauffmanBraid_reidemeister_two_unitarity`):**
In any non-commutative ring `M`, if $A A^{-1} = 1$, $A_inv A = 1$, $A$ and $A^{-1}$
commute with $e$, and $e^2 = (-A^2 - A^{-2}) e$, then:
$$B_i B_i^{-1} = 1 \quad\text{and}\quad B_i^{-1} B_i = 1.$$ -/
theorem kauffmanBraid_reidemeister_two_unitarity (A A_inv e : M)
    (h_inv : A * A_inv = 1)
    (h_inv2 : A_inv * A = 1)
    (h_comm_A : ∀ x : M, A * x = x * A)
    (h_comm_A_inv : ∀ x : M, A_inv * x = x * A_inv)
    (he_sq : e * e = (-(A * A) - A_inv * A_inv) * e) :
    kauffmanBraid A A_inv e * kauffmanBraidInv A A_inv e = 1 ∧
    kauffmanBraidInv A A_inv e * kauffmanBraid A A_inv e = 1 := by
  unfold kauffmanBraid kauffmanBraidInv
  have hAe : (A_inv * e) * (A * e) = -(A * A) * e - (A_inv * A_inv) * e := by
    calc (A_inv * e) * (A * e)
      _ = A_inv * (e * A) * e := by noncomm_ring
      _ = A_inv * (A * e) * e := by rw [← h_comm_A e]
      _ = (A_inv * A) * (e * e) := by noncomm_ring
      _ = 1 * (e * e) := by rw [h_inv2]
      _ = e * e := by noncomm_ring
      _ = (-(A * A) - A_inv * A_inv) * e := by rw [he_sq]
      _ = -(A * A) * e - (A_inv * A_inv) * e := by noncomm_ring
  have hEA : (A * e) * (A_inv * e) = -(A * A) * e - (A_inv * A_inv) * e := by
    calc (A * e) * (A_inv * e)
      _ = A * (e * A_inv) * e := by noncomm_ring
      _ = A * (A_inv * e) * e := by rw [← h_comm_A_inv e]
      _ = (A * A_inv) * (e * e) := by noncomm_ring
      _ = 1 * (e * e) := by rw [h_inv]
      _ = e * e := by noncomm_ring
      _ = (-(A * A) - A_inv * A_inv) * e := by rw [he_sq]
      _ = -(A * A) * e - (A_inv * A_inv) * e := by noncomm_ring
  refine ⟨?_, ?_⟩
  · calc (A + A_inv * e) * (A_inv + A * e)
      _ = A * A_inv + (A * A) * e + A_inv * (e * A_inv) + (A_inv * e) * (A * e) := by
        noncomm_ring
      _ = 1 + (A * A) * e + A_inv * (A_inv * e) + (-(A * A) * e - (A_inv * A_inv) * e) := by
        rw [h_inv, ← h_comm_A_inv e, hAe]
      _ = 1 := by noncomm_ring
  · calc (A_inv + A * e) * (A + A_inv * e)
      _ = A_inv * A + (A_inv * A_inv) * e + A * (e * A) + (A * e) * (A_inv * e) := by
        noncomm_ring
      _ = 1 + (A_inv * A_inv) * e + A * (A * e) + (-(A * A) * e - (A_inv * A_inv) * e) := by
        rw [h_inv2, ← h_comm_A e, hEA]
      _ = 1 := by noncomm_ring

/-- **Kauffman Linear Skein Relation (`kauffmanBraid_linear_skein_identity`):**
Whenever $A$ and $A^{-1}$ are mutual inverses ($A A^{-1} = A^{-1} A = 1$), the weighted
difference of the positive and negative braid generators eliminates the Temperley–Lieb
projector $e$ identically:
$$A \cdot B_i - A^{-1} \cdot B_i^{-1} = A^2 - A^{-2}.$$ -/
theorem kauffmanBraid_linear_skein_identity (A A_inv e : M)
    (h_inv : A * A_inv = 1)
    (h_inv2 : A_inv * A = 1) :
    A * kauffmanBraid A A_inv e - A_inv * kauffmanBraidInv A A_inv e =
      A * A - A_inv * A_inv := by
  unfold kauffmanBraid kauffmanBraidInv
  calc A * (A + A_inv * e) - A_inv * (A_inv + A * e)
    _ = A * A - A_inv * A_inv + (A * A_inv) * e - (A_inv * A) * e := by noncomm_ring
    _ = A * A - A_inv * A_inv + 1 * e - 1 * e := by rw [h_inv, h_inv2]
    _ = A * A - A_inv * A_inv := by noncomm_ring

/-- Eight-term non-commutative binomial cube expansion $(a + b)(c + d)(e + f)$ in `M`. -/
lemma dist3 (a b c d e f : M) :
    (a + b) * (c + d) * (e + f) =
      a * c * e + a * c * f + a * d * e + a * d * f +
      b * c * e + b * c * f + b * d * e + b * d * f := by
  noncomm_ring

/-- **Reduction of $B_1 B_2 B_1$ to `symmetricBraidPoly` (`kauffmanBraid_121_eq_symmetric`):**
If $e_1^2 = (-A^2 - A^{-2}) e_1$ and $e_1 e_2 e_1 = e_1$, then
$B_1 B_2 B_1 = A^3 + A e_1 + A e_2 + A^{-1}(e_1 e_2 + e_2 e_1)$. -/
theorem kauffmanBraid_121_eq_symmetric (A A_inv e₁ e₂ : M)
    (h_inv : A * A_inv = 1)
    (h_inv2 : A_inv * A = 1)
    (h_comm_A : ∀ x : M, A * x = x * A)
    (h_comm_A_inv : ∀ x : M, A_inv * x = x * A_inv)
    (he₁_sq : e₁ * e₁ = (-(A * A) - A_inv * A_inv) * e₁)
    (he₁₂₁ : e₁ * e₂ * e₁ = e₁) :
    kauffmanBraid A A_inv e₁ * kauffmanBraid A A_inv e₂ * kauffmanBraid A A_inv e₁ =
      symmetricBraidPoly A A_inv e₁ e₂ := by
  unfold kauffmanBraid symmetricBraidPoly
  rw [dist3]
  have t2 : A * A * (A_inv * e₁) = A * e₁ := by
    calc A * A * (A_inv * e₁)
      _ = A * (A * A_inv) * e₁ := by noncomm_ring
      _ = A * 1 * e₁ := by rw [h_inv]
      _ = A * e₁ := by noncomm_ring
  have t3 : A * (A_inv * e₂) * A = A * e₂ := by
    calc A * (A_inv * e₂) * A
      _ = (A * A_inv) * (e₂ * A) := by noncomm_ring
      _ = 1 * (e₂ * A) := by rw [h_inv]
      _ = e₂ * A := by noncomm_ring
      _ = A * e₂ := by rw [← h_comm_A e₂]
  have t4 : A * (A_inv * e₂) * (A_inv * e₁) = A_inv * (e₂ * e₁) := by
    calc A * (A_inv * e₂) * (A_inv * e₁)
      _ = (A * A_inv) * (e₂ * A_inv) * e₁ := by noncomm_ring
      _ = 1 * (e₂ * A_inv) * e₁ := by rw [h_inv]
      _ = (e₂ * A_inv) * e₁ := by noncomm_ring
      _ = (A_inv * e₂) * e₁ := by rw [← h_comm_A_inv e₂]
      _ = A_inv * (e₂ * e₁) := by noncomm_ring
  have t5 : (A_inv * e₁) * A * A = A * e₁ := by
    calc (A_inv * e₁) * A * A
      _ = A_inv * (e₁ * A) * A := by noncomm_ring
      _ = A_inv * (A * e₁) * A := by rw [← h_comm_A e₁]
      _ = (A_inv * A) * (e₁ * A) := by noncomm_ring
      _ = 1 * (e₁ * A) := by rw [h_inv2]
      _ = e₁ * A := by noncomm_ring
      _ = A * e₁ := by rw [← h_comm_A e₁]
  have t6 : (A_inv * e₁) * A * (A_inv * e₁) =
      - A * e₁ - (A_inv * A_inv * A_inv) * e₁ := by
    calc (A_inv * e₁) * A * (A_inv * e₁)
      _ = A_inv * (e₁ * A) * (A_inv * e₁) := by noncomm_ring
      _ = A_inv * (A * e₁) * (A_inv * e₁) := by rw [← h_comm_A e₁]
      _ = (A_inv * A) * (e₁ * A_inv) * e₁ := by noncomm_ring
      _ = 1 * (e₁ * A_inv) * e₁ := by rw [h_inv2]
      _ = (e₁ * A_inv) * e₁ := by noncomm_ring
      _ = (A_inv * e₁) * e₁ := by rw [← h_comm_A_inv e₁]
      _ = A_inv * (e₁ * e₁) := by noncomm_ring
      _ = A_inv * ((-(A * A) - A_inv * A_inv) * e₁) := by rw [he₁_sq]
      _ = - (A_inv * A) * A * e₁ - (A_inv * A_inv * A_inv) * e₁ := by noncomm_ring
      _ = - 1 * A * e₁ - (A_inv * A_inv * A_inv) * e₁ := by rw [h_inv2]
      _ = - A * e₁ - (A_inv * A_inv * A_inv) * e₁ := by noncomm_ring
  have t7 : (A_inv * e₁) * (A_inv * e₂) * A = A_inv * (e₁ * e₂) := by
    calc (A_inv * e₁) * (A_inv * e₂) * A
      _ = A_inv * (e₁ * A_inv) * (e₂ * A) := by noncomm_ring
      _ = A_inv * (A_inv * e₁) * (A * e₂) := by rw [← h_comm_A_inv e₁, ← h_comm_A e₂]
      _ = A_inv * A_inv * (e₁ * A) * e₂ := by noncomm_ring
      _ = A_inv * A_inv * (A * e₁) * e₂ := by rw [← h_comm_A e₁]
      _ = A_inv * (A_inv * A) * (e₁ * e₂) := by noncomm_ring
      _ = A_inv * 1 * (e₁ * e₂) := by rw [h_inv2]
      _ = A_inv * (e₁ * e₂) := by noncomm_ring
  have t8 : (A_inv * e₁) * (A_inv * e₂) * (A_inv * e₁) =
      (A_inv * A_inv * A_inv) * e₁ := by
    calc (A_inv * e₁) * (A_inv * e₂) * (A_inv * e₁)
      _ = A_inv * (e₁ * A_inv) * (e₂ * A_inv) * e₁ := by noncomm_ring
      _ = A_inv * (A_inv * e₁) * (A_inv * e₂) * e₁ := by
        rw [← h_comm_A_inv e₁, ← h_comm_A_inv e₂]
      _ = A_inv * A_inv * (e₁ * A_inv) * e₂ * e₁ := by noncomm_ring
      _ = A_inv * A_inv * (A_inv * e₁) * e₂ * e₁ := by rw [← h_comm_A_inv e₁]
      _ = (A_inv * A_inv * A_inv) * (e₁ * e₂ * e₁) := by noncomm_ring
      _ = (A_inv * A_inv * A_inv) * e₁ := by rw [he₁₂₁]
  rw [t2, t3, t4, t5, t6, t7, t8]
  noncomm_ring

/-- **Reduction of $B_2 B_1 B_2$ to `symmetricBraidPoly` (`kauffmanBraid_212_eq_symmetric`):**
By index symmetry $(e_1 \leftrightarrow e_2)$, if $e_2^2 = (-A^2 - A^{-2}) e_2$ and
$e_2 e_1 e_2 = e_2$, then $B_2 B_1 B_2 = A^3 + A e_1 + A e_2 + A^{-1}(e_1 e_2 + e_2 e_1)$. -/
theorem kauffmanBraid_212_eq_symmetric (A A_inv e₁ e₂ : M)
    (h_inv : A * A_inv = 1)
    (h_inv2 : A_inv * A = 1)
    (h_comm_A : ∀ x : M, A * x = x * A)
    (h_comm_A_inv : ∀ x : M, A_inv * x = x * A_inv)
    (he₂_sq : e₂ * e₂ = (-(A * A) - A_inv * A_inv) * e₂)
    (he₂₁₂ : e₂ * e₁ * e₂ = e₂) :
    kauffmanBraid A A_inv e₂ * kauffmanBraid A A_inv e₁ * kauffmanBraid A A_inv e₂ =
      symmetricBraidPoly A A_inv e₁ e₂ := by
  rw [kauffmanBraid_121_eq_symmetric A A_inv e₂ e₁ h_inv h_inv2 h_comm_A h_comm_A_inv he₂_sq he₂₁₂]
  unfold symmetricBraidPoly
  noncomm_ring

/-- **Reidemeister Move III / Yang–Baxter Braid Theorem (`chern_simons_temperley_lieb_yang_baxter`):**
In any non-commutative ring `M`, if $e_1, e_2 \in M$ satisfy the Temperley–Lieb loop
and absorption relations with central Kauffman phase $A, A^{-1} \in M$, then:
$$B_1 B_2 B_1 = B_2 B_1 B_2.$$ -/
theorem chern_simons_temperley_lieb_yang_baxter (A A_inv e₁ e₂ : M)
    (h_inv : A * A_inv = 1)
    (h_inv2 : A_inv * A = 1)
    (h_comm_A : ∀ x : M, A * x = x * A)
    (h_comm_A_inv : ∀ x : M, A_inv * x = x * A_inv)
    (he₁_sq : e₁ * e₁ = (-(A * A) - A_inv * A_inv) * e₁)
    (he₂_sq : e₂ * e₂ = (-(A * A) - A_inv * A_inv) * e₂)
    (he₁₂₁ : e₁ * e₂ * e₁ = e₁)
    (he₂₁₂ : e₂ * e₁ * e₂ = e₂) :
    kauffmanBraid A A_inv e₁ * kauffmanBraid A A_inv e₂ * kauffmanBraid A A_inv e₁ =
      kauffmanBraid A A_inv e₂ * kauffmanBraid A A_inv e₁ * kauffmanBraid A A_inv e₂ := by
  rw [kauffmanBraid_121_eq_symmetric A A_inv e₁ e₂ h_inv h_inv2 h_comm_A h_comm_A_inv he₁_sq he₁₂₁,
      kauffmanBraid_212_eq_symmetric A A_inv e₁ e₂ h_inv h_inv2 h_comm_A h_comm_A_inv he₂_sq he₂₁₂]

end InfoGeometry.Topology.ChernSimons
