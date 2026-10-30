/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition

/-!
# Graded Endomorphism Propagation along Sequential Inductive Towers

This module formalizes the propagation of a 5-component family of commuting
linear endomorphisms along a sequential inductive tower of $R$-modules with a
compatible target cocone.

## Mathematical Content

Given a sequence of $R$-modules $A_n$, bonding homomorphisms $\iota_n : A_n \toₗ[R] A_{n+1}$,
and endomorphisms $\Pi_k^{(n)} \in \operatorname{End}_R(A_n)$ indexed by $k \in \text{FiveGrade}$
satisfying the intertwining relation $\Pi_k^{(n+1)} \circ \iota_n = \iota_n \circ \Pi_k^{(n)}$:

1. **Multi-Step Intertwining**:
   $\Pi_k^{(n+m)} \circ \iota^{(n, m)} = \iota^{(n, m)} \circ \Pi_k^{(n)}$ for all $m \in \mathbb{N}$.
2. **Grade Invariant Subspace Survival**:
   If $\Pi_k^{(n)} x = x$, then $\Pi_k^{(n+m)}(\iota^{(n, m)} x) = \iota^{(n, m)} x$.
3. **Orthogonal Annihilation Preservation**:
   If $\Pi_k^{(n)} x = 0$, then $\Pi_k^{(n+m)}(\iota^{(n, m)} x) = 0$.
4. **Idempotence & Orthogonality Preservation on Tower Image**:
   If $\Pi_k^{(n)}$ is idempotent at stage $n$, it acts idempotently on the image of $\iota^{(n, m)}$.
   If $\Pi_i^{(n)} \circ \Pi_j^{(n)} = 0$, the composition vanishes on the image of $\iota^{(n, m)}$.
5. **Cocone Linear Evaluation**:
   Evaluation of a compatible target cocone $\psi_n : A_n \toₗ[R] A_\infty$ on a sum of components.
6. **Graded Trace Invariance**:
   Trace functionals $\psi_{\text{trace}} : A_\infty \to R$ evaluate identically across tower steps.
-/

namespace InfoGeometry.Canonical.ColimitFiveGrading

open InfoGeometry.Physics.Algebra

universe u v

variable {R : Type u} [CommRing R]
variable (A : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (iota : ∀ n, A n →ₗ[R] A (n + 1))
variable (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf]
variable (psi : ∀ n, A n →ₗ[R] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)

/-! ### 1. Commuting Graded Endomorphisms -/

variable (proj : ∀ n, FiveGrade → (A n →ₗ[R] A n))
variable (proj_comm : ∀ n k, (proj (n + 1) k).comp (iota n) = (iota n).comp (proj n k))

include proj_comm

/-- **Theorem 1: Multi-Step Intertwining Law**
    The multi-step transition map $\iota^{(n, m)} : A_n \to A_{n+m}$ commutes
    with the graded endomorphisms for every step count $m \in \mathbb{N}$ and
    every grade $k \in \text{FiveGrade}$. -/
theorem iota_seq_proj_comm (n : ℕ) (k : FiveGrade) :
    ∀ m, (proj (n + m) k).comp (iota_seq A iota n m) =
         (iota_seq A iota n m).comp (proj n k)
  | 0 => by
    dsimp [iota_seq]
  | m + 1 => by
    change (proj (n + (m + 1)) k).comp
        ((iota (n + m)).comp (iota_seq A iota n m)) =
      ((iota (n + m)).comp (iota_seq A iota n m)).comp (proj n k)
    rw [← LinearMap.comp_assoc]
    have h_step : (proj (n + (m + 1)) k).comp (iota (n + m)) =
                  (iota (n + m)).comp (proj (n + m) k) := by
      simpa only [Nat.add_succ] using proj_comm (n + m) k
    rw [h_step]
    rw [LinearMap.comp_assoc]
    rw [iota_seq_proj_comm n k m]
    rw [← LinearMap.comp_assoc]

/-- Elementwise multi-step intertwining:
    $$\Pi_k^{(n+m)}(\iota^{(n, m)} x) = \iota^{(n, m)}(\Pi_k^{(n)} x)$$ -/
theorem iota_seq_proj_apply (n m : ℕ) (k : FiveGrade) (x : A n) :
    proj (n + m) k (iota_seq A iota n m x) =
    iota_seq A iota n m (proj n k x) := by
  have h := iota_seq_proj_comm A iota proj proj_comm n k m
  exact LinearMap.congr_fun h x

/-- **Theorem 2: Grade Invariant Survival Along the Tower**
    An element $x \in A_n$ invariant under $\Pi_k^{(n)}$ ($\Pi_k^{(n)} x = x$)
    has an invariant transition image under $\Pi_k^{(n+m)}$. -/
theorem grade_survival (n m : ℕ) (k : FiveGrade) (x : A n)
    (hx : proj n k x = x) :
    proj (n + m) k (iota_seq A iota n m x) = iota_seq A iota n m x := by
  rw [iota_seq_proj_apply A iota proj proj_comm n m k x, hx]

/-- **Theorem 3: Orthogonal Annihilation Along the Tower**
    An element $x \in A_n$ annihilated by $\Pi_k^{(n)}$ ($\Pi_k^{(n)} x = 0$)
    has its transition image annihilated by $\Pi_k^{(n+m)}$. -/
theorem orthogonal_annihilation (n m : ℕ) (k : FiveGrade) (x : A n)
    (hx : proj n k x = 0) :
    proj (n + m) k (iota_seq A iota n m x) = 0 := by
  rw [iota_seq_proj_apply A iota proj proj_comm n m k x, hx, map_zero]

/-- **Theorem 4: Idempotence Preservation on Transition Image**
    If $\Pi_k^{(n)}$ is idempotent at stage $n$, then $\Pi_k^{(n+m)}$ acts
    idempotently on the image of $\iota^{(n, m)}$. -/
theorem idempotence_preservation_on_image (n m : ℕ) (k : FiveGrade) (x : A n)
    (hidem : (proj n k).comp (proj n k) = proj n k) :
    proj (n + m) k (proj (n + m) k (iota_seq A iota n m x)) =
    proj (n + m) k (iota_seq A iota n m x) := by
  rw [iota_seq_proj_apply A iota proj proj_comm n m k x]
  rw [iota_seq_proj_apply A iota proj proj_comm n m k (proj n k x)]
  have h : proj n k (proj n k x) = proj n k x := LinearMap.congr_fun hidem x
  rw [h]

/-- **Theorem 5: Pairwise Annihilation Preservation on Transition Image**
    If two graded endomorphisms are orthogonal at stage $n$ ($\Pi_i^{(n)} \circ \Pi_j^{(n)} = 0$),
    their composition vanishes on the image of $\iota^{(n, m)}$. -/
theorem orthogonality_preservation_on_image (n m : ℕ) (i j : FiveGrade) (x : A n)
    (hortho : (proj n i).comp (proj n j) = 0) :
    proj (n + m) i (proj (n + m) j (iota_seq A iota n m x)) = 0 := by
  rw [iota_seq_proj_apply A iota proj proj_comm n m j x]
  rw [iota_seq_proj_apply A iota proj proj_comm n m i (proj n j x)]
  have h : proj n i (proj n j x) = 0 := by
    have h_comp := LinearMap.congr_fun hortho x
    exact h_comp
  rw [h, map_zero]

/-! ### 2. Target Cocone Linear Evaluation -/

include psi_comm

omit psi_comm proj_comm in
/-- **Theorem 6: Linear Evaluation on Graded Component Sum**
    For every stage $n$ and element $x \in A_n$, if $x$ decomposes into the sum
    of five graded components, its cocone image $\psi_n(x)$ equals the sum of
    the cocone images of those components. -/
theorem cocone_eval_sum_graded_components (n : ℕ) (x : A n)
    (hrecons : proj n .negTwo x + proj n .negOne x + proj n .zero x +
               proj n .posOne x + proj n .posTwo x = x) :
    psi n (proj n .negTwo x) + psi n (proj n .negOne x) + psi n (proj n .zero x) +
    psi n (proj n .posOne x) + psi n (proj n .posTwo x) = psi n x := by
  rw [← map_add, ← map_add, ← map_add, ← map_add, hrecons]

/-- **Theorem 7: Graded Cocone Trace Invariance**
    Evaluating an evaluation functional $\psi_{\text{trace}} : A_\infty \to R$ on the
    $k$-th graded component is strictly invariant under tower propagation. -/
theorem graded_cocone_trace_invariance (psi_trace : A_inf →ₗ[R] R)
    (n m : ℕ) (k : FiveGrade) (x : A n) :
    psi_trace (psi (n + m) (proj (n + m) k (iota_seq A iota n m x))) =
    psi_trace (psi n (proj n k x)) := by
  rw [iota_seq_proj_apply A iota proj proj_comm n m k x]
  exact colimit_trace_comm A iota A_inf psi psi_comm psi_trace n m (proj n k x)

end InfoGeometry.Canonical.ColimitFiveGrading
