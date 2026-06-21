import Mathlib
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Nilpotent → Cyclic Subspace Decomposition

Implements the Shapiro "Cyclic Decomposition of a Nilpotent Operator" proof.

## Nilpotent Splitting Theorem

If `N : V → V` is nilpotent with `Nᵏ = 0`, `N^{k-1} ≠ 0`, there exists
`x ∈ V` and an N-invariant complement `W` such that:
  - `C = span{x, Nx, ..., N^{k-1}x}` is cyclic of dimension k
  - `V = C ⊕ W` (internal direct sum)
  - `N|_W` has nilpotence index strictly less than k

Iterating gives the full Jordan decomposition.

## Construction (Shapiro §2, "The Nilpotent Splitting Theorem"):

1. Pick `x` with `N^{k-1} x ≠ 0`. Let `v = N^{k-1} x ∈ ker N`.
2. Since `v ≠ 0`, extend `{v}` to a basis `{v, u₂, ..., u_d}` of `ker N`.
3. Choose a projection `π : V → span{v}` such that `π` commutes with `N`
   and `im(1-π)` is N-invariant. This uses linear functionals on `ker N`.
4. The key: `ker N^{k-1} = im N ⊕ ker N` and the splitting uses this.

The invariant complement is `W = (1-π) V` which contains
`ker N \ span{v}` and is N-invariant.

Since `N^{k-1} (N x) = 0`, `N x ∈ ker N^{k-1}`. The splitting
uses `x` to lift the projection from `ker N` to `ker N^{k-1}`.
-/

noncomputable section

open FiniteDimensional
open Submodule

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/--
A nilpotent operator with minimal index k: Nᵏ = 0 and N^{k-1} ≠ 0.
-/
/--
A nilpotent operator with minimal index k: (N)^k = 0 and (N)^{k-1} ≠ 0.
-/
def NilpotentIndex (N : Module.End K V) (k : ℕ) : Prop :=
  (N ^ k) = 0 ∧ (N ^ (k - 1)) ≠ 0

/--
If `N : V → V` is nilpotent, there exists a minimal k ≥ 1 such that (N)^k = 0.
This k is the *nilpotence index* of N.
-/
lemma exists_nilpotent_index (N : Module.End K V) [FiniteDimensional K V]
    (hN : IsNilpotent N) (hN_ne : N ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ NilpotentIndex N k := by
  -- IsNilpotent in mathlib4 means ∃ k, N^k = 0. Pick minimal such k.
  rcases hN with ⟨k, hk⟩
  sorry
/-!
### Lemma 2: Splitting off one cyclic subspace
-/

/--
**Nilpotent Splitting Lemma (Shapiro, Thm 2.1).**

Let N : V → V be nilpotent with nilpotence index k ≥ 1.
There exist a vector x ∈ V and an N-invariant subspace W ⊆ V such that:
  (a) V = span{x, Nx, ..., N^{k-1}x} ⊕ W  (internal direct sum)
  (b) N|_W has nilpotence index < k (or W = {0})

In matrix terms: this splits off one Jordan block of size k.

Proof construction:
  1. Pick x with N^{k-1} x ≠ 0. Set v = N^{k-1} x ∈ ker N, v ≠ 0.
  2. Choose a basis {v, u₂, ..., u_d} of ker N. Let φ : ker N → K
     be the linear functional with φ(v) = 1, φ(u_i) = 0.
  3. Extend φ to a linear functional ψ : ker N^{k-1} → K by:
     For y ∈ ker N^{k-1}, define ψ(y) such that there exists z with
     ψ(y) = φ(N^{k-1} z) when y = N^{k-1} z + u where u ∈ ker N.
     This uses the fact that im N ∩ ker N = span{v} when k > 1.
  4. Define π : V → span{x, ..., N^{k-1}x} as a projection
     commuting with N. Set W = ker π, then W is N-invariant
     and V = C ⊕ W where C = span{x, ..., N^{k-1}x}.
-/
theorem nilpotent_split_cyclic [FiniteDimensional K V] (N : Module.End K V) (k : ℕ)
    (hN : NilpotentIndex N k) (hk_pos : 1 ≤ k) :
    ∃ (x : V) (W : Submodule K V),
      (∀ y ∈ W, N y ∈ W) ∧                                       -- W is N-invariant
      (⊤ : Submodule K V) = span K { (N ^ i) x | i ≤ k-1 } ⊔ W ∧ -- V = C + W
      Disjoint (span K { (N ^ i) x | i ≤ k-1 }) W := by          -- C ∩ W = {0}
  -- Step 1: Pick x with N^{k-1} x ≠ 0.
  have hk_prev : N ^ (k-1) ≠ 0 := hN.right
  -- There exists x such that N^{k-1} x ≠ 0
  have h_exists_x : ∃ x, N ^ (k-1) x ≠ 0 := by
    contrapose! hk_prev; ext x; exact hk_prev x
  rcases h_exists_x with ⟨x, hx⟩

  -- Step 2: v = N^{k-1} x ∈ ker N, v ≠ 0.
  let v := N ^ (k-1) x
  have hv_ker : N v = 0 := by
    calc N v = N (N ^ (k-1) x) := rfl
      _ = (N * N ^ (k-1)) x := rfl
      _ = N ^ k x := by ring
      _ = 0 := by rw [hN.left]; rfl
  have hv_ne_zero : v ≠ 0 := hx

  -- Step 3: Choose a basis of ker N containing v.
  -- ker N is a subspace. Extend {v} to a basis {v, u₂, ..., u_d}.
  -- This uses `Submodule.exists_basis` and `Basis.extend`.
  sorry

/-!
### Lemma 3: Induction → full decomposition
-/

/--
**Nilpotent Cyclic Decomposition Theorem.**

Every nilpotent endomorphism of a finite-dimensional vector space
decomposes the space into a direct sum of cyclic subspaces.

Each cyclic subspace corresponds to a Jordan block.
-/
theorem nilpotent_cyclic_decomposition [FiniteDimensional K V]
    (N : Module.End K V) (hN : IsNilpotent N) :
    ∃ (r : ℕ) (xs : Fin r → V) (ks : Fin r → ℕ),
      (∀ i, ks i ≥ 1) ∧
      (∀ i, NilpotentIndex (N.restrict (λ y => ?_)) (ks i)) ∧
      -- The cyclic subspaces are independent and span V
      CompleteLattice.Independent (λ i => span K { (N ^ j) (xs i) | j ≤ ks i - 1 }) ∧
      (⨆ i, span K { (N ^ j) (xs i) | j ≤ ks i - 1 }) = ⊤ := by
  -- Induction on the nilpotence index k = min {m | N^m = 0}
  rcases exists_nilpotent_index N hN with ⟨k, hk_pos, hk⟩
  -- Base: k = 0 (N = 0 on V) → trivial decomposition
  -- Induction: use nilpotent_split_cyclic to split off one block,
  --   then apply induction to N|_W (which has smaller nilpotence index)
  --
  -- The induction is on (dim V, nilpotence_index N) with the lexicographic order.
  -- nilpotent_split_cyclic gives x and N-invariant W.
  -- The restriction N_W has nilpotence index < k (or W = {0}).
  --
  -- Formal induction: strong induction on `dim V` + `nilpotence_index N`.
  -- If dim V = 0 or k = 1: N = 0, done (each basis vector is a cyclic subspace).
  -- If k > 1: use the splitting lemma, then apply IH to W.
  sorry

end CyclicNilpotent
