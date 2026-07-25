import Mathlib.Tactic
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
def NilpotentIndex (N : Module.End K V) (k : ℕ) : Prop :=
  (N ^ k) = 0 ∧ (N ^ (k - 1)) ≠ 0

/-- A nilpotent index is strictly positive. -/
theorem nilpotentIndex_pos {N : Module.End K V} {k : ℕ}
    (h : NilpotentIndex N k) : 1 ≤ k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  subst hk0
  have h10 : (1 : Module.End K V) = 0 := by
    ext v
    have h' := congrArg (fun f : Module.End K V => f v) h.1
    simpa using h'
  have hne : (1 : Module.End K V) ≠ 0 := by
    simpa using h.2
  exact hne h10

/--
If `N : V → V` is nilpotent, there exists a minimal k ≥ 1 such that (N)^k = 0.
This k is the *nilpotence index* of N.
-/
lemma exists_nilpotent_index (N : Module.End K V) [FiniteDimensional K V]
    (hN : IsNilpotent N) (hN_ne : N ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ NilpotentIndex N k := by
  classical
  rcases hN with ⟨m, hm⟩
  let S := { n : ℕ | N ^ n = 0 }
  have hS : S.Nonempty := ⟨m, hm⟩
  let k := Nat.find hS
  have hk0 : N ^ k = 0 := Nat.find_spec hS
  have hk_pos : 1 ≤ k := by
    by_contra h
    push_neg at h
    have hk_zero : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
    have hz : N ^ 0 = 0 := by rw [←hk_zero, hk0]
    have hz2 : N ^ 0 = 1 := pow_zero N
    rw [hz2] at hz
    have h10 : (1 : Module.End K V) = 0 := hz
    have hN0 : N = 0 := by
      calc N = N * 1 := (mul_one N).symm
           _ = N * 0 := by rw [h10]
           _ = 0 := mul_zero N
    exact hN_ne hN0
  have hk_prev : N ^ (k - 1) ≠ 0 := by
    intro h
    have hlt : k - 1 < k := by omega
    have contra := Nat.find_min hS hlt
    exact contra h
  exact ⟨k, hk_pos, hk0, hk_prev⟩
/-!
### Lemma 2: Splitting off one cyclic subspace
-/

/-!
### Lemma 2 & 3: Splitting/decomposition roadmap

The full cyclic splitting and full cyclic decomposition theorems are not encoded
as kernel-checked claims in this file. This file contributes only local index
lemmas and infrastructure for finite-dimensional nilpotent chains.
-/
