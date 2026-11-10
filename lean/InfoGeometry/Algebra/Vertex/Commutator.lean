/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Vertex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Mode Commutator from the Borcherds Identity

This module derives the mode commutator by specializing the Borcherds identity
at its second integer parameter `n = 0`. The generalized binomial coefficient
`intBinom k 0 i` annihilates every summand except `i = 0`.

All sums remain finite and use the positive cutoff supplied by the vertex
algebra structure.
-/

namespace InfoGeometry.Algebra.Vertex

open scoped BigOperators
open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair_commutator :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section DivisionRingCommutatorCollapse

variable {D V : Type*} [DivisionRing D] [AddCommGroup V] [Module D V]

/-- Over any `[DivisionRing D]`, the `n = 0` Borcherds commutator RHS sum collapses to its `i = 0`
commutator term for any additive mode family `mode : ℤ → V → V → V` and positive cutoff `0 < N`. -/
theorem borcherdsRhsList_collapse_at_zero
    (mode : ℤ → V → V → V) (m ell : ℤ) (a b c : V) {N : ℕ} (hN : 0 < N) :
    (∑ i ∈ Finset.range N,
      (((-1 : D) ^ i) * intBinomList D 0 i) •
        (mode (m - (i : ℤ)) a (mode (ell + (i : ℤ)) b c) -
          mode (ell - (i : ℤ)) b (mode (m + (i : ℤ)) a c))) =
      mode m a (mode ell b c) - mode ell b (mode m a c) := by
  calc
    (∑ i ∈ Finset.range N,
      (((-1 : D) ^ i) * intBinomList D 0 i) •
        (mode (m - (i : ℤ)) a (mode (ell + (i : ℤ)) b c) -
          mode (ell - (i : ℤ)) b (mode (m + (i : ℤ)) a c))) =
      (((-1 : D) ^ 0) * intBinomList D 0 0) •
        (mode (m - (0 : ℤ)) a (mode (ell + (0 : ℤ)) b c) -
          mode (ell - (0 : ℤ)) b (mode (m + (0 : ℤ)) a c)) := by
      apply Finset.sum_eq_single 0
      · intro i _ hne
        have hipos : 0 < i := Nat.pos_of_ne_zero hne
        simp [intBinomList_zero_of_pos D i hipos]
      · intro hzero
        exact (hzero (Finset.mem_range.mpr hN)).elim
    _ = mode m a (mode ell b c) - mode ell b (mode m a c) := by
      simp

end DivisionRingCommutatorCollapse

variable {k V : Type*}
variable [Field k] [CharZero k] [AddCommGroup V] [Module k V]

namespace VertexAlgebra

/-- The finite mode commutator formula derived from the Borcherds identity.

The returned cutoff is the actual positive Borcherds cutoff. The accompanying
tail statement records that both original summand families vanish from that
index onward.
-/
theorem mode_commutator (A : VertexAlgebra k V)
    (m ell : ℤ) (a b c : V) :
    ∃ N : ℕ,
      0 < N ∧
        (∀ i : ℕ, N ≤ i →
          borcherdsLhsTerm A.mode m 0 ell a b c i = 0 ∧
          borcherdsRhsTerm A.mode m 0 ell a b c i = 0) ∧
        A.mode m a (A.mode ell b c) -
            A.mode ell b (A.mode m a c) =
          ∑ i ∈ Finset.range N,
            intBinom k m i •
              A.mode (m + ell - (i : ℤ))
                (A.mode (i : ℤ) a b) c := by
  rcases A.borcherds m 0 ell a b c with
    ⟨N, hN, hvanish, hidentity⟩
  refine ⟨N, hN, hvanish, ?_⟩
  have hrhs :
      (∑ i ∈ Finset.range N,
          borcherdsRhsTerm A.mode m 0 ell a b c i) =
        A.mode m a (A.mode ell b c) -
          A.mode ell b (A.mode m a c) := by
    calc
      (∑ i ∈ Finset.range N,
          borcherdsRhsTerm A.mode m 0 ell a b c i) =
          borcherdsRhsTerm A.mode m 0 ell a b c 0 := by
        apply Finset.sum_eq_single 0
        · intro i _ hne
          have hipos : 0 < i := Nat.pos_of_ne_zero hne
          simp [borcherdsRhsTerm,
            intBinom_zero_of_pos (k := k) i hipos]
        · intro hzero
          exact (hzero (Finset.mem_range.mpr hN)).elim
      _ = A.mode m a (A.mode ell b c) -
          A.mode ell b (A.mode m a c) := by
        simp [borcherdsRhsTerm]
  calc
    A.mode m a (A.mode ell b c) -
        A.mode ell b (A.mode m a c) =
        ∑ i ∈ Finset.range N,
          borcherdsRhsTerm A.mode m 0 ell a b c i :=
      hrhs.symm
    _ = ∑ i ∈ Finset.range N,
          borcherdsLhsTerm A.mode m 0 ell a b c i :=
      hidentity.symm
    _ = ∑ i ∈ Finset.range N,
          intBinom k m i •
            A.mode (m + ell - (i : ℤ))
              (A.mode (i : ℤ) a b) c := by
      apply Finset.sum_congr rfl
      intro i _
      simp [borcherdsLhsTerm]

end VertexAlgebra

end InfoGeometry.Algebra.Vertex
