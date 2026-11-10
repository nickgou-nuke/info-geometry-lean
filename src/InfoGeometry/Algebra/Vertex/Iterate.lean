/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Vertex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Mode Iterate Formula from the Borcherds Identity

This module derives the mode iterate formula by specializing the Borcherds
identity at its first integer parameter `m = 0`. The generalized binomial
coefficient `intBinom k 0 i` annihilates every summand on the iterate side
except `i = 0`.

All sums remain finite and use the positive cutoff supplied by the vertex
algebra structure.
-/

namespace InfoGeometry.Algebra.Vertex

open scoped BigOperators
open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair_iterate :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section DivisionRingIterateCollapse

variable {D V : Type*} [DivisionRing D] [AddCommGroup V] [Module D V]

/-- Over any `[DivisionRing D]`, the `m = 0` Borcherds iterate LHS sum collapses to its `i = 0`
iterate term `mode ell (mode n a b) c` for any mode family `mode : ℤ → V → V → V` and `0 < N`. -/
theorem borcherdsLhsList_collapse_at_zero
    (mode : ℤ → V → V → V) (n ell : ℤ) (a b c : V) {N : ℕ} (hN : 0 < N) :
    (∑ i ∈ Finset.range N,
      intBinomList D 0 i •
        mode (ell - (i : ℤ)) (mode (n + (i : ℤ)) a b) c) =
      mode ell (mode n a b) c := by
  calc
    (∑ i ∈ Finset.range N,
      intBinomList D 0 i •
        mode (ell - (i : ℤ)) (mode (n + (i : ℤ)) a b) c) =
      intBinomList D 0 0 •
        mode (ell - (0 : ℤ)) (mode (n + (0 : ℤ)) a b) c := by
      apply Finset.sum_eq_single 0
      · intro i _ hne
        have hipos : 0 < i := Nat.pos_of_ne_zero hne
        simp [intBinomList_zero_of_pos D i hipos]
      · intro hzero
        exact (hzero (Finset.mem_range.mpr hN)).elim
    _ = mode ell (mode n a b) c := by
      simp

end DivisionRingIterateCollapse

variable {k V : Type*}
variable [Field k] [CharZero k] [AddCommGroup V] [Module k V]

namespace VertexAlgebra

/-- The finite mode iterate formula derived from the Borcherds identity.

The returned cutoff is the actual positive Borcherds cutoff. The accompanying
tail statement records that both original summand families vanish from that
index onward.
-/
theorem mode_iterate (A : VertexAlgebra k V)
    (n ell : ℤ) (a b c : V) :
    ∃ N : ℕ,
      0 < N ∧
        (∀ i : ℕ, N ≤ i →
          borcherdsLhsTerm A.mode 0 n ell a b c i = 0 ∧
          borcherdsRhsTerm A.mode 0 n ell a b c i = 0) ∧
        A.mode ell (A.mode n a b) c =
          ∑ i ∈ Finset.range N,
            (((-1 : k) ^ i) * intBinom k n i) •
              (A.mode (n - (i : ℤ)) a
                  (A.mode (ell + (i : ℤ)) b c) -
                ((-1 : k) ^ n) •
                  A.mode (n + ell - (i : ℤ)) b
                    (A.mode (i : ℤ) a c)) := by
  rcases A.borcherds 0 n ell a b c with
    ⟨N, hN, hvanish, hidentity⟩
  refine ⟨N, hN, hvanish, ?_⟩
  have hlhs :
      (∑ i ∈ Finset.range N,
          borcherdsLhsTerm A.mode 0 n ell a b c i) =
        A.mode ell (A.mode n a b) c := by
    calc
      (∑ i ∈ Finset.range N,
          borcherdsLhsTerm A.mode 0 n ell a b c i) =
          borcherdsLhsTerm A.mode 0 n ell a b c 0 := by
        apply Finset.sum_eq_single 0
        · intro i _ hne
          have hipos : 0 < i := Nat.pos_of_ne_zero hne
          simp [borcherdsLhsTerm,
            intBinom_zero_of_pos (k := k) i hipos]
        · intro hzero
          exact (hzero (Finset.mem_range.mpr hN)).elim
      _ = A.mode ell (A.mode n a b) c := by
        simp [borcherdsLhsTerm]
  calc
    A.mode ell (A.mode n a b) c =
        ∑ i ∈ Finset.range N,
          borcherdsLhsTerm A.mode 0 n ell a b c i :=
      hlhs.symm
    _ = ∑ i ∈ Finset.range N,
          borcherdsRhsTerm A.mode 0 n ell a b c i :=
      hidentity
    _ = ∑ i ∈ Finset.range N,
          (((-1 : k) ^ i) * intBinom k n i) •
            (A.mode (n - (i : ℤ)) a
                (A.mode (ell + (i : ℤ)) b c) -
              ((-1 : k) ^ n) •
                A.mode (n + ell - (i : ℤ)) b
                  (A.mode (i : ℤ) a c)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [borcherdsRhsTerm]

end VertexAlgebra

end InfoGeometry.Algebra.Vertex
