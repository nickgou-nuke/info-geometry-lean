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
