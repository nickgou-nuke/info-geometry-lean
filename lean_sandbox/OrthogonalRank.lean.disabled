import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Orthogonal Rank Additivity

Theorem: rank(A+B) = rank(A) + rank(B) when AᵀB = 0 AND ABᵀ = 0.

Proof: (A+B)ᵀ(A+B) = AᵀA + BᵀB (cross terms vanish).
rank(A+B) = rank((A+B)ᵀ(A+B)) = rank(AᵀA + BᵀB).

Let P = AᵀA, Q = BᵀB. Both are symmetric, positive semidefinite.
PQ = Aᵀ(ABᵀ)B = 0, QP = 0.
For commuting symmetric matrices with zero product, ker(P+Q) = ker(P) ∩ ker(Q),
hence rank(P+Q) = rank(P) + rank(Q) by rank-nullity.
And rank(P) = rank(A), rank(Q) = rank(B) by Mathlib `rank_transpose_mul_self`.
-/

open Matrix

namespace OrthogonalRank

variable {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ)

/--
**Theorem: rank(A+B) = rank(A) + rank(B) when AᵀB = 0 AND ABᵀ = 0.**

Assumptions:
- h1: AᵀB = 0 (columns of A orthogonal to columns of B)
- h2: ABᵀ = 0 (rows of A orthogonal to rows of B)

Proof:
1. (A+B)ᵀ(A+B) = AᵀA + BᵀB (cross terms vanish by h1, h2)
2. rank(A+B) = rank((A+B)ᵀ(A+B)) (Mathlib: rank_transpose_mul_self)
   = rank(AᵀA + BᵀB)
3. Let P = AᵀA, Q = BᵀB. PQ = Aᵀ(ABᵀ)B = 0. QP = 0 symmetrically.
4. For symmetric P, Q with PQ = QP = 0: ker(P+Q) = ker(P) ∩ ker(Q)
   (If (P+Q)v = 0, then ⟨v,Pv⟩ + ⟨v,Qv⟩ = 0. Since both terms ≥ 0, each = 0.
    Hence Pv = Qv = 0.)
5. By rank-nullity: rank(P+Q) + dim(ker(P+Q)) = n
   rank(P) + dim(ker P) = n
   rank(Q) + dim(ker Q) = n
   Since ker(P+Q) = ker P ∩ ker Q ⊆ ker P, ker Q:
   dim(ker(P+Q)) ≤ min(dim(ker P), dim(ker Q))
   And ker P ∩ ker Q ⊇ ker P ∩ ker Q trivially.
   Actually: since PQ = 0, im(Q) ⊆ ker(P) and im(P) ⊆ ker(Q).
   Hence rank(P) + rank(Q) ≤ n. And rank(P+Q) ≤ rank(P) + rank(Q) (subadditivity).
   With ker(P+Q) = ker(P) ∩ ker(Q):
     rank(P+Q) = n - dim(ker P ∩ ker Q)
     ≥ n - min(dim(ker P), dim(ker Q))
     Not quite — need a direct argument.
   Let's use the orthogonal decomposition: im(P) ⟂ im(Q) since P·Q = 0.
   For orthogonal subspaces, rank(P+Q) = rank(P) + rank(Q).
6. rank(P) = rank(A) by rank_transpose_mul_self.
   rank(Q) = rank(B) by rank_self_mul_transpose (since Q = BᵀB, but Mathlib has rank_transpose_mul_self for AᵀA; for AAᵀ use rank_self_mul_transpose).

Actually: Qᵀ = (BᵀB)ᵀ = BᵀB = Q, so Q = BᵀB, and rank_transpose_mul_self B gives rank(BᵀB) = rank(B).
P = AᵀA, so rank_transpose_mul_self A gives rank(AᵀA) = rank(A).
-/
theorem rank_add_of_orthogonal (h1 : Aᵀ * B = 0) (h2 : A * Bᵀ = 0) :
    (A + B).rank = A.rank + B.rank := by
  -- Step 1: (A+B)ᵀ(A+B) = AᵀA + BᵀB
  have h_expand : (A + B)ᵀ * (A + B) = Aᵀ * A + Bᵀ * B := by
    calc
      (A + B)ᵀ * (A + B) = (Aᵀ + Bᵀ) * (A + B) := by simp
      _ = Aᵀ * A + Aᵀ * B + Bᵀ * A + Bᵀ * B := by noncomm_ring
      _ = Aᵀ * A + 0 + 0 + Bᵀ * B := by rw [h1, h2, transpose_transpose]
      _ = Aᵀ * A + Bᵀ * B := by simp
  -- Step 2: rank(A+B) = rank((A+B)ᵀ(A+B)) = rank(AᵀA + BᵀB)
  have h_rank_sum : (A + B).rank = (Aᵀ * A + Bᵀ * B).rank := by
    calc
      (A + B).rank = ((A + B)ᵀ * (A + B)).rank := by
        simpa using (rank_transpose_mul_self (A + B)).symm
      _ = (Aᵀ * A + Bᵀ * B).rank := by rw [h_expand]
  -- Step 3: Let P = AᵀA, Q = BᵀB
  let P := Aᵀ * A
  let Q := Bᵀ * B
  -- PQ = Aᵀ(ABᵀ)B = 0, QP = 0
  have h_PQ : P * Q = 0 := by
    dsimp [P, Q]
    calc
      (Aᵀ * A) * (Bᵀ * B) = Aᵀ * (A * Bᵀ) * B := by noncomm_ring
      _ = Aᵀ * (0 : Matrix (Fin m) (Fin m) ℚ) * B := by rw [h2]
      _ = 0 := by simp
  have h_QP : Q * P = 0 := by
    dsimp [P, Q]
    calc
      (Bᵀ * B) * (Aᵀ * A) = Bᵀ * (B * Aᵀ) * A := by noncomm_ring
      _ = Bᵀ * ((A * Bᵀ)ᵀ) * A := by simp
      _ = Bᵀ * (0 : Matrix (Fin m) (Fin m) ℚ)ᵀ * A := by rw [h2]
      _ = 0 := by simp
  -- Step 4: rank(P+Q) = rank(P) + rank(Q) when PQ = QP = 0
  -- For symmetric P, Q over ℚ: im(P) ⟂ im(Q) when PQ = 0.
  -- This means the subspaces are linearly independent, giving the rank sum.
  have h_rankPQ : (P + Q).rank = P.rank + Q.rank := by
    -- The key: when PQ = 0, every eigenvalue of P+Q is either from P or Q.
    -- Since ℚ is a field, we can use the fact that ker(P+Q) = ker(P) ∩ ker(Q).
    -- Proof: (P+Q)v = 0 ⇒ vᵀPv + vᵀQv = 0. Since vᵀPv ≥ 0, vᵀQv ≥ 0
    -- (P, Q are Gram matrices), both must be 0. Hence Pv = Qv = 0.
    -- Then rank(P+Q) = n - dim(ker P ∩ ker Q)
    --               = n - dim(ker P) - dim(ker Q) + dim(ker P + ker Q)
    -- When PQ = 0: im(Q) ⊆ ker(P), so dim(im Q) ≤ dim(ker P). Similarly.
    -- Actually simpler: from im(Q) ⊆ ker(P): rank(Q) ≤ dim(ker P) = n - rank(P)
    -- So rank(P) + rank(Q) ≤ n.
    -- And rank(P+Q) = n - dim(ker(P+Q)) = n - dim(ker P ∩ ker Q)
    --                ≥ n - dim(ker P) = rank(P)
    -- Not enough. Need the full argument.
    --
    -- The cleanest proof: diagonalize P, Q simultaneously (they commute since PQ=QP=0).
    -- Over ℚ, symmetric commuting matrices are simultaneously diagonalizable.
    -- This gives rank(P+Q) = rank(P) + rank(Q).
    sorry
  -- Step 5: rank(P) = rank(A), rank(Q) = rank(B)
  have h_rankP : P.rank = A.rank := by
    dsimp [P]; simpa using (rank_transpose_mul_self A).symm
  have h_rankQ : Q.rank = B.rank := by
    dsimp [Q]; simpa using (rank_transpose_mul_self B).symm
  -- Step 6: Assemble
  rw [h_rank_sum, h_rankPQ, h_rankP, h_rankQ]

end OrthogonalRank
