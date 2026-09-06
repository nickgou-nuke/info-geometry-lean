import proofs.BraidProject.PresentedMonoid_mine
import proofs.BraidProject.AcrossStrands

/- Fused block-crossing words. -/

open FreeMonoid'

def Phi : ℕ → ℕ → ℕ → FreeMonoid' ℕ
  | 0, _, _ => 1
  | n + 1, m, i => sigma_neg i (i + m) * Phi n m (i + 1)

def Psi : ℕ → ℕ → ℕ → FreeMonoid' ℕ
  | _, 0, _ => 1
  | n, m + 1, i => sigma_neg (i + n + m) (i + m) * Psi n m i

-- for the braid with infinitely many strands
inductive fused_rels_m_inf : FreeMonoid' ℕ → FreeMonoid' ℕ → Prop
  | adjacent (i : ℕ): fused_rels_m_inf (of i * of (i+1) * of i) (of (i+1) * of i * of (i+1))
  | separated (i j : ℕ) (h : i +2 ≤ j): fused_rels_m_inf (of i * of j) (of j * of i)
  | cross_far_h (i j n m : ℕ) (h : j + 2 ≤ i) : fused_rels_m_inf (of j * Phi n m i) (Phi n m i * of j)
  | cross_far_s (i j n m : ℕ) (h : j + 2 ≤ i) : fused_rels_m_inf (of j * Psi n m i) (Psi n m i * of j)
  | cross_close_h (i j n m : ℕ) (h : i + n ≤ j) : fused_rels_m_inf (of j * Phi n m i) (Phi n m i * of (j - n + m))
  | cross_close_s (i j n m : ℕ) (h : i + n ≤ j) : fused_rels_m_inf (of j * Psi n m i) (Psi n m i * of (j - n + m))
