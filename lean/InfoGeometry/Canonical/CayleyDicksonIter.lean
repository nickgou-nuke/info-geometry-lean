import InfoGeometry.Canonical.CayleyDicksonEmbedding
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.AlbertCayleyDickson

variable {A : ℕ → Type*} 
variable (e : (n : ℕ) → A n → A (n + 1))

def cdEmbedIter (e : (n : ℕ) → A n → A (n + 1)) : (n m : ℕ) → n ≤ m → A n → A m
| n, m, h =>
  if heq : n = m then
    fun x => cast (by rw [heq]) x
  else
    have hlt : n < m := lt_of_le_of_ne h heq
    fun x => cdEmbedIter e (n + 1) m hlt (e n x)

theorem cdEmbedIter_self (n : ℕ) (h : n ≤ n) (x : A n) :
    cdEmbedIter e n n h x = x := by
  unfold cdEmbedIter
  rw [dif_pos rfl]
  rfl

theorem cdEmbedIter_succ (n : ℕ) (h : n ≤ n + 1) (x : A n) :
    cdEmbedIter e n (n + 1) h x = e n x := by
  unfold cdEmbedIter
  rw [dif_neg (Nat.ne_of_lt (Nat.lt_succ_self n))]
  unfold cdEmbedIter
  rw [dif_pos rfl]
  rfl

end InfoGeometry.Canonical.AlbertCayleyDickson
