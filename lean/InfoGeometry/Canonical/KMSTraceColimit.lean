import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

noncomputable section

namespace InfoGeometry.Canonical.KMSTraceColimit

/-!
# KMS Trace Preservation & State Factorizability across $A_\infty$ Colimits

This module formalizes finite-stage normalized KMS states and trace readback on the
diagonal MASA $A_\infty$ cylinder colimit.

Key Results:
1. `normalizedTrace`: Normalized trace $\tau_n(f) = \frac{1}{2^n} \sum_{w} f(w)$.
2. `normalizedTrace_one`: $\tau_n(1) = 1$.
3. `normalizedTrace_embed`: $\tau_{n+1}(\text{diagEmbedSucc } n f) = \tau_n(f)$ (Inductive Trace Preservation).
4. `normalizedTrace_seq`: $\tau_{n+m}(\iota_{n \to n+m}(f)) = \tau_n(f)$ for all $m \in \mathbb{N}$.
-/

/-- Normalized trace at stage $n$ on $\text{DiagAlg } n$. -/
def normalizedTrace (n : ℕ) (f : DiagAlg n) : ℂ :=
  (1 / (2 ^ n : ℂ)) * ∑ w : BitWord n, f w

set_option linter.unusedSimpArgs false in
/-- Trace of the identity observable is 1. -/
theorem normalizedTrace_one (n : ℕ) :
    normalizedTrace n 1 = 1 := by
  dsimp [normalizedTrace]
  simp [Finset.sum_const, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- Equivalence between `BitWord (n + 1)` and `BitWord n × Bool`. -/
def bitWordSuccEquiv (n : ℕ) : BitWord (n + 1) ≃ BitWord n × Bool where
  toFun w := (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩)
  invFun p := extendSucc n p.1 p.2
  left_inv w := by
    ext ⟨i, hi⟩
    by_cases h_in : i < n
    · dsimp [extendSucc, prefixSucc]
      rw [dif_pos h_in]
    · have h_eq_n : i = n := by omega
      subst h_eq_n
      dsimp [extendSucc]
      rw [dif_neg (by omega)]
  right_inv := by
    rintro ⟨w, b⟩
    refine Prod.ext ?_ ?_
    · exact prefixSucc_extendSucc n w b
    · dsimp [extendSucc]; rw [dif_neg (by omega)]

/-- Decomposition of summation over `BitWord (n + 1)` into `false` and `true` branches. -/
theorem sum_bitWord_succ (n : ℕ) (g : BitWord (n + 1) → ℂ) :
    (∑ w : BitWord (n + 1), g w) =
      (∑ w : BitWord n, g (extendSucc n w false)) + (∑ w : BitWord n, g (extendSucc n w true)) := by
  have h_comp := Equiv.sum_comp (bitWordSuccEquiv n).symm g
  dsimp [bitWordSuccEquiv] at h_comp
  rw [← h_comp, Fintype.sum_prod_type]
  simp [Finset.sum_add_distrib, add_comm]

/-- **Theorem: Inductive Trace Preservation (Single Step)**
    Embedding $f \in \text{DiagAlg } n$ into stage $n+1$ preserves the normalized trace. -/
theorem normalizedTrace_embed (n : ℕ) (f : DiagAlg n) :
    normalizedTrace (n + 1) (diagEmbedSucc n f) = normalizedTrace n f := by
  dsimp [normalizedTrace, diagEmbedSucc]
  rw [pow_succ]
  have h_split : (∑ w : BitWord (n + 1), f (prefixSucc n w)) = 2 * ∑ w : BitWord n, f w := by
    rw [sum_bitWord_succ n (fun w => f (prefixSucc n w))]
    simp [prefixSucc_extendSucc]
    ring
  rw [h_split]
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n h2
  calc (1 / ((2 : ℂ) ^ n * 2)) * (2 * ∑ w : BitWord n, f w)
    _ = (1 / (2 ^ n : ℂ)) * (1 / 2) * (2 * ∑ w : BitWord n, f w) := by
        congr 1; ring
    _ = (1 / (2 ^ n : ℂ)) * ((1 / 2 * 2) * ∑ w : BitWord n, f w) := by
        ring
    _ = (1 / (2 ^ n : ℂ)) * (1 * ∑ w : BitWord n, f w) := by
        rw [one_div_mul_cancel h2]
    _ = (1 / (2 ^ n : ℂ)) * ∑ w : BitWord n, f w := by
        rw [one_mul]

/-- Inductive sequence of diagonal embeddings across $m$ steps. -/
def diagEmbedSeq (n : ℕ) : ∀ m : ℕ, DiagAlg n → DiagAlg (n + m)
| 0, f => f
| m + 1, f => diagEmbedSucc (n + m) (diagEmbedSeq n m f)

/-- **Theorem: Inductive Trace Preservation across $m$ stages**
    $\tau_{n+m}(\text{diagEmbedSeq } n m f) = \tau_n(f)$. -/
theorem normalizedTrace_seq (n : ℕ) (f : DiagAlg n) : ∀ m : ℕ,
    normalizedTrace (n + m) (diagEmbedSeq n m f) = normalizedTrace n f
| 0 => rfl
| m + 1 => by
    have h_step : normalizedTrace (n + (m + 1)) (diagEmbedSeq n (m + 1) f) =
        normalizedTrace ((n + m) + 1) (diagEmbedSucc (n + m) (diagEmbedSeq n m f)) := rfl
    rw [h_step, normalizedTrace_embed (n + m), normalizedTrace_seq n f m]


end InfoGeometry.Canonical.KMSTraceColimit
