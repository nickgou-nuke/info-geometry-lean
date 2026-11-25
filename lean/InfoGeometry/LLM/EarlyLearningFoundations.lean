/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Foundational Mathematical Boundaries of Early Learning Models (1943–1969)

Kernel-checked theorems separating exact mathematical results of the 1943–1969
foundational era from narrative or empirical claims about contemporary ML:

1. **McCulloch–Pitts (1943) and Minsky–Papert (1969) XOR Boundary:**
   no single linear-threshold neuron computes `XOR`, whereas a two-layer threshold
   circuit computes `XOR` exactly (`minsky_papert_no_single_layer_xor`,
   `mcculloch_pitts_two_layer_computes_xor`).
2. **Shannon (1948) Cross-Entropy / Prediction-as-Compression Bound:**
   the cross-entropy of a predictive distribution `q` relative to a source `p`
   splits cleanly as `H(p) + D_KL(p ‖ q) ≥ H(p)` with equality iff `p = q`
   (`crossEntropy_eq_shannonEntropy_add_kl`, `klDivergence_nonneg`,
   `shannon_compression_lower_bound`, `klDivergence_eq_zero_iff`).
3. **Gold (1967) Identification-in-the-Limit Obstruction:**
   exact identification in the limit from positive-only text is impossible for any
   superfinite class containing all finite bounded subsets `{x | x ≤ k}` and `ℕ`
   (`gold_1967_superfinite_nonidentifiable`).

See `docs/GROMOV_EARLY_MODELS_EPISTEMIC_COMPILATION.md` for the epistemic ledger,
scope barriers, and digested modern literature (Strobl et al. 2024, Merrill–Sabharwal
2022/2024, Delétang–Hutter et al. 2024, Valiant 1984, and Gromov 2011/2014).
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.LLM.EarlyLearningFoundations

/-! ## 1. McCulloch–Pitts (1943) and Minsky–Papert (1969) Threshold-Unit XOR Boundary -/

/-- Canonical embedding of Boolean inputs `{false, true}` into `{0, 1} ⊂ ℝ`. -/
def bitToReal (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Single-layer linear-threshold neuron predicate `w₁ x₁ + w₂ x₂ > θ`. -/
def singleLayerThreshold (w₁ w₂ θ : ℝ) (x₁ x₂ : Bool) : Prop :=
  θ < w₁ * bitToReal x₁ + w₂ * bitToReal x₂

/-- **Minsky–Papert (1969) single-layer impossibility for XOR**: no choice of weights
`(w₁, w₂)` and threshold `θ` makes a single threshold gate compute Boolean `xor`. -/
theorem minsky_papert_no_single_layer_xor :
    ¬ ∃ w₁ w₂ θ : ℝ, ∀ x₁ x₂ : Bool,
      singleLayerThreshold w₁ w₂ θ x₁ x₂ ↔ xor x₁ x₂ = true := by
  rintro ⟨w₁, w₂, θ, h⟩
  have h00 : ¬ singleLayerThreshold w₁ w₂ θ false false := by
    intro hlt
    have : xor false false = true := (h false false).mp hlt
    simp at this
  have h10 : singleLayerThreshold w₁ w₂ θ true false :=
    (h true false).mpr rfl
  have h01 : singleLayerThreshold w₁ w₂ θ false true :=
    (h false true).mpr rfl
  have h11 : ¬ singleLayerThreshold w₁ w₂ θ true true := by
    intro hlt
    have : xor true true = true := (h true true).mp hlt
    simp at this
  simp only [singleLayerThreshold, bitToReal, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero,
    not_lt, mul_one, zero_add] at h00 h10 h01 h11
  linarith

/-- Explicit two-layer McCulloch–Pitts threshold network (`(x₁ ∨ x₂) ∧ ¬(x₁ ∧ x₂)`). -/
def twoLayerThresholdXOR (x₁ x₂ : Bool) : Prop :=
  (1.5 : ℝ) <
    (if (0.5 : ℝ) < bitToReal x₁ + bitToReal x₂ then (1 : ℝ) else 0) +
    (if (-1.5 : ℝ) < -(bitToReal x₁) - bitToReal x₂ then (1 : ℝ) else 0)

/-- **McCulloch–Pitts (1943) multi-layer realization**: a depth-2 threshold network
computes `xor` exactly on all Boolean pairs. -/
theorem mcculloch_pitts_two_layer_computes_xor (x₁ x₂ : Bool) :
    twoLayerThresholdXOR x₁ x₂ ↔ xor x₁ x₂ = true := by
  cases x₁ <;> cases x₂ <;> norm_num [twoLayerThresholdXOR, bitToReal]

/-! ## 2. Finite Automata, Hebbian Updates, and Perceptron Algebra -/

/-- A deterministic finite-state transition system. -/
structure DeterministicAutomaton (State Symbol : Type*) where
  step : State → Symbol → State
  accepting : State → Prop

namespace DeterministicAutomaton

variable {State Symbol : Type*}

/-- State reached after reading a finite word. -/
def run (A : DeterministicAutomaton State Symbol) (s : State) : List Symbol → State
  | [] => s
  | a :: w => run A (A.step s a) w

/-- The empty word leaves the state unchanged. -/
@[simp] theorem run_nil (A : DeterministicAutomaton State Symbol) (s : State) :
    run A s [] = s := rfl

/-- Reading a leading symbol is one transition followed by the remaining word. -/
@[simp] theorem run_cons (A : DeterministicAutomaton State Symbol)
    (s : State) (a : Symbol) (w : List Symbol) :
    run A s (a :: w) = run A (A.step s a) w := rfl

/-- Sequential reading factors through the state after the first word. -/
theorem run_append (A : DeterministicAutomaton State Symbol)
    (s : State) (u v : List Symbol) :
    run A s (u ++ v) = run A (run A s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih =>
      simp [ih]

/-- Acceptance is determined by the state reached after the word. -/
def accepts (A : DeterministicAutomaton State Symbol) (s : State)
    (w : List Symbol) : Prop :=
  A.accepting (run A s w)

@[simp] theorem accepts_nil (A : DeterministicAutomaton State Symbol) (s : State) :
    A.accepts s [] ↔ A.accepting s := by
  rfl

/-- Acceptance after concatenation is acceptance from the intermediate state. -/
theorem accepts_append (A : DeterministicAutomaton State Symbol)
    (s : State) (u v : List Symbol) :
    A.accepts s (u ++ v) ↔ A.accepts (run A s u) v := by
  change A.accepting (run A s (u ++ v)) ↔
    A.accepting (run A (run A s u) v)
  rw [run_append]

end DeterministicAutomaton

/-- One scalar Hebbian-style update, with all parameters explicit. -/
def hebbianUpdate (weight input output rate : ℝ) : ℝ :=
  weight + rate * output * input

/-- The Hebbian increment is exactly the product of rate and co-activity. -/
theorem hebbianUpdate_sub (weight input output rate : ℝ) :
    hebbianUpdate weight input output rate - weight = rate * output * input := by
  unfold hebbianUpdate
  ring

/-- Positive co-activity strictly increases a weight at positive learning rate. -/
theorem hebbianUpdate_lt_of_pos (weight input output rate : ℝ)
    (hrate : 0 < rate) (hinput : 0 < input) (houtput : 0 < output) :
    weight < hebbianUpdate weight input output rate := by
  unfold hebbianUpdate
  nlinarith [mul_pos (mul_pos hrate houtput) hinput]

/-- The finite-dimensional perceptron update used by the algebraic part of the
learning rule. -/
def perceptronUpdate {ι : Type*} (w x : ι → ℝ)
    (target prediction rate : ℝ) : ι → ℝ :=
  fun i => w i + rate * (target - prediction) * x i

/-- The score change under a perceptron update is the prediction error times
its input self-correlation. -/
theorem dotProduct_perceptronUpdate {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (target prediction rate : ℝ) :
    dotProduct (perceptronUpdate w x target prediction rate) x =
      dotProduct w x + rate * (target - prediction) * dotProduct x x := by
  classical
  unfold dotProduct perceptronUpdate
  simp_rw [add_mul]
  calc
    (∑ i, (w i * x i + rate * (target - prediction) * x i * x i)) =
        (∑ i, w i * x i) +
          ∑ i, (rate * (target - prediction)) * (x i * x i) := by
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = dotProduct w x + rate * (target - prediction) * dotProduct x x := by
      unfold dotProduct
      rw [Finset.mul_sum]

/-- The squared self-correlation of a finite real input vector is nonnegative. -/
theorem dotProduct_self_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ dotProduct x x := by
  classical
  unfold dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- Under a nonnegative update coefficient, a perceptron update cannot decrease
its score on the updated input.  This is an algebraic monotonicity statement,
not a convergence theorem for the perceptron algorithm. -/
theorem perceptron_score_nondec {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (target prediction rate : ℝ)
    (hcoef : 0 ≤ rate * (target - prediction)) :
    dotProduct w x ≤ dotProduct (perceptronUpdate w x target prediction rate) x := by
  rw [dotProduct_perceptronUpdate]
  exact le_add_of_nonneg_right (mul_nonneg hcoef (dotProduct_self_nonneg x))

/-! ## 3. Shannon (1948) Cross-Entropy and Compression Lower Bound -/

/-- Shannon entropy `H(p) = -∑ pᵢ log pᵢ` (in nats) on a finite alphabet. -/
def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i : ι, p i * Real.log (p i)

/-- Expected code-length / cross-entropy `H(p, q) = -∑ pᵢ log qᵢ`. -/
def crossEntropy {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  -∑ i : ι, p i * Real.log (q i)

/-- Kullback–Leibler divergence `D_KL(p ‖ q) = ∑ pᵢ log (pᵢ / qᵢ)`. -/
def klDivergence {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i : ι, p i * Real.log (p i / q i)

/-- Cross-entropy equals source Shannon entropy plus KL divergence excess code length. -/
theorem crossEntropy_eq_shannonEntropy_add_kl
    {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i : ι, 0 < p i) (hq : ∀ i : ι, 0 < q i) :
    crossEntropy p q = shannonEntropy p + klDivergence p q := by
  unfold crossEntropy shannonEntropy klDivergence
  have hlog : ∀ i : ι,
      p i * Real.log (p i / q i) = p i * Real.log (p i) - p i * Real.log (q i) := by
    intro i
    rw [Real.log_div (hp i).ne' (hq i).ne']
    ring
  simp_rw [hlog, Finset.sum_sub_distrib]
  ring

private theorem kl_term_sub_ge_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ a * Real.log (a / b) - (a - b) := by
  have hle : Real.log (b / a) ≤ b / a - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hmul : a * Real.log (b / a) ≤ a * (b / a - 1) :=
    mul_le_mul_of_nonneg_left hle ha.le
  have hlog_inv : Real.log (a / b) = -Real.log (b / a) := by
    rw [Real.log_div ha.ne' hb.ne', Real.log_div hb.ne' ha.ne']
    ring
  have harith : a * (b / a - 1) = b - a := by
    field_simp [ha.ne']
  rw [hlog_inv]
  linarith

/-- **Gibbs' inequality**: KL divergence between strictly positive normalized distributions
on a finite alphabet is non-negative. -/
theorem klDivergence_nonneg
    {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i : ι, 0 < p i) (hq : ∀ i : ι, 0 < q i)
    (hsumP : ∑ i : ι, p i = 1) (hsumQ : ∑ i : ι, q i = 1) :
    0 ≤ klDivergence p q := by
  unfold klDivergence
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ p i * Real.log (p i / q i) - (p i - q i) :=
    fun i _ => kl_term_sub_ge_zero (hp i) (hq i)
  have hsum_nonneg : 0 ≤ ∑ i : ι, (p i * Real.log (p i / q i) - (p i - q i)) :=
    Finset.sum_nonneg hterm
  have hdiff : ∑ i : ι, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hsumP, hsumQ, sub_self]
  rw [Finset.sum_sub_distrib, hdiff, sub_zero] at hsum_nonneg
  exact hsum_nonneg

/-- **Shannon source-coding compression lower bound**: no predictive model `q`
can achieve expected cross-entropy strictly below the source entropy `H(p)`. -/
theorem shannon_compression_lower_bound
    {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i : ι, 0 < p i) (hq : ∀ i : ι, 0 < q i)
    (hsumP : ∑ i : ι, p i = 1) (hsumQ : ∑ i : ι, q i = 1) :
    shannonEntropy p ≤ crossEntropy p q := by
  rw [crossEntropy_eq_shannonEntropy_add_kl hp hq]
  linarith [klDivergence_nonneg hp hq hsumP hsumQ]

/-- Expected code length equals the source entropy iff the model matches the source exactly. -/
theorem klDivergence_eq_zero_iff
    {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i : ι, 0 < p i) (hq : ∀ i : ι, 0 < q i)
    (hsumP : ∑ i : ι, p i = 1) (hsumQ : ∑ i : ι, q i = 1) :
    klDivergence p q = 0 ↔ p = q := by
  constructor
  · intro hkl
    have hsum_eq : ∑ i : ι, (p i * Real.log (p i / q i) - (p i - q i)) = 0 := by
      have hdiff : ∑ i : ι, (p i - q i) = 0 := by
        rw [Finset.sum_sub_distrib, hsumP, hsumQ, sub_self]
      rw [Finset.sum_sub_distrib, hdiff, sub_zero]
      exact hkl
    have hall : ∀ i ∈ Finset.univ, p i * Real.log (p i / q i) - (p i - q i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => kl_term_sub_ge_zero (hp i) (hq i)).mp hsum_eq
    funext i
    have hi := hall i (Finset.mem_univ i)
    by_contra hne
    have hratio_ne : q i / p i ≠ 1 := by
      intro hratio
      apply hne
      have : q i = p i := (div_eq_one_iff_eq (hp i).ne').mp hratio
      exact this.symm
    have hstrict : Real.log (q i / p i) < q i / p i - 1 :=
      Real.log_lt_sub_one_of_pos (div_pos (hq i) (hp i)) hratio_ne
    have hmul : p i * Real.log (q i / p i) < p i * (q i / p i - 1) :=
      mul_lt_mul_of_pos_left hstrict (hp i)
    have hlog_inv : Real.log (p i / q i) = -Real.log (q i / p i) := by
      rw [Real.log_div (hp i).ne' (hq i).ne', Real.log_div (hq i).ne' (hp i).ne']
      ring
    have harith : p i * (q i / p i - 1) = q i - p i := by
      field_simp [(hp i).ne']
    rw [hlog_inv] at hi
    linarith
  · intro hpq
    subst hpq
    simp [klDivergence]

/-! ## 3. Gold (1967) Identification-in-the-Limit Obstruction on Positive Text -/

/-- A positive text presentation of language `L : ℕ → Prop` is a total stream
whose entries all lie in `L` and which eventually emits every element of `L`. -/
def IsPositiveText (L : ℕ → Prop) (t : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, L (t n)) ∧ (∀ x : ℕ, L x → ∃ n : ℕ, t n = x)

/-- First `n` symbols of an infinite stream `t : ℕ → ℕ`. -/
def prefixList (t : ℕ → ℕ) (n : ℕ) : List ℕ :=
  List.ofFn fun i : Fin n => t i.1

/-- Gold-style identification in the limit of exact hypothesis `L` from positive text. -/
def IdentifiesInLimit (M : List ℕ → (ℕ → Prop)) (L : ℕ → Prop) : Prop :=
  ∀ t : ℕ → ℕ, IsPositiveText L t → ∃ N : ℕ, ∀ n ≥ N, M (prefixList t n) = L

private def listMax : List ℕ → ℕ
  | [] => 0
  | a :: w => max a (listMax w)

private theorem le_listMax {x : ℕ} {w : List ℕ} (hx : x ∈ w) : x ≤ listMax w := by
  induction w with
  | nil => simp at hx
  | cons a w ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hmem
      · exact le_max_left x (listMax w)
      · exact le_trans (ih hmem) (le_max_right a (listMax w))

private def prefixText (w : List ℕ) (K n : ℕ) : ℕ :=
  if h : n < w.length then w[n]
  else if n - w.length ≤ K then n - w.length else K

private theorem prefixList_prefixText_append (w : List ℕ) (K n : ℕ) (hn : w.length ≤ n) :
    ∃ ext : List ℕ, prefixList (prefixText w K) n = w ++ ext ∧
      ext.length = n - w.length ∧
      (∀ i : ℕ, i < n - w.length → ext[i]? = some (if i ≤ K then i else K)) ∧
      ∀ x ∈ w ++ ext, x ≤ max (listMax w) K := by
  let tail : List ℕ := List.ofFn fun i : Fin (n - w.length) => if i.1 ≤ K then i.1 else K
  refine ⟨tail, ?_, ?_, ?_, ?_⟩
  · apply List.ext_getElem
    · simp only [prefixList, List.length_ofFn, List.length_append, tail]
      exact (Nat.add_sub_of_le hn).symm
    · intro i hi1 hi2
      simp only [prefixList, List.getElem_ofFn, prefixText]
      by_cases hiw : i < w.length
      · rw [dif_pos hiw, List.getElem_append_left hiw]
      · rw [dif_neg hiw, List.getElem_append_right (Nat.not_lt.mp hiw)]
        simp [tail]
  · simp [tail]
  · intro i hi
    simp [tail, hi]
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hxw | hxtail
    · exact le_trans (le_listMax hxw) (le_max_left _ _)
    · simp only [tail, List.mem_ofFn, Set.mem_range] at hxtail
      rcases hxtail with ⟨i, rfl⟩
      split_ifs with hik
      · exact le_trans hik (le_max_right _ _)
      · exact le_max_right _ _

private theorem isPositiveText_prefixText (w : List ℕ) (K : ℕ)
    (hw : ∀ x ∈ w, x ≤ listMax w) (hK : listMax w ≤ K) :
    IsPositiveText (fun x => x ≤ K) (prefixText w K) := by
  refine ⟨?_, ?_⟩
  · intro n
    dsimp [prefixText]
    split_ifs with h1 h2
    · exact le_trans (hw _ (List.getElem_mem h1)) hK
    · exact h2
    · exact le_rfl
  · intro x hx
    refine ⟨w.length + x, ?_⟩
    have hn : ¬ w.length + x < w.length := by omega
    simp only [prefixText, dif_neg hn, Nat.add_sub_cancel_left]
    rw [if_pos hx]

private theorem ne_true_pred (K : ℕ) : (fun x : ℕ => x ≤ K) ≠ (fun _ => True) := by
  intro heq
  have h := congrFun heq (K + 1)
  have hnot : ¬ K + 1 ≤ K := by omega
  exact hnot (h.mpr trivial)

private theorem gold_stage_step
    (M : List ℕ → (ℕ → Prop))
    (hfin : ∀ k : ℕ, IdentifiesInLimit M (fun x => x ≤ k))
    (w : List ℕ) (r : ℕ) :
    ∃ ext : List ℕ,
      1 ≤ ext.length ∧ r ∈ w ++ ext ∧ M (w ++ ext) ≠ (fun _ => True) := by
  let K := max (listMax w) r
  have hpos := isPositiveText_prefixText w K (fun _ hx => le_listMax hx) (le_max_left _ _)
  obtain ⟨N, hN⟩ := hfin K (prefixText w K) hpos
  let n := max N (w.length + K + 1)
  have hnN : N ≤ n := le_max_left _ _
  have hnw : w.length ≤ n := by omega
  obtain ⟨ext, hpref, hlen, hget, _⟩ := prefixList_prefixText_append w K n hnw
  have hM := hN n hnN
  rw [hpref] at hM
  refine ⟨ext, by omega, ?_, ?_⟩
  · rw [List.mem_append]; right
    have hrK : r ≤ K := le_max_right _ _
    have hrlen : r < n - w.length := by omega
    have hopt := hget r hrlen
    rw [if_pos hrK] at hopt
    have hr_idx : ext[r] = r := by
      have hlen_lt : r < ext.length := by omega
      rw [List.getElem?_eq_getElem hlen_lt] at hopt
      exact Option.some.inj hopt
    rw [← hr_idx]
    exact List.getElem_mem (by omega)
  · rw [hM]
    exact ne_true_pred K

/-- **Gold (1967) Positive-Text Non-Identifiability Theorem**:
no learner `M` can identify in the limit from positive text all bounded finite languages
`{x | x ≤ k}` together with the single infinite language `ℕ = {x | True}`. -/
theorem gold_1967_superfinite_nonidentifiable :
    ¬ ∃ M : List ℕ → (ℕ → Prop),
      IdentifiesInLimit M (fun _ => True) ∧ (∀ k : ℕ, IdentifiesInLimit M (fun x => x ≤ k)) := by
  rintro ⟨M, hInf, hFin⟩
  let step : ℕ → List ℕ → List ℕ := fun r w =>
    w ++ Classical.choose (gold_stage_step M hFin w r)
  let seq : ℕ → List ℕ := Nat.rec [] step
  have hseq_succ : ∀ r : ℕ,
      ∃ ext : List ℕ, seq (r + 1) = seq r ++ ext ∧
        1 ≤ ext.length ∧ r ∈ seq (r + 1) ∧ M (seq (r + 1)) ≠ (fun _ => True) := by
    intro r
    have hspec := Classical.choose_spec (gold_stage_step M hFin (seq r) r)
    exact ⟨Classical.choose (gold_stage_step M hFin (seq r) r), rfl, hspec⟩
  have hlen_succ : ∀ r : ℕ, (seq r).length + 1 ≤ (seq (r + 1)).length := by
    intro r
    obtain ⟨ext, heq, h1, _, _⟩ := hseq_succ r
    rw [heq, List.length_append]
    omega
  have hlen_ge : ∀ r : ℕ, r ≤ (seq r).length := by
    intro r
    induction r with
    | zero => simp [seq]
    | succ r ih => exact le_trans (Nat.succ_le_succ ih) (hlen_succ r)
  have hget_mono : ∀ r k : ℕ, r ≤ k → ∀ i : ℕ, (hi : i < (seq r).length) →
      ∃ hik : i < (seq k).length, (seq k)[i]'hik = (seq r)[i]'hi := by
    intro r k hrk
    induction k with
    | zero =>
        have hr0 : r = 0 := Nat.le_zero.mp hrk
        subst hr0
        intro i hi
        exact ⟨hi, rfl⟩
    | succ k ih =>
        by_cases hlt : r ≤ k
        · intro i hi
          obtain ⟨hik, heq⟩ := ih hlt i hi
          obtain ⟨ext, hseq, _, _, _⟩ := hseq_succ k
          have hik' : i < (seq (k + 1)).length := by rw [hseq, List.length_append]; omega
          refine ⟨hik', ?_⟩
          have hget : (seq (k + 1))[i]'hik' = (seq k)[i]'hik := by
            simp only [hseq]
            exact List.getElem_append_left hik
          rw [hget, heq]
        · have hrk' : r = k + 1 := by omega
          subst hrk'
          intro i hi
          exact ⟨hi, rfl⟩
  let t : ℕ → ℕ := fun i => (seq (i + 1))[i]'(by have := hlen_ge (i + 1); omega)
  have hpref_seq : ∀ r : ℕ, prefixList t (seq r).length = seq r := by
    intro r
    apply List.ext_getElem
    · simp [prefixList]
    · intro i hi1 hi2
      simp only [prefixList, List.getElem_ofFn, t]
      by_cases hle : i + 1 ≤ r
      · obtain ⟨hik, heq⟩ := hget_mono (i + 1) r hle i (by have := hlen_ge (i + 1); omega)
        exact heq.symm
      · have hrle : r ≤ i + 1 := by omega
        obtain ⟨hik, heq⟩ := hget_mono r (i + 1) hrle i hi2
        exact heq
  have ht_pos : IsPositiveText (fun _ => True) t := by
    refine ⟨fun _ => trivial, fun r _ => ?_⟩
    obtain ⟨_, _, _, hmem, _⟩ := hseq_succ r
    rw [← hpref_seq (r + 1)] at hmem
    simp only [prefixList, List.mem_ofFn, Set.mem_range] at hmem
    rcases hmem with ⟨i, hi⟩
    exact ⟨i.1, hi⟩
  obtain ⟨N, hN⟩ := hInf t ht_pos
  let r := N + 1
  have hr_len : N ≤ (seq r).length := le_trans (Nat.le_succ N) (hlen_ge r)
  have hM := hN (seq r).length hr_len
  rw [hpref_seq r] at hM
  obtain ⟨_, _, _, _, hne⟩ := hseq_succ N
  exact hne hM

end InfoGeometry.LLM.EarlyLearningFoundations

end noncomputable section
