import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import InfoGeometry.Routing.FiniteSoftmax

open Matrix
open Topology
open scoped BigOperators

namespace DeterministicArgmaxAttention

variable {N M : ℕ} [NeZero N] [NeZero M]

/-! ### 1. Finite Deterministic Routing -/

/-- The deterministic routing matrix `Aᵢⱼ = 1` exactly at the selected key
`σ i`, and zero elsewhere. -/
def deterministicAttention (σ : Fin N → Fin M) : Matrix (Fin N) (Fin M) ℝ :=
  fun i j => if j = σ i then 1 else 0

omit [NeZero N] in
/-- In inverse-temperature coordinates, rowwise softmax converges in the
finite matrix topology to deterministic routing when each row has a unique
strict maximum. The parameter `β` tends to `+∞`, corresponding to temperature
`1 / β` tending to zero through positive values. -/
theorem softmaxMatrix_tendsto_deterministic_of_unique_max
    (scores : Fin N → Fin M → ℝ) (σ : Fin N → Fin M)
    (hmax : ∀ i j, j ≠ σ i → scores i j < scores i (σ i)) :
    Filter.Tendsto
      (fun β : ℝ => fun i j =>
        InfoGeometry.Routing.FiniteSoftmax.weight (scores i) (1 / β) j)
      Filter.atTop (𝓝 (deterministicAttention σ)) := by
  classical
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  simpa [deterministicAttention] using
    (InfoGeometry.Routing.FiniteSoftmax.weight_tendsto_indicator_of_unique_max
      (scores i) (σ i) (fun j hj => hmax i j hj) j)

omit [NeZero N] [NeZero M] in
/-- Each row of the deterministic attention matrix sums to 1. -/
theorem deterministic_attention_row_sum (σ : Fin N → Fin M) (i : Fin N) :
    (∑ j : Fin M, deterministicAttention σ i j) = 1 := by
  dsimp [deterministicAttention]
  have h : (∑ j : Fin M, if j = σ i then (1 : ℝ) else 0) = if σ i = σ i then (1 : ℝ) else 0 := by
    apply Finset.sum_eq_single (σ i)
    · intro j _ hj
      rw [if_neg hj]
    · intro hi
      exact False.elim (hi (Finset.mem_univ (σ i)))
  rw [h, if_pos rfl]

/-- Normalized bipartite joint distribution P(i, j) = (1 / N) * A*_{i, j}. -/
noncomputable def jointDistribution (σ : Fin N → Fin M) : Matrix (Fin N) (Fin M) ℝ :=
  fun i j => (1 / (N : ℝ)) * deterministicAttention σ i j

/-- Query marginal distribution p(i) = 1 / N. -/
noncomputable def rowMarginal (σ : Fin N → Fin M) (i : Fin N) : ℝ :=
  ∑ j : Fin M, jointDistribution σ i j

omit [NeZero N] [NeZero M] in
theorem rowMarginal_eq_uniform (σ : Fin N → Fin M) (i : Fin N) :
    rowMarginal σ i = 1 / (N : ℝ) := by
  dsimp [rowMarginal, jointDistribution]
  rw [← Finset.mul_sum, deterministic_attention_row_sum σ i, mul_one]

/-- Key marginal distribution q(j) = ∑_i P(i, j). -/
noncomputable def colMarginal (σ : Fin N → Fin M) (j : Fin M) : ℝ :=
  ∑ i : Fin N, jointDistribution σ i j

/-! ### 2. Entropic Quantities -/

/-- Marginal Key Shannon Entropy: H(K) = - ∑_j q(j) * ln(q(j)). -/
noncomputable def entropyKey (σ : Fin N → Fin M) : ℝ :=
  - ∑ j : Fin M, colMarginal σ j * Real.log (colMarginal σ j)

/-- Conditional Key Entropy given query i: H(K | Q = i) = - ∑_j A_{i, j} * ln(A_{i, j}). -/
noncomputable def conditionalEntropyAt (σ : Fin N → Fin M) (i : Fin N) : ℝ :=
  - ∑ j : Fin M, deterministicAttention σ i j * Real.log (deterministicAttention σ i j)

/-- Conditional Entropy: H(K | Q) = - ∑_{i, j} P(i, j) * ln(A_{i, j}). -/
noncomputable def conditionalEntropy (σ : Fin N → Fin M) : ℝ :=
  - ∑ i : Fin N, ∑ j : Fin M, jointDistribution σ i j * Real.log (deterministicAttention σ i j)

/-- Shannon Mutual Information: I(Q; K) = H(K) - H(K | Q). -/
noncomputable def mutualInformation (σ : Fin N → Fin M) : ℝ :=
  entropyKey σ - conditionalEntropy σ

/-! ### 3. Vanishing Conditional Entropy (H(K | Q) = 0) -/

omit [NeZero N] [NeZero M] in
/-- Pointwise indicator vanishing: For x ∈ {0, 1}, x * ln(x) = 0. -/
lemma deterministic_entry_mul_log (σ : Fin N → Fin M) (i : Fin N) (j : Fin M) :
    deterministicAttention σ i j * Real.log (deterministicAttention σ i j) = 0 := by
  dsimp [deterministicAttention]
  split_ifs with h
  · rw [Real.log_one, mul_zero]
  · rw [zero_mul]

omit [NeZero N] [NeZero M] in
/-- For deterministic routing, the conditional entropy at any query node
vanishes: H(K | Q = i) = 0. -/
theorem conditionalEntropyAt_zero (σ : Fin N → Fin M) (i : Fin N) :
    conditionalEntropyAt σ i = 0 := by
  dsimp [conditionalEntropyAt]
  have h_sum : (∑ j : Fin M, deterministicAttention σ i j * Real.log (deterministicAttention σ i j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact deterministic_entry_mul_log σ i j
  rw [h_sum, neg_zero]

omit [NeZero N] [NeZero M] in
/-- Total conditional entropy vanishes for deterministic routing. -/
theorem conditionalEntropy_zero (σ : Fin N → Fin M) :
    conditionalEntropy σ = 0 := by
  dsimp [conditionalEntropy, jointDistribution]
  have h_term : ∀ (i : Fin N) (j : Fin M),
      (1 / (N : ℝ)) * deterministicAttention σ i j * Real.log (deterministicAttention σ i j) = 0 := by
    intro i j
    have h_alg : (1 / (N : ℝ)) * deterministicAttention σ i j * Real.log (deterministicAttention σ i j) =
        (1 / (N : ℝ)) * (deterministicAttention σ i j * Real.log (deterministicAttention σ i j)) := by ring
    rw [h_alg, deterministic_entry_mul_log σ i j, mul_zero]
  have h_inner : ∀ (i : Fin N),
      (∑ j : Fin M, (1 / (N : ℝ)) * deterministicAttention σ i j * Real.log (deterministicAttention σ i j)) = 0 := by
    intro i
    apply Finset.sum_eq_zero
    intro j _
    exact h_term i j
  have h_outer : (∑ i : Fin N, ∑ j : Fin M,
      (1 / (N : ℝ)) * deterministicAttention σ i j * Real.log (deterministicAttention σ i j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact h_inner i
  rw [h_outer, neg_zero]

/-! ### 4. Mutual Information Saturation (I(Q; K) = H(K)) -/

omit [NeZero N] [NeZero M] in
/-- For deterministic routing, mutual information equals the entropy of the
key marginal because conditional key entropy vanishes. -/
theorem mutualInformation_eq_entropyKey (σ : Fin N → Fin M) :
    mutualInformation σ = entropyKey σ := by
  dsimp [mutualInformation]
  rw [conditionalEntropy_zero σ, sub_zero]

/-! ### 5. Bijective Routing: Maximum Entropic Capacity -/

omit [NeZero N] in
/-- For bijective routing, the key marginals are uniform: q(j) = 1 / N. -/
theorem colMarginal_bijective_uniform (e : Fin N ≃ Fin N) (j : Fin N) :
    colMarginal (N := N) (M := N) e j = 1 / (N : ℝ) := by
  dsimp [colMarginal, jointDistribution, deterministicAttention]
  have h_single : (∑ i : Fin N, (1 / (N : ℝ)) * (if j = e i then (1 : ℝ) else 0)) =
      (1 / (N : ℝ)) * (if j = e (e.symm j) then (1 : ℝ) else 0) := by
    apply Finset.sum_eq_single (e.symm j)
    · intro i _ hi
      have hne : ¬(j = e i) := by
        intro heq
        have h_symm : e.symm j = i := by rw [heq, Equiv.symm_apply_apply]
        exact hi h_symm.symm
      rw [if_neg hne, mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ (e.symm j)))
  rw [h_single, Equiv.apply_symm_apply, if_pos rfl, mul_one]

/-- Maximal Information Theorem: If deterministic attention is a permutation,
    the Mutual Information reaches the absolute channel capacity ln(N). -/
theorem mutualInformation_bijective_eq_log_N (e : Fin N ≃ Fin N) :
    mutualInformation (N := N) (M := N) e = Real.log (N : ℝ) := by
  rw [mutualInformation_eq_entropyKey]
  dsimp [entropyKey]
  simp_rw [colMarginal_bijective_uniform e]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  rw [nsmul_eq_mul (N : ℕ) ((1 / (N : ℝ)) * Real.log (1 / (N : ℝ)))]
  have h_alg : (N : ℝ) * ((1 / (N : ℝ)) * Real.log (1 / (N : ℝ))) = Real.log (1 / (N : ℝ)) := by
    calc (N : ℝ) * ((1 / (N : ℝ)) * Real.log (1 / (N : ℝ)))
      _ = ((N : ℝ) * (1 / (N : ℝ))) * Real.log (1 / (N : ℝ)) := by ring
      _ = 1 * Real.log (1 / (N : ℝ)) := by rw [mul_one_div_cancel hN]
      _ = Real.log (1 / (N : ℝ)) := by ring
  rw [h_alg, Real.log_div one_ne_zero hN, Real.log_one, zero_sub, neg_neg]

/-! ### 6. Upper Fréchet-Hoeffding Copula Bound (Comonotonicity) -/

/-- Joint cumulative distribution H(i, j) = ∑_{a ≤ i, b ≤ j} P(a, b). -/
noncomputable def jointCDF (σ : Fin N → Fin M) (i : Fin N) (j : Fin M) : ℝ :=
  ∑ a : Fin N, ∑ b : Fin M, if a ≤ i ∧ b ≤ j then jointDistribution σ a b else 0

/-- Row marginal cumulative distribution F(i) = ∑_{a ≤ i} p(a) = (i + 1) / N. -/
noncomputable def rowCDF (i : Fin N) : ℝ :=
  (i.val + 1 : ℝ) / (N : ℝ)

/-- Column marginal cumulative distribution G(j) = ∑_{b ≤ j} q(b) = (j + 1) / N. -/
noncomputable def colCDF (j : Fin N) : ℝ :=
  (j.val + 1 : ℝ) / (N : ℝ)

/-- The upper Fréchet-Hoeffding comonotonic copula bound M(u, v) = min u v. -/
def frechetHoeffdingUpper (u v : ℝ) : ℝ :=
  min u v

lemma min_div_right_real (a b c : ℝ) (hc : 0 ≤ c) : min (a / c) (b / c) = (min a b) / c := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left]
    exact div_le_div_of_nonneg_right h hc
  · push_neg at h
    rw [min_eq_right h.le, min_eq_right]
    exact div_le_div_of_nonneg_right h.le hc

omit [NeZero N] in
/-- Under identity routing, the discrete joint CDF at grid thresholds equals
the minimum of the two discrete marginal CDF values. -/
theorem identity_attention_is_frechet_hoeffding_upper (i j : Fin N) :
    jointCDF (N := N) (M := N) id i j = frechetHoeffdingUpper (rowCDF i) (colCDF j) := by
  dsimp [jointCDF, frechetHoeffdingUpper, rowCDF, colCDF, jointDistribution, deterministicAttention, id]
  have h_inner : ∀ a : Fin N, (∑ b : Fin N,
      if a ≤ i ∧ b ≤ j then (1 / (N : ℝ)) * (if b = a then (1 : ℝ) else 0) else 0) =
      if a ≤ i ∧ a ≤ j then (1 / (N : ℝ)) else 0 := by
    intro a
    have h_split : (∑ b : Fin N, if a ≤ i ∧ b ≤ j then (1 / (N : ℝ)) * (if b = a then (1 : ℝ) else 0) else 0) =
        if a ≤ i ∧ a ≤ j then (1 / (N : ℝ)) * (if a = a then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_eq_single a
      · intro b _ hb
        have : ¬(b = a) := hb
        rw [if_neg this, mul_zero]
        split_ifs <;> rfl
      · intro ha
        exact False.elim (ha (Finset.mem_univ a))
    rw [h_split, if_pos rfl, mul_one]
  simp_rw [h_inner]
  -- Count the indices satisfying a ≤ i ∧ a ≤ j, i.e., a.val ≤ min(i.val, j.val)
  let k := min i.val j.val
  have h_count : (∑ a : Fin N, if a ≤ i ∧ a ≤ j then (1 / (N : ℝ)) else 0) =
      ((k + 1 : ℝ) / (N : ℝ)) := by
    have h_card : (Finset.filter (fun a : Fin N => a ≤ i ∧ a ≤ j) Finset.univ).card = k + 1 := by
      have heq : (Finset.filter (fun a : Fin N => a ≤ i ∧ a ≤ j) Finset.univ) =
          (Finset.Iic (⟨k, lt_of_le_of_lt (min_le_left i.val j.val) i.isLt⟩ : Fin N)) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
        change (a ≤ i ∧ a ≤ j) ↔ a.val ≤ k
        exact ⟨fun ⟨h1, h2⟩ => le_min h1 h2, fun h => ⟨le_trans h (min_le_left _ _), le_trans h (min_le_right _ _)⟩⟩
      rw [heq]
      exact Fin.card_Iic _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [h_card]
    push_cast
    ring
  rw [h_count]
  dsimp [k]
  rw [Nat.cast_min]
  have h_min_add : ((min (i.val : ℝ) (j.val : ℝ)) + 1) = min ((i.val : ℝ) + 1) ((j.val : ℝ) + 1) := by
    rw [← min_add_add_right (i.val : ℝ) (j.val : ℝ) 1]
  rw [h_min_add]
  have hN_pos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [← min_div_right_real (i.val + 1 : ℝ) (j.val + 1 : ℝ) (N : ℝ) hN_pos]

end DeterministicArgmaxAttention
