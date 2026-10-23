/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

namespace InfoGeometry.Routing.BlockCausalSinkhorn

open scoped BigOperators
noncomputable section
variable {C K D : Type*}
variable [Fintype C] [LinearOrder C] [Fintype K] [Fintype D]

/-!
## 1. Block-Lower-Triangular Causal Prefix Weights & Online Partition Function
-/

/-- An inter-chunk weight family `Ω : C → C → K → ℝ` is block-causal if it vanishes
    whenever the key chunk `s` lies strictly in the future of the query chunk `t` (`t < s`). -/
def IsBlockCausalWeights (Ω : C → C → K → ℝ) : Prop :=
  ∀ (t s : C) (k : K), t < s → Ω t s k = 0

/-- The cumulative causal partition function `Z_{≤ t, k} = ∑_{r ≤ t} exp(m_{r, k})`
    over all chunks `r ≤ t`. -/
noncomputable def causalPrefixPart (m : C → K → ℝ) (t : C) (k : K) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r => r ≤ t), Real.exp (m r k)

/-- The exact online block-causal inter-chunk barycentric weights:
    `Ω_{t, s, k} = exp(m_{s, k}) / Z_{≤ t, k}` if `s ≤ t`, and `0` if `s > t`. -/
noncomputable def causalPrefixWeights (m : C → K → ℝ) (t s : C) (k : K) : ℝ :=
  if s ≤ t then Real.exp (m s k) / causalPrefixPart m t k else 0

/-- Because `t ≤ t`, the causal prefix filter is always nonempty and `Z_{≤ t, k} > 0`. -/
theorem causalPrefixPart_pos (m : C → K → ℝ) (t : C) (k : K) :
    0 < causalPrefixPart m t k := by
  unfold causalPrefixPart
  apply Finset.sum_pos
  · intro r _
    exact Real.exp_pos (m r k)
  · exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, le_refl t⟩⟩

/-- **Block-Causal Support & Simplex Normalization (`causalPrefixWeights_properties`):**
    1. `causalPrefixWeights m` satisfies `IsBlockCausalWeights` (`t < s → Ω_{t,s,k} = 0`).
    2. Every weight is nonnegative (`0 ≤ Ω_{t,s,k}`).
    3. For every query chunk `t` and channel `k`, the weights sum to `1` over `s : C`. -/
theorem causalPrefixWeights_properties (m : C → K → ℝ) :
    IsBlockCausalWeights (causalPrefixWeights m) ∧
    (∀ t s k, 0 ≤ causalPrefixWeights m t s k) ∧
    (∀ t k, ∑ s : C, causalPrefixWeights m t s k = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t s k hts
    unfold causalPrefixWeights
    rw [if_neg (not_le_of_gt hts)]
  · intro t s k
    unfold causalPrefixWeights
    split_ifs with hst
    · exact div_nonneg (le_of_lt (Real.exp_pos (m s k)))
        (le_of_lt (causalPrefixPart_pos m t k))
    · norm_num
  · intro t k
    unfold causalPrefixWeights
    rw [← Finset.sum_filter, ← Finset.sum_div]
    exact div_self (ne_of_gt (causalPrefixPart_pos m t k))

/-- **Prefix Invariance of Causal Weights (`causalPrefixWeights_congr_of_le`):**
    If two chunk log-partition sequences `m₁, m₂` agree on all chunks `r ≤ t`,
    then `causalPrefixWeights m₁ t s k = causalPrefixWeights m₂ t s k` for ALL `s : C`. -/
theorem causalPrefixWeights_congr_of_le {m₁ m₂ : C → K → ℝ} {t : C}
    (h_eq : ∀ r ≤ t, m₁ r = m₂ r) (s : C) (k : K) :
    causalPrefixWeights m₁ t s k = causalPrefixWeights m₂ t s k := by
  have h_part : causalPrefixPart m₁ t k = causalPrefixPart m₂ t k := by
    unfold causalPrefixPart
    apply Finset.sum_congr rfl
    intro r hr
    have hrt : r ≤ t := (Finset.mem_filter.mp hr).2
    rw [h_eq r hrt]
  unfold causalPrefixWeights
  split_ifs with hst
  · rw [h_eq s hst, h_part]
  · rfl

/-!
## 2. Block-Lower-Triangular Prefix Pooling Operator
-/

/-- Causal prefix pooling of chunk matrices `X : C → Matrix K D ℝ` using weights `Ω`:
    `(causalPrefixPool Ω X t)_{k, d} = ∑_{s : C} Ω_{t, s, k} * X_{s, k, d}`. -/
def causalPrefixPool (Ω : C → C → K → ℝ) (X : C → Matrix K D ℝ) (t : C) :
    Matrix K D ℝ :=
  fun k d => ∑ s : C, Ω t s k * X s k d

/-- **Zero Future-Chunk Leakage of Prefix Pooling (`causalPrefixPool_congr_of_le`):**
    For any block-causal weight families `Ω₁, Ω₂` and chunk tensor sequences `X₁, X₂`,
    if `Ω₁ t s = Ω₂ t s` and `X₁ s = X₂ s` for all `s ≤ t`, then the pooled prefix
    states at chunk `t` are identically equal regardless of arbitrary changes at `s > t`. -/
theorem causalPrefixPool_congr_of_le
    {Ω₁ Ω₂ : C → C → K → ℝ}
    (hΩ₁ : IsBlockCausalWeights Ω₁) (hΩ₂ : IsBlockCausalWeights Ω₂)
    {X₁ X₂ : C → Matrix K D ℝ} {t : C}
    (hΩ_eq : ∀ s ≤ t, Ω₁ t s = Ω₂ t s)
    (hX_eq : ∀ s ≤ t, X₁ s = X₂ s) :
    causalPrefixPool Ω₁ X₁ t = causalPrefixPool Ω₂ X₂ t := by
  ext k d
  unfold causalPrefixPool
  apply Finset.sum_congr rfl
  intro s _
  rcases le_or_gt s t with hst | hts
  · have h1 : Ω₁ t s k = Ω₂ t s k := congrFun (hΩ_eq s hst) k
    have h2 : X₁ s k d = X₂ s k d := congrFun (congrFun (hX_eq s hst) k) d
    rw [h1, h2]
  · rw [hΩ₁ t s k hts, hΩ₂ t s k hts, zero_mul, zero_mul]


end
end InfoGeometry.Routing.BlockCausalSinkhorn
