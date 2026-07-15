import InfoGeometry.Canonical.AttentionSplit
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic

/-!
# Lorentzian Routing Analysis

This module analyzes how the causal structure of the split-signature (1,1)
metric affects the attention weights.

We prove that "Timelike" Query-Key alignments (where scores are positive)
dominate the thermodynamic routing compared to "Spacelike" alignments
(where scores are negative), formally verifying the causal filtering 
behavior of Lorentzian Attention.
-/

namespace InfoGeometry.Canonical.Attention

open InfoGeometry.Clifford
open InfoGeometry.GrandCanonical
open scoped BigOperators

variable {n : ℕ} [Fact (0 < n)]
variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

omit [AddCommMonoid V] [Module ℝ V] in
/-- 
Theorem: Timelike tokens have higher thermodynamic weight than Spacelike tokens.
If token `i` is Timelike-aligned with query `q` and token `j` is 
Spacelike-aligned, and all other things are equal (key/query magnitudes),
then the router will pay more attention to token `i`.
-/
theorem timelike_dominance
    (q : ℝ × ℝ)
    (ctx : _root_.Attention.ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) (hβ : 0 < β)
    (i j : Fin n)
    (hi : splitB11 q (ctx.keys i) > 0)
    (hj : splitB11 q (ctx.keys j) < 0) :
    lorentzianAttentionWeights q ctx β i > lorentzianAttentionWeights q ctx β j := by
  unfold lorentzianAttentionWeights _root_.Attention.attentionWeights
  set params := lorentzianAttentionParams q ctx
  
  haveI : Nonempty (Fin n) := ⟨⟨0, by exact_mod_cast Fact.out⟩⟩
  set Z := partition params β
  
  have hZpos : 0 < Z := by
    apply partition_pos -- From GrandCanonical.Core
  
  unfold gibbsWeight
  
  -- Compare fractions: exp_i / Z > exp_j / Z
  rw [gt_iff_lt, div_lt_div_iff_of_pos_right hZpos]
  apply Real.exp_lt_exp.mpr
  
  -- Compare energies: -β * energy_i > -β * energy_j
  dsimp [params, lorentzianAttentionParams, _root_.Attention.attentionParams, _root_.Attention.interactionEnergy, splitB11, splitB11_expand]
  
  -- Now we have: β * (q.1 * (ctx.keys i).1 - q.2 * (ctx.keys i).2) > β * (q.1 * (ctx.keys j).1 - q.2 * (ctx.keys j).2)
  -- Which matches the definitions of hi and hj via splitB11_expand.
  rw [splitB11_expand] at hi hj
  nlinarith

end InfoGeometry.Canonical.Attention
