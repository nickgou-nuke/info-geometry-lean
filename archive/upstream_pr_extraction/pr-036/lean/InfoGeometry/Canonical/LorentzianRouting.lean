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
behavior of Lorentzian InfoGeometry.Canonical.Attention.
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
    (ctx : InfoGeometry.Canonical.Attention.ContextWindow n (ℝ × ℝ) V)
    (β : ℝ) (hβ : 0 < β)
    (i j : Fin n)
    (hi : splitB11 q (ctx.keys i) > 0)
    (hj : splitB11 q (ctx.keys j) < 0) :
    lorentzianAttentionWeights q ctx β i > lorentzianAttentionWeights q ctx β j := by
  unfold lorentzianAttentionWeights InfoGeometry.Canonical.Attention.attentionWeights
  set params := lorentzianAttentionParams q ctx
  
  haveI : Nonempty (Fin n) := ⟨⟨0, by exact_mod_cast Fact.out⟩⟩
  set Z := partition params β
  
  have hZpos : 0 < Z := by
    apply partition_pos -- From GrandCanonical.Core
  
  unfold gibbsWeight
  
  have hscore : splitB11 q (ctx.keys j) < splitB11 q (ctx.keys i) := by
    linarith
  apply (div_lt_div_iff_of_pos_right hZpos).2
  apply Real.exp_lt_exp.mpr
  change (-β * (-(splitB11 q (ctx.keys j)))) <
    (-β * (-(splitB11 q (ctx.keys i))))
  nlinarith [hscore, hβ]

end InfoGeometry.Canonical.Attention
