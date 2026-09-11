/-
Copyright (c) 2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topological.FibonacciAnyons
import InfoGeometry.Topological.FibonacciColimit
import Mathlib.Order.Zorn

/-!
# InfoGeometry.Canonical.BraidColimitZornBarrier

Bare algebraic stage and subset lemmas for Fibonacci braid data.

This file does **not** construct the Artin braid-group direct limit `B_∞`, does
not prove a shift automorphism of that group, and does not build an anyonic
representation.  It proves:

* injectivity of a concrete stage-extension record map;
* an upper-bound lemma for nonempty families of successor-closed stage sets;
* a Zorn-style maximal successor-closed stage set above a seed.

## Theorems (bare algebraic version)

1. **Stage-Extension Injectivity**: the record map from stage `n` to `n+1`
   is injective because it preserves the scalar fields definitionally.

2. **Successor-Closed Stage Set Upper Bound**: every nonempty family of
   successor-closed stage sets has a successor-closed union upper bound.

3. **Zorn Maximality**: Zorn's Lemma applied to these stage sets yields a
   maximal successor-closed stage set above a seed.

This module stays at the semiring/algebraic level (no full category theory)
and builds on the existing `DirectLimitSuperClosureLemmas` infrastructure.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Canonical.BraidColimitZornBarrier

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Topological.FibonacciAnyons


/-! ## 1. Fibonacci Braid Stages and Stage Extension -/

section FibonacciBraidStages

/--
A Fibonacci braid stage at level n carries the braid data:
R-matrix, F-matrix, B-matrix = F R F, and the Artin relation
R B R = B R B.
-/
structure FibBraidStage (n : ℕ) where
  q : ℝ
  qInv : ℝ
  tau : ℝ
  sqrtTau : ℝ
  /-- The Artin relation holds at this stage. -/
  artinHolds : R_matrixOf (K := ℝ) q qInv * B_matrixOf (K := ℝ) q qInv tau sqrtTau *
               R_matrixOf (K := ℝ) q qInv =
               B_matrixOf (K := ℝ) q qInv tau sqrtTau * R_matrixOf (K := ℝ) q qInv *
               B_matrixOf (K := ℝ) q qInv tau sqrtTau

/--
The canonical stage-extension map: embeds stage n data into stage (n+1)
by the identity on the scalar parameters (the matrices are size-independent).
-/
def fibStageExtend {n : ℕ} (s : FibBraidStage n) : FibBraidStage (n + 1) where
  q := s.q
  qInv := s.qInv
  tau := s.tau
  sqrtTau := s.sqrtTau
  artinHolds := s.artinHolds

/--
Stage-extension map for the record model: it re-indexes the stage parameter
from `n` to `n+1` while preserving the scalar fields and the supplied Artin
relation witness.

This is not a theorem about the shift automorphism of an Artin braid-group
direct limit.
-/
def shiftEndofunctor {n : ℕ} (s : FibBraidStage n) : FibBraidStage (n + 1) :=
  fibStageExtend s

/--
The stage-extension record map is injective.

This theorem does not assert surjectivity, a fixed point, or a `B_∞` colimit
automorphism.
-/
theorem shift_is_injective {n : ℕ} (s t : FibBraidStage n)
    (h : fibStageExtend s = fibStageExtend t) : s = t := by
  cases s; cases t
  simp [fibStageExtend] at h
  simp [h]

end FibonacciBraidStages


/-! ## 2. The Inductive Poset of Fibonacci Fusion Sub-Stages -/

section InductivePoset

/--
A Fibonacci fusion sub-stage of a directed system of braid stages.
We model this as a subset of stages that is closed under the stage extension.
-/
structure FibFusionSubset where
  /-- Which stages are included. -/
  stages : Set ℕ
  /-- The subset is nonempty. -/
  nonempty : stages.Nonempty
  /-- Closed under the successor: if n is in the subset, so is n+1. -/
  succClosed : ∀ n, n ∈ stages → n + 1 ∈ stages

/-- Inclusion order on fusion subsets. -/
abbrev fusionInclusion (C D : FibFusionSubset) : Prop :=
  C.stages ⊆ D.stages

/--
Theorem 2: Inductive Property.

Every chain of Fibonacci fusion subsets has an upper bound (their union).

Proof: Take the union of all stages in the chain. Since each member is
closed under successor, the union is also closed under successor.
-/
theorem fusion_poset_inductive
    (chain : Set FibFusionSubset)
    (_hchain : IsChain fusionInclusion chain)
    (hne : chain.Nonempty) :
    ∃ C : FibFusionSubset,
      (∀ D ∈ chain, fusionInclusion D C) := by
  -- Construct the union of all stages in the chain
  let unionStages : Set ℕ := {n | ∃ D ∈ chain, n ∈ D.stages}
  have hne' : unionStages.Nonempty := by
    rcases hne with ⟨D, hD⟩
    rcases D.nonempty with ⟨n, hn⟩
    exact ⟨n, D, hD, hn⟩
  have hsucc : ∀ n, n ∈ unionStages → n + 1 ∈ unionStages := by
    intro n hn
    rcases hn with ⟨D, hD, hnD⟩
    exact ⟨D, hD, D.succClosed n hnD⟩
  refine ⟨{ stages := unionStages, nonempty := hne', succClosed := hsucc }, ?_⟩
  intro D hD n hn
  exact ⟨D, hD, hn⟩

end InductivePoset


/-! ## 3. Zorn Barrier: Maximal Fibonacci Fusion Subset -/

section ZornBarrier

/--
Theorem 3: existence of a maximal successor-closed Fibonacci stage subset.

Given any Fibonacci fusion subset as seed, there exists a maximal
fusion subset dominating it.

This is an order-theoretic maximality statement only; it does not construct
braid representations or prove phase stabilization.
-/
theorem zorn_maximal_fusion_subset
    (C0 : FibFusionSubset) :
    ∃ C_max : FibFusionSubset,
      fusionInclusion C0 C_max ∧
      ∀ D : FibFusionSubset,
        fusionInclusion C_max D → D = C_max := by
  let S : Set (Set ℕ) := {s | ∃ C : FibFusionSubset, fusionInclusion C0 C ∧ C.stages = s}
  have hSn : S.Nonempty := ⟨C0.stages, C0, (fun n hn => hn), rfl⟩
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hchain'
    by_cases hcne : c.Nonempty
    · rcases hcne with ⟨s0, hs0⟩
      let U : Set ℕ := {n | ∃ s ∈ c, n ∈ s}
      have hU_nonempty : U.Nonempty := by
        have hmem : s0 ∈ S := hcS hs0
        rcases hmem with ⟨C, _, hstages⟩
        rcases C.nonempty with ⟨n, hn⟩
        exact ⟨n, s0, hs0, hstages ▸ hn⟩
      have hU_succ : ∀ n, n ∈ U → n + 1 ∈ U := by
        intro n hn
        rcases hn with ⟨s, hs, hns⟩
        have hmem : s ∈ S := hcS hs
        rcases hmem with ⟨C, _, hstages⟩
        exact ⟨s, hs, hstages ▸ C.succClosed n (hstages.symm ▸ hns)⟩
      let C_U : FibFusionSubset := ⟨U, hU_nonempty, hU_succ⟩
      have hC0U : fusionInclusion C0 C_U := by
        intro n hn
        have hmem : s0 ∈ S := hcS hs0
        rcases hmem with ⟨C, hC0C, hstages⟩
        exact ⟨s0, hs0, hstages ▸ hC0C hn⟩
      refine ⟨U, ⟨C_U, hC0U, rfl⟩, ?_⟩
      intro s hs n hn
      exact ⟨s, hs, hn⟩
    · refine ⟨C0.stages, ⟨C0, (fun n hn => hn), rfl⟩, fun s hs => (hcne ⟨s, hs⟩).elim⟩
  obtain ⟨m, hmMax⟩ := zorn_subset S hchain
  rcases hmMax with ⟨hmS, hmMax'⟩
  rcases hmS with ⟨C_max, hC0max, hm⟩
  refine ⟨C_max, hC0max, ?_⟩
  intro D hmaxD
  have hDS : D.stages ∈ S := ⟨D, Set.Subset.trans hC0max hmaxD, rfl⟩
  have hmSub : m ⊆ D.stages := by
    rw [hm.symm]
    exact hmaxD
  have hDSubM : D.stages ⊆ m := hmMax' hDS hmSub
  have hEq : D.stages = m := Set.Subset.antisymm hDSubM hmSub
  have hStages : D.stages = C_max.stages := hEq.trans hm.symm
  cases D; cases C_max; simp_all [fusionInclusion]
