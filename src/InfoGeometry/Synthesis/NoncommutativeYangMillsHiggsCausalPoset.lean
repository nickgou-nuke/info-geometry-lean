/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Proof-dependency poset for the noncommutative Yang–Mills–Higgs owners

The nodes distinguish proved identities from the hypotheses/helpers on which
those proofs depend. The selected edges are grounded in the declarations in
`lean/InfoGeometry/Algebra/NoncommutativeYangMillsHiggsSpectralAction.lean`
and `lean/InfoGeometry/Algebra/TwoSheetDiracMassEntropy.lean`:

* the star-ring structure supports the adjoint-based trace identities and
  square completion; the four-channel trace identity and covariant Zorn square
  feed the quartic trace identity;
* flat Bogomolny data
  and the associative Jacobi identity support the harmonicity conclusion;
* the non-central tower conclusion depends on its initial grading and
  chirality-evenness hypotheses.

This is a finite proof-dependency poset, not a physical-causality claim or an
automatically extracted declaration graph. In particular, the quartic action,
square completion, harmonicity, and non-central tower are not forced into a
linear order.
-/

namespace InfoGeometry.Synthesis.NoncommutativeYangMillsHiggsCausalPoset

/-- Propositions and explicit hypotheses occurring in the finite-stage SA
proof contracts. -/
inductive Stage where
  | fourChannelTrace
  | flatReference
  | covariantZornSquare
  | quarticTraceAction
  | starRingStructure
  | squareCompletion
  | flatBogomolnyData
  | associativeJacobi
  | bianchiLaplaceHarmonicity
  | noncentralTowerHypotheses
  | noncentralTower
  deriving DecidableEq, Repr

/-- A rank separating inputs from the conclusions they support. -/
def rank : Stage → ℕ
  | .fourChannelTrace => 1
  | .flatReference => 0
  | .covariantZornSquare => 1
  | .quarticTraceAction => 2
  | .starRingStructure => 0
  | .squareCompletion => 1
  | .flatBogomolnyData => 0
  | .associativeJacobi => 0
  | .bianchiLaplaceHarmonicity => 1
  | .noncentralTowerHypotheses => 1
  | .noncentralTower => 2

/-- Direct proof-dependency edges, not a total-order ranking. -/
inductive directDependency : Stage → Stage → Prop where
  | flatnessToZornSquare :
      directDependency .flatReference .covariantZornSquare
  | starToFourChannel :
      directDependency .starRingStructure .fourChannelTrace
  | starToQuartic :
      directDependency .starRingStructure .quarticTraceAction
  | fourChannelToQuartic :
      directDependency .fourChannelTrace .quarticTraceAction
  | zornSquareToQuartic :
      directDependency .covariantZornSquare .quarticTraceAction
  | starToSquareCompletion :
      directDependency .starRingStructure .squareCompletion
  | bogomolnyDataToHarmonicity :
      directDependency .flatBogomolnyData .bianchiLaplaceHarmonicity
  | jacobiToHarmonicity :
      directDependency .associativeJacobi .bianchiLaplaceHarmonicity
  | towerHypothesesToTower :
      directDependency .noncentralTowerHypotheses .noncentralTower

theorem directDependency_increases_rank {a b : Stage}
    (h : directDependency a b) : rank a < rank b := by
  cases h <;> simp [rank]

theorem transGen_directDependency_increases_rank {a b : Stage}
    (h : Relation.TransGen directDependency a b) : rank a < rank b := by
  induction h with
  | single hab => exact directDependency_increases_rank hab
  | tail _ hbc ih =>
      exact Nat.lt_trans ih (directDependency_increases_rank hbc)

/-- Reachability, with equality included, is the causal partial order. -/
def causalLE (a b : Stage) : Prop :=
  a = b ∨ Relation.TransGen directDependency a b

instance instPartialOrder : PartialOrder Stage where
  le := causalLE
  le_refl := by
    intro a
    exact Or.inl rfl
  le_trans := by
    intro a b c hab hbc
    rcases hab with hab | hab
    · subst b
      exact hbc
    · rcases hbc with hbc | hbc
      · subst c
        exact Or.inr hab
      · exact Or.inr (Relation.TransGen.trans hab hbc)
  le_antisymm := by
    intro a b hab hba
    rcases hab with hab | hab
    · exact hab
    · rcases hba with hba | hba
      · exact hba.symm
      · have hlt := transGen_directDependency_increases_rank hab
        have hgt := transGen_directDependency_increases_rank hba
        omega

theorem direct_edges :
    directDependency .flatReference .covariantZornSquare ∧
    directDependency .starRingStructure .fourChannelTrace ∧
    directDependency .starRingStructure .quarticTraceAction ∧
    directDependency .fourChannelTrace .quarticTraceAction ∧
    directDependency .covariantZornSquare .quarticTraceAction ∧
    directDependency .starRingStructure .squareCompletion ∧
    directDependency .flatBogomolnyData .bianchiLaplaceHarmonicity ∧
    directDependency .associativeJacobi .bianchiLaplaceHarmonicity ∧
    directDependency .noncentralTowerHypotheses .noncentralTower := by
  exact ⟨.flatnessToZornSquare, .starToFourChannel, .starToQuartic,
    .fourChannelToQuartic,
    .zornSquareToQuartic, .starToSquareCompletion,
    .bogomolnyDataToHarmonicity, .jacobiToHarmonicity,
    .towerHypothesesToTower⟩

/-- SA₂ and SA₄ are incomparable: neither theorem is a prerequisite of the
other in the inspected owner proofs. -/
theorem quarticAction_and_noncentralTower_incomparable :
    ¬ (Stage.quarticTraceAction ≤ Stage.noncentralTower) ∧
    ¬ (Stage.noncentralTower ≤ Stage.quarticTraceAction) := by
  constructor
  · intro h
    rcases h with heq | hpath
    · cases heq
    · have hr := transGen_directDependency_increases_rank hpath
      norm_num [rank] at hr
  · intro h
    rcases h with heq | hpath
    · cases heq
    · have hr := transGen_directDependency_increases_rank hpath
      norm_num [rank] at hr

end InfoGeometry.Synthesis.NoncommutativeYangMillsHiggsCausalPoset
