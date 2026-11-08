/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Order
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.ScalarStatisticalIdentities

inductive Archetype
  | exponentialModel
  | probabilityCoordinate
  | oddsCoordinate
  | informationScaling
  | reciprocalVariance
  | equalMoments
  | relativeFluctuation
  | standardization
  | scalingIdentity
  deriving DecidableEq

instance : Fintype Archetype :=
  Fintype.ofList
    [.exponentialModel, .probabilityCoordinate, .oddsCoordinate,
      .informationScaling, .reciprocalVariance, .equalMoments,
      .relativeFluctuation, .standardization, .scalingIdentity]
    (by intro x; cases x <;> simp)

def prerequisites : Archetype → Finset ℕ
  | .exponentialModel => {0}
  | .probabilityCoordinate => {1}
  | .oddsCoordinate => {1, 2}
  | .informationScaling => {3}
  | .reciprocalVariance => {3, 4}
  | .equalMoments => {5}
  | .relativeFluctuation => {5, 6}
  | .standardization => {7}
  | .scalingIdentity => {7, 8}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

theorem dependency_branches :
    Archetype.probabilityCoordinate ≤ Archetype.oddsCoordinate ∧
      Archetype.informationScaling ≤ Archetype.reciprocalVariance ∧
      Archetype.equalMoments ≤ Archetype.relativeFluctuation ∧
      Archetype.standardization ≤ Archetype.scalingIdentity := by decide

theorem exponential_and_statistical_branches_incomparable :
    ¬ Archetype.exponentialModel ≤ Archetype.scalingIdentity ∧
      ¬ Archetype.scalingIdentity ≤ Archetype.exponentialModel := by decide

theorem equal_moments_and_standardization_incomparable :
    ¬ Archetype.equalMoments ≤ Archetype.standardization ∧
      ¬ Archetype.standardization ≤ Archetype.equalMoments := by decide

theorem no_dependency_cycle (left right : Archetype)
    (forward : left ≤ right) (backward : right ≤ left) : left = right :=
  le_antisymm forward backward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetypes 1–5 (`exponentialModel`, `probabilityCoordinate`, `oddsCoordinate`, `informationScaling`, `reciprocalVariance`):**
Non-commutative operator lift of projector probability coordinates `(P, 1 - P)`, log-odds
grading `S_P = P - (1 - P)`, and Fisher–Bures variance `V = {N_+, N_-}` over `[Ring B]`. -/
theorem archetype_operator_probability_odds_and_variance
    {P : B} (hP : P * P = P) (A C : B) :
    P + (1 - P) = 1 ∧
    P - (1 - P) = invS P ∧
    invS P * invS P = 1 ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C := by
  refine ⟨by abel, rfl, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetypes 6–9 (`equalMoments`, `relativeFluctuation`, `standardization`, `scalingIdentity`):**
Non-commutative operator moment and fluctuation identities:
`Φ² + J² = 0` (opposite second moments), `[Φ, J] = -2 • Σ` (relative fluctuation commutator),
`Σ² = V²` (standardized square equality), and `derivSqPhi P A C J = -4 • (V * J)` (scaling). -/
theorem archetype_operator_moments_fluctuation_and_scaling
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C ∧
    derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · simp only [derivSqPhi]; peirce_nf hP

/-- **Master Synthesis (`scalar_statistical_identities_operator_master_synthesis`):**
Unites the 9-stage partial-order branch theorems with the non-commutative `[Ring B]`
operator probability, log-odds, and fluctuation identities. -/
theorem scalar_statistical_identities_operator_master_synthesis
    {P : B} (hP : P * P = P) (A C : B) :
    (Archetype.probabilityCoordinate ≤ Archetype.oddsCoordinate ∧
      Archetype.informationScaling ≤ Archetype.reciprocalVariance ∧
      Archetype.equalMoments ≤ Archetype.relativeFluctuation ∧
      Archetype.standardization ≤ Archetype.scalingIdentity) ∧
    (invS P * invS P = 1 ∧ genPhi P A C * genPhi P A C = genV P A C) ∧
    (genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 ∧
      genSig P A C * genSig P A C = genV P A C * genV P A C) := by
  have h1 := archetype_operator_probability_odds_and_variance hP A C
  have h2 := archetype_operator_moments_fluctuation_and_scaling hP A C
  exact ⟨dependency_branches, ⟨h1.2.2.1, h1.2.2.2.1⟩, ⟨h2.1, h2.2.2.1⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.ScalarStatisticalIdentities
