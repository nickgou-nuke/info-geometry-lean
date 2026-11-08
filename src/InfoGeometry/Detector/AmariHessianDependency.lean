/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Detector.AmariHessianDuality.ProofDependency

inductive Archetype
  | oddsCoordinate
  | logPartition
  | expectationDerivative
  | fisherHessian
  | legendreConjugate
  | singlesResponse
  | singlesMetricIdentity
  | efficiencyPullback
  | varianceBound
  deriving DecidableEq

open Archetype

def archetypeFinEquiv : Archetype ≃ Fin 9 where
  toFun
    | oddsCoordinate => 0
    | logPartition => 1
    | expectationDerivative => 2
    | fisherHessian => 3
    | legendreConjugate => 4
    | singlesResponse => 5
    | singlesMetricIdentity => 6
    | efficiencyPullback => 7
    | varianceBound => 8
  invFun i := match i.val with
    | 0 => oddsCoordinate
    | 1 => logPartition
    | 2 => expectationDerivative
    | 3 => fisherHessian
    | 4 => legendreConjugate
    | 5 => singlesResponse
    | 6 => singlesMetricIdentity
    | 7 => efficiencyPullback
    | _ => varianceBound
  left_inv x := by cases x <;> rfl
  right_inv i := by
    apply Fin.ext
    fin_cases i <;> rfl

instance : Fintype Archetype := Fintype.ofEquiv (Fin 9) archetypeFinEquiv.symm

def prerequisites : Archetype → Finset Archetype
  | oddsCoordinate => {oddsCoordinate}
  | logPartition => {logPartition}
  | expectationDerivative => {logPartition, expectationDerivative}
  | fisherHessian => {logPartition, expectationDerivative, fisherHessian}
  | legendreConjugate => {oddsCoordinate, logPartition, legendreConjugate}
  | singlesResponse => {singlesResponse}
  | singlesMetricIdentity =>
      {oddsCoordinate, logPartition, expectationDerivative, fisherHessian,
        singlesResponse, singlesMetricIdentity}
  | efficiencyPullback =>
      {oddsCoordinate, logPartition, expectationDerivative, fisherHessian, efficiencyPullback}
  | varianceBound => {varianceBound}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem hessian_branch :
    logPartition < expectationDerivative ∧ expectationDerivative < fisherHessian ∧
    fisherHessian < singlesMetricIdentity ∧ singlesResponse < singlesMetricIdentity := by
  simp only [lt_iff_le_not_ge]
  decide

theorem legendre_branch : oddsCoordinate < legendreConjugate ∧ logPartition < legendreConjugate := by
  simp only [lt_iff_le_not_ge]
  decide

theorem coordinate_readouts_incomparable :
    ¬ singlesMetricIdentity ≤ efficiencyPullback ∧
    ¬ efficiencyPullback ≤ singlesMetricIdentity := by
  decide

theorem no_cycle {earlier later : Archetype} (forward : earlier < later) :
    ¬ later < earlier := lt_asymm forward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetypes 1–4 (`oddsCoordinate`, `logPartition`, `expectationDerivative`, `fisherHessian`):**
Non-commutative Peirce–Amari log-partition generator `Σ = [N_+, N_-]`, expectation derivative
`[Σ, X]`, and Para-Kähler Fisher–Bures Hessian `-(derivSqPhi + derivSqJ)`:
`[N_+, [N_-, X]] - [N_-, [N_+, X]] = [Σ, X]` and
`2 • ([N_+, [N_-, X]] + [N_-, [N_+, X]]) = -(derivSqPhi P A C X + derivSqJ P A C X)`. -/
theorem archetype_logPartition_expectation_and_fisherHessian
    {P : B} (hP : P * P = P) (A C X : B) :
    genSig P A C = invS P * genV P A C ∧
    comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X) =
      comm (genSig P A C) X ∧
    (2 : ℤ) • (comm (conePlus P A) (comm (coneMinus P C) X) +
        comm (coneMinus P C) (comm (conePlus P A) X)) =
      -(derivSqPhi P A C X + derivSqJ P A C X) := by
  refine ⟨?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · simp only [derivSqPhi, derivSqJ]; peirce_nf hP

/-- **Archetype 5 (`legendreConjugate`):**
Non-commutative quadratic Legendre–Bregman three-point identity over `[Ring B]`:
`(X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) = anticomm (X - Y) (Y - Z)`. -/
theorem archetype_legendreConjugate_bregman_three_point (X Y Z : B) :
    (X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) =
      anticomm (X - Y) (Y - Z) := by
  dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]
  noncomm_ring

/-- **Archetypes 6–9 (`singlesResponse`, `singlesMetricIdentity`, `efficiencyPullback`, `varianceBound`):**
Singles response and variance identities on the off-diagonal tangent basis `(Φ, J)`:
`derivSqPhi P A C (genJ P A C) = -4 • (V * J)`,
`derivSqJ P A C (genPhi P A C) = -4 • (V * Φ)`, and
`derivSqPhi P A C X - derivSqJ P A C X = 4 • sandwichSame P A C X`. -/
theorem archetype_singles_response_metric_and_variance_identities
    {P : B} (hP : P * P = P) (A C X : B) :
    derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    derivSqJ P A C (genPhi P A C) = -((4 : ℤ) • (genV P A C * genPhi P A C)) ∧
    derivSqPhi P A C X - derivSqJ P A C X = (4 : ℤ) • sandwichSame P A C X := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [derivSqPhi, derivSqJ, sandwichSame]; peirce_nf hP)

/-- **Master Synthesis (`amari_hessian_dependency_master_synthesis`):**
Unites the 9-stage partial-order branch theorems with the non-commutative `[Ring B]`
Amari–Bregman–Peirce Hessian theorems. -/
theorem amari_hessian_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (logPartition < expectationDerivative ∧ expectationDerivative < fisherHessian ∧
      oddsCoordinate < legendreConjugate ∧ logPartition < legendreConjugate) ∧
    (comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X) =
      comm (genSig P A C) X) ∧
    ((X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) =
      anticomm (X - Y) (Y - Z)) ∧
    (derivSqPhi P A C X - derivSqJ P A C X = (4 : ℤ) • sandwichSame P A C X) := by
  have h1 := archetype_logPartition_expectation_and_fisherHessian hP A C X
  have h2 := archetype_legendreConjugate_bregman_three_point X Y Z
  have h3 := archetype_singles_response_metric_and_variance_identities hP A C X
  exact ⟨⟨hessian_branch.1, hessian_branch.2.1, legendre_branch⟩,
    h1.2.1, h2, h3.2.2⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Detector.AmariHessianDuality.ProofDependency
