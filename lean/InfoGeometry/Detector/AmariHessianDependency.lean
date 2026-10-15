import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

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

end InfoGeometry.Detector.AmariHessianDuality.ProofDependency
