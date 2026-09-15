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
  deriving DecidableEq, Fintype

open Archetype

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
