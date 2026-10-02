import Mathlib.Data.Finset.Order
import Mathlib.Tactic

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
  deriving DecidableEq, Fintype

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

end InfoGeometry.ScalarStatisticalIdentities
