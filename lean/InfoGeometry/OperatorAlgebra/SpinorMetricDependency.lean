import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic

namespace InfoGeometry.OperatorAlgebra.SpinorMetricDependency

inductive Archetype
  | matrixTower
  | faithfulTrace
  | isometricTransitions
  | dualTangentSpace
  | positiveDensity
  | sldInverse
  | traceMetric
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | matrixTower => {matrixTower}
  | faithfulTrace => {matrixTower, faithfulTrace}
  | isometricTransitions => {matrixTower, faithfulTrace, isometricTransitions}
  | dualTangentSpace => {dualTangentSpace}
  | positiveDensity => {positiveDensity}
  | sldInverse => {positiveDensity, sldInverse}
  | traceMetric => {positiveDensity, sldInverse, traceMetric}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem tower_order : matrixTower ≤ faithfulTrace ∧ faithfulTrace ≤ isometricTransitions := by
  change prerequisites matrixTower ⊆ prerequisites faithfulTrace ∧
    prerequisites faithfulTrace ⊆ prerequisites isometricTransitions
  decide

theorem metric_order : positiveDensity ≤ sldInverse ∧ sldInverse ≤ traceMetric := by
  change prerequisites positiveDensity ⊆ prerequisites sldInverse ∧
    prerequisites sldInverse ⊆ prerequisites traceMetric
  decide

theorem independent_branches : ¬ isometricTransitions ≤ traceMetric ∧
    ¬ traceMetric ≤ isometricTransitions ∧ ¬ dualTangentSpace ≤ traceMetric := by
  change ¬ prerequisites isometricTransitions ⊆ prerequisites traceMetric ∧
    ¬ prerequisites traceMetric ⊆ prerequisites isometricTransitions ∧
    ¬ prerequisites dualTangentSpace ⊆ prerequisites traceMetric
  decide

end InfoGeometry.OperatorAlgebra.SpinorMetricDependency
