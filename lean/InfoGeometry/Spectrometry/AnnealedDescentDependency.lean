import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.DeriveFintype

namespace InfoGeometry.Spectrometry.AnnealedDescentDependency

inductive Archetype
  | concaveFreeEnergy
  | regularAnchor
  | majorization
  | quadraticMinimum
  | descent
  | energyLowerBound
  | energyConvergence
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | concaveFreeEnergy => {concaveFreeEnergy}
  | regularAnchor => {regularAnchor}
  | majorization => {concaveFreeEnergy, regularAnchor, majorization}
  | quadraticMinimum => {regularAnchor, quadraticMinimum}
  | descent => {concaveFreeEnergy, regularAnchor, majorization, quadraticMinimum, descent}
  | energyLowerBound => {energyLowerBound}
  | energyConvergence =>
      {concaveFreeEnergy, regularAnchor, majorization, quadraticMinimum, descent,
        energyLowerBound, energyConvergence}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem descent_dependencies :
    concaveFreeEnergy ≤ majorization ∧ regularAnchor ≤ majorization ∧
      regularAnchor ≤ quadraticMinimum ∧ majorization ≤ descent ∧
      quadraticMinimum ≤ descent := by
  change prerequisites concaveFreeEnergy ⊆ prerequisites majorization ∧
    prerequisites regularAnchor ⊆ prerequisites majorization ∧
    prerequisites regularAnchor ⊆ prerequisites quadraticMinimum ∧
    prerequisites majorization ⊆ prerequisites descent ∧
    prerequisites quadraticMinimum ⊆ prerequisites descent
  decide

theorem convergence_dependencies :
    descent ≤ energyConvergence ∧ energyLowerBound ≤ energyConvergence := by
  change prerequisites descent ⊆ prerequisites energyConvergence ∧
    prerequisites energyLowerBound ⊆ prerequisites energyConvergence
  decide

theorem majorization_and_minimization_incomparable :
    ¬ majorization ≤ quadraticMinimum ∧ ¬ quadraticMinimum ≤ majorization := by
  change ¬ prerequisites majorization ⊆ prerequisites quadraticMinimum ∧
    ¬ prerequisites quadraticMinimum ⊆ prerequisites majorization
  decide

end InfoGeometry.Spectrometry.AnnealedDescentDependency
