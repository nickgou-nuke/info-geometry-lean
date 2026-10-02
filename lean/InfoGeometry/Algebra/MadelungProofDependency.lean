import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic

namespace InfoGeometry.Algebra.MadelungProofDependency

inductive Archetype
  | logDensity
  | osmoticScore
  | curvatureIdentity
  | commutingDerivations
  | hamiltonJacobi
  | eulerEquation
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | logDensity => {logDensity}
  | osmoticScore => {logDensity, osmoticScore}
  | curvatureIdentity => {logDensity, osmoticScore, curvatureIdentity}
  | commutingDerivations => {commutingDerivations}
  | hamiltonJacobi => {logDensity, osmoticScore, curvatureIdentity, hamiltonJacobi}
  | eulerEquation =>
      {logDensity, osmoticScore, curvatureIdentity, commutingDerivations,
        hamiltonJacobi, eulerEquation}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem curvature_branch :
    logDensity ≤ osmoticScore ∧ osmoticScore ≤ curvatureIdentity := by
  change prerequisites logDensity ⊆ prerequisites osmoticScore ∧
    prerequisites osmoticScore ⊆ prerequisites curvatureIdentity
  decide

theorem euler_prerequisites :
    curvatureIdentity ≤ hamiltonJacobi ∧ hamiltonJacobi ≤ eulerEquation ∧
      commutingDerivations ≤ eulerEquation := by
  change prerequisites curvatureIdentity ⊆ prerequisites hamiltonJacobi ∧
    prerequisites hamiltonJacobi ⊆ prerequisites eulerEquation ∧
    prerequisites commutingDerivations ⊆ prerequisites eulerEquation
  decide

theorem commutation_not_implied_by_curvature :
    ¬ commutingDerivations ≤ curvatureIdentity ∧
      ¬ curvatureIdentity ≤ commutingDerivations := by
  change ¬ prerequisites commutingDerivations ⊆ prerequisites curvatureIdentity ∧
    ¬ prerequisites curvatureIdentity ⊆ prerequisites commutingDerivations
  decide

end InfoGeometry.Algebra.MadelungProofDependency
