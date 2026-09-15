import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.DeriveFintype

namespace InfoGeometry.Physics.CobaltAsymmetryDependency

inductive Archetype
  | betaModel
  | betaReflectionViolation
  | evenAngularModel
  | gammaAnisotropy
  | gammaReflectionInvariance
  | anisotropyCounterexample
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | betaModel => {betaModel}
  | betaReflectionViolation => {betaModel, betaReflectionViolation}
  | evenAngularModel => {evenAngularModel}
  | gammaAnisotropy => {evenAngularModel, gammaAnisotropy}
  | gammaReflectionInvariance => {evenAngularModel, gammaReflectionInvariance}
  | anisotropyCounterexample =>
      {evenAngularModel, gammaAnisotropy, gammaReflectionInvariance, anisotropyCounterexample}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem model_dependencies :
    betaModel ≤ betaReflectionViolation ∧ evenAngularModel ≤ gammaAnisotropy ∧
      evenAngularModel ≤ gammaReflectionInvariance ∧
      gammaAnisotropy ≤ anisotropyCounterexample ∧
      gammaReflectionInvariance ≤ anisotropyCounterexample := by
  change prerequisites betaModel ⊆ prerequisites betaReflectionViolation ∧
    prerequisites evenAngularModel ⊆ prerequisites gammaAnisotropy ∧
    prerequisites evenAngularModel ⊆ prerequisites gammaReflectionInvariance ∧
    prerequisites gammaAnisotropy ⊆ prerequisites anisotropyCounterexample ∧
    prerequisites gammaReflectionInvariance ⊆ prerequisites anisotropyCounterexample
  decide

theorem beta_and_gamma_branches_incomparable :
    ¬ betaReflectionViolation ≤ anisotropyCounterexample ∧
      ¬ anisotropyCounterexample ≤ betaReflectionViolation := by
  change ¬ prerequisites betaReflectionViolation ⊆ prerequisites anisotropyCounterexample ∧
    ¬ prerequisites anisotropyCounterexample ⊆ prerequisites betaReflectionViolation
  decide

end InfoGeometry.Physics.CobaltAsymmetryDependency
