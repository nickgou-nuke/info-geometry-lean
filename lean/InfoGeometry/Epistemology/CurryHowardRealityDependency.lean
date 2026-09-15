import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.DeriveFintype

namespace InfoGeometry.Epistemology.CurryHowardRealityDependency

inductive Archetype
  | positiveCoupling
  | quadraticResponse
  | squareCompletion
  | optimalityCertificate
  | normalizationEquality
  | relaxationContraction
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | positiveCoupling => {positiveCoupling}
  | quadraticResponse => {positiveCoupling, quadraticResponse}
  | squareCompletion => {positiveCoupling, quadraticResponse, squareCompletion}
  | optimalityCertificate =>
      {positiveCoupling, quadraticResponse, squareCompletion, optimalityCertificate}
  | normalizationEquality =>
      {positiveCoupling, quadraticResponse, squareCompletion, optimalityCertificate,
        normalizationEquality}
  | relaxationContraction =>
      {positiveCoupling, quadraticResponse, squareCompletion, optimalityCertificate,
        relaxationContraction}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem optimization_order :
    positiveCoupling ≤ quadraticResponse ∧ quadraticResponse ≤ squareCompletion ∧
      squareCompletion ≤ optimalityCertificate := by
  change prerequisites positiveCoupling ⊆ prerequisites quadraticResponse ∧
    prerequisites quadraticResponse ⊆ prerequisites squareCompletion ∧
    prerequisites squareCompletion ⊆ prerequisites optimalityCertificate
  decide

theorem certificate_branches :
    optimalityCertificate ≤ normalizationEquality ∧
      optimalityCertificate ≤ relaxationContraction := by
  change prerequisites optimalityCertificate ⊆ prerequisites normalizationEquality ∧
    prerequisites optimalityCertificate ⊆ prerequisites relaxationContraction
  decide

theorem normalization_and_dynamics_incomparable :
    ¬ normalizationEquality ≤ relaxationContraction ∧
      ¬ relaxationContraction ≤ normalizationEquality := by
  change ¬ prerequisites normalizationEquality ⊆ prerequisites relaxationContraction ∧
    ¬ prerequisites relaxationContraction ⊆ prerequisites normalizationEquality
  decide

end InfoGeometry.Epistemology.CurryHowardRealityDependency
