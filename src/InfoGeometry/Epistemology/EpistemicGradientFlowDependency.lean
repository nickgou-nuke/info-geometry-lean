/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Epistemology.EpistemicGradientFlow
import InfoGeometry.Epistemology.DiracRelativeEntropyBoundary
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-! This is a hand-authored finite prerequisite model for the listed
archetypes. The relation is inclusion between the declared prerequisite sets;
it is not computed from Lean imports or declaration dependencies. -/

namespace InfoGeometry.Epistemology.EpistemicGradientFlow.ProofDependency

inductive Archetype
  | logisticDerivative
  | fenchelNonnegativity
  | relaxation
  | quadraticBound
  | dissipation
  | decayBound
  | equilibriumLimit
  | diracObstruction
  deriving DecidableEq

open Archetype

def prerequisites : Archetype → Finset Archetype
  | logisticDerivative => {logisticDerivative}
  | fenchelNonnegativity => {fenchelNonnegativity}
  | relaxation => {logisticDerivative, relaxation}
  | quadraticBound => {logisticDerivative, fenchelNonnegativity, quadraticBound}
  | dissipation => {logisticDerivative, relaxation, dissipation}
  | decayBound =>
      {logisticDerivative, fenchelNonnegativity, relaxation, quadraticBound, decayBound}
  | equilibriumLimit => {logisticDerivative, relaxation, equilibriumLimit}
  | diracObstruction => {diracObstruction}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later h₁ h₂
    have hsets : prerequisites earlier = prerequisites later :=
      Finset.Subset.antisymm h₁ h₂
    cases earlier <;> cases later <;>
      simp_all [prerequisites, Finset.subset_iff]

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem analytic_branches :
    logisticDerivative < quadraticBound ∧ fenchelNonnegativity < quadraticBound ∧
      quadraticBound < decayBound ∧ relaxation < decayBound ∧
      relaxation < dissipation ∧ relaxation < equilibriumLimit := by
  simp only [lt_iff_le_not_ge]
  decide

theorem dissipation_and_rate_incomparable :
    ¬ dissipation ≤ decayBound ∧ ¬ decayBound ≤ dissipation := by
  decide

/-- In this declared prerequisite model, the standalone Dirac node is
incomparable with the equilibrium-limit node. This states nothing about the
repository's import graph. -/
theorem dirac_obstruction_is_separate :
    ¬ diracObstruction ≤ equilibriumLimit ∧ ¬ equilibriumLimit ≤ diracObstruction := by
  decide

theorem no_cycle {earlier later : Archetype} (forward : earlier < later) :
    ¬ later < earlier := lt_asymm forward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetypes 1–4 (`logisticDerivative`, `fenchelNonnegativity`, `relaxation`, `quadraticBound`):**
Idempotent logistic variance identity `P - P * P = 0`, non-commutative Fenchel–Bregman
three-point identity, and inner-derivation relaxation `comm P (comm P X) = oddGrade P X`. -/
theorem archetype_logistic_fenchel_and_relaxation_identities
    {P : B} (hP : P * P = P) (X Y Z : B) :
    P * (1 - P) = 0 ∧
    (X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) =
      anticomm (X - Y) (Y - Z) ∧
    comm P (comm P X) = oddGrade P X := by
  refine ⟨?_, ?_, ?_⟩
  · peirce_nf hP
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]; noncomm_ring
  · simp only [oddGrade]; peirce_nf hP

/-- **Archetypes 5–8 (`dissipation`, `decayBound`, `equilibriumLimit`, `diracObstruction`):**
Dissipative double-commutator spectrum (`derivSqPhi P A C J = -4 • (V * J)`), equilibrium
centralizer (`comm P (evenGrade P X) = 0`), and Dirac chiral anticommutator obstruction
(`anticomm (invS P) Φ = 0`, `comm Φ J = -2 • Σ`). -/
theorem archetype_dissipation_equilibrium_and_dirac_obstruction
    {P : B} (hP : P * P = P) (A C X : B) :
    derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    comm P (evenGrade P X) = 0 ∧
    anticomm (invS P) (genPhi P A C) = 0 ∧
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [derivSqPhi]; peirce_nf hP
  · simp only [evenGrade]; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- **Master Synthesis (`epistemic_gradient_flow_dependency_master_synthesis`):**
Unites the 8-stage partial-order branch theorems with the non-commutative `[Ring B]`
Fenchel–Bregman, dissipation, and Dirac obstruction theorems. -/
theorem epistemic_gradient_flow_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (logisticDerivative < quadraticBound ∧ fenchelNonnegativity < quadraticBound ∧
      quadraticBound < decayBound ∧ relaxation < decayBound ∧
      relaxation < dissipation ∧ relaxation < equilibriumLimit) ∧
    ((X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) =
      anticomm (X - Y) (Y - Z)) ∧
    (derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
      comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C)) := by
  have h1 := archetype_logistic_fenchel_and_relaxation_identities hP X Y Z
  have h2 := archetype_dissipation_equilibrium_and_dirac_obstruction hP A C X
  exact ⟨analytic_branches, h1.2.1, ⟨h2.1, h2.2.2.2⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Epistemology.EpistemicGradientFlow.ProofDependency
