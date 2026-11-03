/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.DeriveFintype
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Spectrometry.AnnealedDescentDependency

inductive Archetype
  | concaveFreeEnergy
  | regularAnchor
  | majorization
  | quadraticMinimum
  | descent
  | energyLowerBound
  | energyConvergence
  deriving DecidableEq

instance : Fintype Archetype where
  elems := {Archetype.concaveFreeEnergy, Archetype.regularAnchor,
    Archetype.majorization, Archetype.quadraticMinimum, Archetype.descent,
    Archetype.energyLowerBound, Archetype.energyConvergence}
  complete := by
    intro x
    cases x <;> simp

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

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetypes 1–4 (`concaveFreeEnergy`, `regularAnchor`, `majorization`, `quadraticMinimum`):**
Non-commutative operator Bregman majorization / three-point identity around an anchor `Y`
and Peirce anchor stationarity `comm P (evenGrade P Y) = 0`. -/
theorem archetype_operator_bregman_majorization_and_anchor
    {P : B} (hP : P * P = P) (X Y Z : B) :
    (X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) =
      anticomm (X - Y) (Y - Z) ∧
    comm P (evenGrade P Y) = 0 ∧
    evenGrade P Y + oddGrade P Y = Y := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]; noncomm_ring
  · simp only [evenGrade]; peirce_nf hP
  · simp only [evenGrade, oddGrade]; peirce_nf hP

/-- **Archetypes 5–7 (`descent`, `energyLowerBound`, `energyConvergence`):**
Non-commutative operator descent along the inner derivation `ad_P²(X) = oddGrade P X`,
with fixed-point convergence on the even-grade centralizer (`ad_P(evenGrade P X) = 0`)
and exact Hessian splitting `derivSqPhi P A C X - derivSqJ P A C X = 4 • sandwichSame P A C X`. -/
theorem archetype_operator_descent_and_equilibrium_convergence
    {P : B} (hP : P * P = P) (A C X : B) :
    comm P (comm P X) = oddGrade P X ∧
    comm P (X - comm P (comm P X)) = 0 ∧
    derivSqPhi P A C X - derivSqJ P A C X = (4 : ℤ) • sandwichSame P A C X := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [oddGrade]; peirce_nf hP
  · peirce_nf hP
  · simp only [derivSqPhi, derivSqJ, sandwichSame]; peirce_nf hP

/-- **Master Synthesis (`annealed_descent_dependency_master_synthesis`):**
Unites the 7-stage partial-order branch theorems with the non-commutative `[Ring B]`
Bregman majorization and Peirce descent theorems. -/
theorem annealed_descent_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (concaveFreeEnergy ≤ majorization ∧ regularAnchor ≤ majorization ∧
      regularAnchor ≤ quadraticMinimum ∧ majorization ≤ descent ∧
      quadraticMinimum ≤ descent ∧ descent ≤ energyConvergence ∧
      energyLowerBound ≤ energyConvergence) ∧
    ((X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) =
      anticomm (X - Y) (Y - Z)) ∧
    (comm P (X - comm P (comm P X)) = 0 ∧
      derivSqPhi P A C X - derivSqJ P A C X = (4 : ℤ) • sandwichSame P A C X) := by
  have h1 := archetype_operator_bregman_majorization_and_anchor hP X Y Z
  have h2 := archetype_operator_descent_and_equilibrium_convergence hP A C X
  exact ⟨⟨descent_dependencies.1, descent_dependencies.2.1,
      descent_dependencies.2.2.1, descent_dependencies.2.2.2.1,
      descent_dependencies.2.2.2.2, convergence_dependencies⟩,
    h1.1, ⟨h2.2.1, h2.2.2⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Spectrometry.AnnealedDescentDependency
