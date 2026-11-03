/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.DeriveFintype
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Epistemology.CurryHowardRealityDependency

inductive Archetype
  | positiveCoupling
  | quadraticResponse
  | squareCompletion
  | optimalityCertificate
  | normalizationEquality
  | relaxationContraction
  deriving DecidableEq

open Archetype

instance : Fintype Archetype where
  elems := {positiveCoupling, quadraticResponse, squareCompletion, optimalityCertificate, normalizationEquality, relaxationContraction}
  complete := by rintro (_ | _ | _ | _ | _ | _) <;> simp

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

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetypes 1–3 (`positiveCoupling`, `quadraticResponse`, `squareCompletion`):**
Non-commutative square completion and quadratic Bregman three-point identity over `[Ring B]`:
`(X - Y) * (X - Y) = X * X + Y * Y - anticomm X Y` and
`(X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) = anticomm (X - Y) (Y - Z)`. -/
theorem archetype_noncommutative_square_completion (X Y Z : B) :
    (X - Y) * (X - Y) = X * X + Y * Y - anticomm X Y ∧
    (X - Z) * (X - Z) - (X - Y) * (X - Y) - (Y - Z) * (Y - Z) =
      anticomm (X - Y) (Y - Z) := by
  refine ⟨?_, ?_⟩ <;>
    (dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]; noncomm_ring)

/-- **Archetypes 4–6 (`optimalityCertificate`, `normalizationEquality`, `relaxationContraction`):**
Peirce stationary certificate `comm P (evenGrade P X) = 0`, normalization partition
`evenGrade P X + oddGrade P X = X`, and dissipative double-commutator contraction
`comm P (comm P X) = oddGrade P X`. -/
theorem archetype_optimality_normalization_and_relaxation
    {P : B} (hP : P * P = P) (A C X : B) :
    comm P (evenGrade P X) = 0 ∧
    evenGrade P X + oddGrade P X = X ∧
    comm P (comm P X) = oddGrade P X ∧
    derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [evenGrade]; peirce_nf hP
  · simp only [evenGrade, oddGrade]; peirce_nf hP
  · simp only [oddGrade]; peirce_nf hP
  · simp only [derivSqPhi]; peirce_nf hP

/-- **Master Synthesis (`curry_howard_reality_dependency_master_synthesis`):**
Unites the 6-stage partial-order branch theorems with the non-commutative `[Ring B]`
square-completion and Peirce relaxation theorems. -/
theorem curry_howard_reality_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (positiveCoupling ≤ quadraticResponse ∧ quadraticResponse ≤ squareCompletion ∧
      squareCompletion ≤ optimalityCertificate ∧
      optimalityCertificate ≤ normalizationEquality ∧
      optimalityCertificate ≤ relaxationContraction) ∧
    ((X - Y) * (X - Y) = X * X + Y * Y - anticomm X Y) ∧
    (comm P (evenGrade P X) = 0 ∧ evenGrade P X + oddGrade P X = X ∧
      comm P (comm P X) = oddGrade P X) := by
  have h1 := archetype_noncommutative_square_completion X Y Z
  have h2 := archetype_optimality_normalization_and_relaxation hP A C X
  exact ⟨⟨optimization_order.1, optimization_order.2.1, optimization_order.2.2,
      certificate_branches⟩,
    h1.1, ⟨h2.1, h2.2.1, h2.2.2.1⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Epistemology.CurryHowardRealityDependency
