/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Epistemology.CrystallizedGrammar
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Epistemology.CrystallizedGrammar.ProofDependency

inductive Archetype
  | hullGeneration
  | extremePoint
  | endpointSaturation
  | maximizerSet
  | linearSaturation
  | uniqueMaximum
  | generatorMembership
  | convexBound
  | finiteMaximum
  deriving DecidableEq

open Archetype

instance : Fintype Archetype where
  elems := [hullGeneration, extremePoint, endpointSaturation, maximizerSet, linearSaturation, uniqueMaximum, generatorMembership, convexBound, finiteMaximum].toFinset
  complete := by
    intro x
    cases x <;> simp

def prerequisites : Archetype → Finset Archetype
  | hullGeneration => {hullGeneration}
  | extremePoint => {extremePoint}
  | endpointSaturation => {endpointSaturation}
  | maximizerSet => {extremePoint, endpointSaturation, maximizerSet}
  | linearSaturation => {endpointSaturation, linearSaturation}
  | uniqueMaximum => {extremePoint, endpointSaturation, uniqueMaximum}
  | generatorMembership =>
      {hullGeneration, extremePoint, endpointSaturation, uniqueMaximum, generatorMembership}
  | convexBound => {hullGeneration, convexBound}
  | finiteMaximum => {hullGeneration, convexBound, finiteMaximum}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem causal_branches :
    extremePoint < uniqueMaximum ∧ uniqueMaximum < generatorMembership ∧
    hullGeneration < generatorMembership ∧ hullGeneration < convexBound ∧
    convexBound < finiteMaximum := by
  simp only [lt_iff_le_not_ge]
  decide

theorem uniqueness_and_finiteness_incomparable :
    ¬ uniqueMaximum ≤ finiteMaximum ∧ ¬ finiteMaximum ≤ uniqueMaximum := by
  decide

theorem saturation_branches :
    endpointSaturation < uniqueMaximum ∧ endpointSaturation < maximizerSet ∧
    extremePoint < maximizerSet ∧ endpointSaturation < linearSaturation ∧
    ¬ maximizerSet ≤ uniqueMaximum ∧ ¬ uniqueMaximum ≤ maximizerSet := by
  simp only [lt_iff_le_not_ge]
  decide

theorem no_cycle {earlier later : Archetype} (forward : earlier < later) :
    ¬ later < earlier := lt_asymm forward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetypes 1–3 (`hullGeneration`, `extremePoint`, `endpointSaturation`):**
Idempotent extreme projectors `P` and `1 - P` generate the identity resolution `P + (1 - P) = 1`
and saturate at the boundary (`P * P = P`, `(1 - P) * (1 - P) = 1 - P`, `P * (1 - P) = 0`). -/
theorem archetype_extreme_projectors_and_endpoint_saturation
    {P : B} (hP : P * P = P) :
    P + (1 - P) = 1 ∧
    P * P = P ∧
    (1 - P) * (1 - P) = 1 - P ∧
    P * (1 - P) = 0 ∧
    (1 - P) * P = 0 := by
  refine ⟨by abel, hP, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetypes 4–6 (`maximizerSet`, `linearSaturation`, `uniqueMaximum`):**
Eigen-subspace saturation for the grading involution `S_P = P - (1 - P)`:
`S_P * P = P` (eigenvalue `+1`), `S_P * (1 - P) = -(1 - P)` (eigenvalue `-1`), and
unique decomposition `X = evenGrade P X + oddGrade P X`. -/
theorem archetype_grading_eigenspace_saturation_and_unique_split
    {P : B} (hP : P * P = P) (X : B) :
    invS P * P = P ∧
    invS P * (1 - P) = -(1 - P) ∧
    evenGrade P X + oddGrade P X = X ∧
    invS P * evenGrade P X * invS P = evenGrade P X ∧
    invS P * oddGrade P X * invS P = -oddGrade P X := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · simp only [evenGrade, oddGrade]; peirce_nf hP
  · simp only [evenGrade]; peirce_nf hP
  · simp only [oddGrade]; peirce_nf hP

/-- **Archetypes 7–9 (`generatorMembership`, `convexBound`, `finiteMaximum`):**
Finite-rank Klein–Hadamard projector partition on the inner-derivation algebra:
`projV P A C X + projPhi P A C X + projJ P A C X + projSig P A C X = 8 • X` and
cubic generator saturation `Φ³ = V * Φ`, `J³ = -(V * J)`. -/
theorem archetype_klein_hadamard_partition_and_cubic_saturation
    {P : B} (hP : P * P = P) (A C X : B) :
    projV P A C X + projPhi P A C X + projJ P A C X + projSig P A C X = (8 : ℤ) • X ∧
    genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C ∧
    genJ P A C * genJ P A C * genJ P A C = -(genV P A C * genJ P A C) := by
  refine ⟨(archetype_A5_klein_hadamard_spectra_and_partition hP A C X).1, ?_, ?_⟩ <;>
    peirce_nf hP

/-- **Master Synthesis (`crystallized_grammar_dependency_master_synthesis`):**
Unites the 9-stage partial-order branch theorems with the non-commutative `[Ring B]`
extreme-projector and Klein–Hadamard partition theorems. -/
theorem crystallized_grammar_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X : B) :
    (extremePoint < uniqueMaximum ∧ uniqueMaximum < generatorMembership ∧
      hullGeneration < generatorMembership ∧ hullGeneration < convexBound ∧
      convexBound < finiteMaximum) ∧
    (P + (1 - P) = 1 ∧ P * (1 - P) = 0) ∧
    (evenGrade P X + oddGrade P X = X) ∧
    (projV P A C X + projPhi P A C X + projJ P A C X + projSig P A C X = (8 : ℤ) • X) := by
  have h1 := archetype_extreme_projectors_and_endpoint_saturation hP
  have h2 := archetype_grading_eigenspace_saturation_and_unique_split hP X
  have h3 := archetype_klein_hadamard_partition_and_cubic_saturation hP A C X
  exact ⟨causal_branches, ⟨h1.1, h1.2.2.2.1⟩, h2.2.2.1, h3.1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Epistemology.CrystallizedGrammar.ProofDependency
