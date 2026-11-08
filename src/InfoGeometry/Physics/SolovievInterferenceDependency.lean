/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.SolovievDressedInterference
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Physics.SolovievDressedInterference.ProofDependency

inductive Archetype
  | circularCoefficients
  | phononCAR
  | operatorSplit
  | complexStrength
  | cocyclicTransport
  | dressedInterference
  | phaseInvariantCommutator
  deriving DecidableEq

instance : Fintype Archetype where
  elems := {Archetype.circularCoefficients, Archetype.phononCAR,
    Archetype.operatorSplit, Archetype.complexStrength,
    Archetype.cocyclicTransport, Archetype.dressedInterference,
    Archetype.phaseInvariantCommutator}
  complete := by
    intro x
    cases x <;> simp

open Archetype

def prerequisites : Archetype → Finset Archetype
  | circularCoefficients => {circularCoefficients}
  | phononCAR => {phononCAR}
  | operatorSplit => {circularCoefficients, phononCAR, operatorSplit}
  | complexStrength => {complexStrength}
  | cocyclicTransport => {cocyclicTransport}
  | dressedInterference => {complexStrength, cocyclicTransport, dressedInterference}
  | phaseInvariantCommutator => {phononCAR, complexStrength, phaseInvariantCommutator}

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
    circularCoefficients < operatorSplit ∧ phononCAR < operatorSplit ∧
    complexStrength < dressedInterference ∧ cocyclicTransport < dressedInterference ∧
    phononCAR < phaseInvariantCommutator ∧ complexStrength < phaseInvariantCommutator := by
  simp only [lt_iff_le_not_ge]
  decide

theorem interference_and_commutator_incomparable :
    ¬ dressedInterference ≤ phaseInvariantCommutator ∧
    ¬ phaseInvariantCommutator ≤ dressedInterference := by
  decide

theorem no_cycle {earlier later : Archetype} (forward : earlier < later) :
    ¬ later < earlier := lt_asymm forward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`circularCoefficients`):**
Circularly polarized Peirce corner modes `N_+ = P A (1 - P)` and `N_- = (1 - P) C P`
are recovered from the linear modes `(Φ, J)` by `Φ + J = 2 • N_+` and `Φ - J = 2 • N_-`. -/
theorem archetype_circularCoefficients_helicity_basis
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C + genJ P A C = (2 : ℤ) • conePlus P A ∧
    genPhi P A C - genJ P A C = (2 : ℤ) • coneMinus P C := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 2 (`phononCAR`):**
Fermionic/phonon CAR-type anticommutation relations on the Peirce corners:
`{N_+, N_+} = 0`, `{N_-, N_-} = 0`, `{N_+, N_-} = V`, and `{Φ, J} = 0`. -/
theorem archetype_phononCAR_corner_anticommutators
    {P : B} (hP : P * P = P) (A C : B) :
    anticomm (conePlus P A) (conePlus P A) = 0 ∧
    anticomm (coneMinus P C) (coneMinus P C) = 0 ∧
    anticomm (conePlus P A) (coneMinus P C) = genV P A C ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 := by
  refine ⟨?_, ?_, rfl, ?_⟩ <;> peirce_nf hP

/-- **Archetype 3 (`operatorSplit`):**
Exact operator splitting of `Φ²` and `J²` into the symmetric anticommutator `V = {N_+, N_-}`
and the commutator `[Φ, J] = -2 • Σ`. -/
theorem archetype_operatorSplit_quadratic_resolution
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 4 (`complexStrength`):**
Para-complex / complex coupling strength relations:
`(Φ * J)² = Σ² = V²` and `Φ * J * Φ = -(V * J)`, `J * Φ * J = V * Φ`. -/
theorem archetype_complexStrength_bivector_square
    {P : B} (hP : P * P = P) (A C : B) :
    (genPhi P A C * genJ P A C) * (genPhi P A C * genJ P A C) = genV P A C * genV P A C ∧
    genPhi P A C * genJ P A C * genPhi P A C = -(genV P A C * genJ P A C) ∧
    genJ P A C * genPhi P A C * genJ P A C = genV P A C * genPhi P A C := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 5 (`cocyclicTransport`):**
Cocyclic transport under the grading involution `S_P`:
`S_P * N_+ * S_P = -N_+`, `S_P * N_- * S_P = -N_-`, and `S_P * V * S_P = V`. -/
theorem archetype_cocyclicTransport_grading_conjugation
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C * invS P = -coneMinus P C ∧
    invS P * genV P A C * invS P = genV P A C := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 6 (`dressedInterference`):**
Dressed cross-channel interference identity:
`(N_+ + N_-)² - (N_+ - N_-)² = 2 • V` and
`sandwichCross P A C X + sandwichSame P A C X = Φ * X * Φ`. -/
theorem archetype_dressedInterference_cross_sandwich
    {P : B} (hP : P * P = P) (A C X : B) :
    genPhi P A C * genPhi P A C - genJ P A C * genJ P A C = (2 : ℤ) • genV P A C ∧
    sandwichCross P A C X + sandwichSame P A C X =
      genPhi P A C * X * genPhi P A C := by
  refine ⟨?_, ?_⟩
  · peirce_nf hP
  · simp only [sandwichCross, sandwichSame]; peirce_nf hP

/-- **Archetype 7 (`phaseInvariantCommutator`):**
Phase-invariant commutator identity: the commutator `[N_+, N_-] = Σ` is invariant under
the chiral phase reflection `(N_+, N_-) ↦ (-N_+, -N_-)` and satisfies `[Σ, V] = 0`. -/
theorem archetype_phaseInvariantCommutator_chiral_invariance
    {P : B} (hP : P * P = P) (A C : B) :
    comm (-conePlus P A) (-coneMinus P C) = comm (conePlus P A) (coneMinus P C) ∧
    comm (genSig P A C) (genV P A C) = 0 := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Master Synthesis (`soloviev_interference_dependency_master_synthesis`):**
Unites the partial-order branch theorems with all seven non-commutative `[Ring B]`
dressed-interference operator theorems. -/
theorem soloviev_interference_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X : B) :
    (circularCoefficients < operatorSplit ∧ phononCAR < operatorSplit ∧
      complexStrength < dressedInterference ∧ cocyclicTransport < dressedInterference ∧
      phononCAR < phaseInvariantCommutator ∧ complexStrength < phaseInvariantCommutator) ∧
    (genPhi P A C + genJ P A C = (2 : ℤ) • conePlus P A) ∧
    (anticomm (genPhi P A C) (genJ P A C) = 0) ∧
    (comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C)) ∧
    ((genPhi P A C * genJ P A C) * (genPhi P A C * genJ P A C) = genV P A C * genV P A C) ∧
    (invS P * genV P A C * invS P = genV P A C) ∧
    (sandwichCross P A C X + sandwichSame P A C X = genPhi P A C * X * genPhi P A C) ∧
    (comm (genSig P A C) (genV P A C) = 0) := by
  have h1 := archetype_circularCoefficients_helicity_basis hP A C
  have h2 := archetype_phononCAR_corner_anticommutators hP A C
  have h3 := archetype_operatorSplit_quadratic_resolution hP A C
  have h4 := archetype_complexStrength_bivector_square hP A C
  have h5 := archetype_cocyclicTransport_grading_conjugation hP A C
  have h6 := archetype_dressedInterference_cross_sandwich hP A C X
  have h7 := archetype_phaseInvariantCommutator_chiral_invariance hP A C
  exact ⟨causal_branches, h1.1, h2.2.2.2, h3.2.2, h4.1, h5.2.2, h6.2, h7.2⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Physics.SolovievDressedInterference.ProofDependency
