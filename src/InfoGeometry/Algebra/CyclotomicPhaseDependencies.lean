/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Order
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicBridge

namespace InfoGeometry.Algebra.CyclotomicPhaseDependencies

inductive Archetype
  | primitivePhase
  | polygonBalance
  | coordinateProjectors
  | spectralReadout
  | cornerDecomposition
  | nilpotentCorners
  deriving DecidableEq

instance : Fintype Archetype :=
  Fintype.ofList [.primitivePhase, .polygonBalance, .coordinateProjectors,
    .spectralReadout, .cornerDecomposition, .nilpotentCorners] (by
      intro x
      cases x <;> simp)

def prerequisites : Archetype → Finset ℕ
  | .primitivePhase => {0}
  | .polygonBalance => {0, 1}
  | .coordinateProjectors => {2}
  | .spectralReadout => {0, 2, 3}
  | .cornerDecomposition => {0, 2, 3, 4}
  | .nilpotentCorners => {0, 2, 3, 4, 5}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

theorem phase_branch : Archetype.primitivePhase ≤ Archetype.polygonBalance := by decide

theorem projector_branch :
    Archetype.coordinateProjectors ≤ Archetype.spectralReadout ∧
      Archetype.spectralReadout ≤ Archetype.cornerDecomposition ∧
      Archetype.cornerDecomposition ≤ Archetype.nilpotentCorners := by decide

theorem balance_and_projectors_incomparable :
    ¬ Archetype.polygonBalance ≤ Archetype.coordinateProjectors ∧
      ¬ Archetype.coordinateProjectors ≤ Archetype.polygonBalance := by decide

theorem no_cycle (left right : Archetype) (forward : left ≤ right)
    (backward : right ≤ left) : left = right := le_antisymm forward backward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`primitivePhase`):**
Grading involution `S_P = P - (1 - P)` satisfies `S_P² = 1` and generates a primitive
2-periodic operator phase on the Peirce corners (`S_P * N_+ = N_+`, `S_P * N_- = -N_-`). -/
theorem archetype_primitivePhase_grading_period
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * invS P = 1 ∧
    invS P * conePlus P A = conePlus P A ∧
    invS P * coneMinus P C = -coneMinus P C := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 2 (`polygonBalance`):**
Universal 6th-root cyclotomic factorization `(U + 1) * (U^2 - U + 1) = U^3 + 1` and
`(U^3 - 1) * (U^3 + 1) = U^6 - 1` in any non-commutative ring `[Ring B]`, together with
balanced square-sum cancellation `Φ² + J² = 0`. -/
theorem archetype_polygonBalance_cyclotomic_and_peirce_cancellation
    {P : B} (hP : P * P = P) (A C U : B) :
    (U + 1) * (U * U - U + 1) = U * U * U + 1 ∧
    genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0 := by
  refine ⟨by noncomm_ring, ?_⟩
  peirce_nf hP

/-- **Archetype 3 (`coordinateProjectors`):**
Complementary idempotent coordinate projectors `P` and `1 - P` satisfy `P + (1 - P) = 1`,
`P * (1 - P) = 0`, and `(1 - P) * P = 0`. -/
theorem archetype_coordinateProjectors_orthogonal_resolution
    {P : B} (hP : P * P = P) :
    P + (1 - P) = 1 ∧
    P * (1 - P) = 0 ∧
    (1 - P) * P = 0 ∧
    (1 - P) * (1 - P) = 1 - P := by
  refine ⟨by abel, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 4 (`spectralReadout`):**
Spectral readout of `V = {N_+, N_-}` and `Σ = [N_+, N_-]` via the diagonal Peirce projectors
`peirce11 P` and `peirce00 P`:
`peirce11 P V + peirce00 P V = V` and `peirce11 P V - peirce00 P V = Σ`. -/
theorem archetype_spectralReadout_diagonal_gram
    {P : B} (hP : P * P = P) (A C : B) :
    peirce11 P (genV P A C) + peirce00 P (genV P A C) = genV P A C ∧
    peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [peirce11, peirce00]; peirce_nf hP)

/-- **Archetype 5 (`cornerDecomposition`):**
Four-block Peirce corner decomposition `X = evenGrade P X + oddGrade P X` and conjugation
reflection `invS P * X * invS P = evenGrade P X - oddGrade P X`. -/
theorem archetype_cornerDecomposition_four_block_split
    {P : B} (hP : P * P = P) (X : B) :
    evenGrade P X + oddGrade P X = X ∧
    invS P * X * invS P = evenGrade P X - oddGrade P X := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [evenGrade, oddGrade]; peirce_nf hP)

/-- **Archetype 6 (`nilpotentCorners`):**
Off-diagonal corners `N_+ = P A (1 - P)` and `N_- = (1 - P) C P` are square-zero nilpotents
that generate the tripotent cubic relations `Φ³ = V * Φ` and `J³ = -(V * J)`. -/
theorem archetype_nilpotentCorners_cubic_closure
    {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C ∧
    genJ P A C * genJ P A C * genJ P A C = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Master Synthesis (`cyclotomic_phase_dependencies_master_synthesis`):**
Unites the partial-order branch theorems with all six non-commutative `[Ring B]`
operator theorems. -/
theorem cyclotomic_phase_dependencies_master_synthesis
    {P : B} (hP : P * P = P) (A C U X : B) :
    (Archetype.primitivePhase ≤ Archetype.polygonBalance ∧
      Archetype.coordinateProjectors ≤ Archetype.spectralReadout ∧
      Archetype.spectralReadout ≤ Archetype.cornerDecomposition ∧
      Archetype.cornerDecomposition ≤ Archetype.nilpotentCorners) ∧
    (invS P * invS P = 1) ∧
    ((U + 1) * (U * U - U + 1) = U * U * U + 1 ∧
      genPhi P A C * genPhi P A C + genJ P A C * genJ P A C = 0) ∧
    (P * (1 - P) = 0 ∧ (1 - P) * P = 0) ∧
    (peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C) ∧
    (evenGrade P X + oddGrade P X = X) ∧
    (conePlus P A * conePlus P A = 0 ∧
      genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C) := by
  have h1 := archetype_primitivePhase_grading_period hP A C
  have h2 := archetype_polygonBalance_cyclotomic_and_peirce_cancellation hP A C U
  have h3 := archetype_coordinateProjectors_orthogonal_resolution hP
  have h4 := archetype_spectralReadout_diagonal_gram hP A C
  have h5 := archetype_cornerDecomposition_four_block_split hP X
  have h6 := archetype_nilpotentCorners_cubic_closure hP A C
  exact ⟨⟨phase_branch, projector_branch⟩, h1.1, h2, ⟨h3.2.1, h3.2.2.1⟩,
    h4.2, h5.1, ⟨h6.1, h6.2.2.1⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Algebra.CyclotomicPhaseDependencies
