/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Geometry.DressingField
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Geometry.DressingField.ProofDependency

inductive Archetype
  | equivariantFrame
  | invariantComposite
  | quotientDescent
  | frameCocycle
  | stabilizerObstruction
  | completeNormalForm
  deriving DecidableEq

private def archetypeEquivFin : Archetype ≃ Fin 6 where
  toFun
    | .equivariantFrame => 0
    | .invariantComposite => 1
    | .quotientDescent => 2
    | .frameCocycle => 3
    | .stabilizerObstruction => 4
    | .completeNormalForm => 5
  invFun
    | 0 => .equivariantFrame
    | 1 => .invariantComposite
    | 2 => .quotientDescent
    | 3 => .frameCocycle
    | 4 => .stabilizerObstruction
    | _ => .completeNormalForm
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Archetype := Fintype.ofEquiv (Fin 6) archetypeEquivFin.symm

open Archetype

def prerequisites : Archetype → Finset Archetype
  | equivariantFrame => {equivariantFrame}
  | invariantComposite => {equivariantFrame, invariantComposite}
  | quotientDescent => {equivariantFrame, invariantComposite, quotientDescent}
  | frameCocycle => {equivariantFrame, frameCocycle}
  | stabilizerObstruction => {equivariantFrame, stabilizerObstruction}
  | completeNormalForm => {equivariantFrame, invariantComposite, completeNormalForm}

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
    equivariantFrame < invariantComposite ∧ invariantComposite < quotientDescent ∧
      equivariantFrame < frameCocycle ∧ equivariantFrame < stabilizerObstruction ∧
      invariantComposite < completeNormalForm := by
  simp only [lt_iff_le_not_ge]
  decide

theorem descent_and_obstruction_incomparable :
    ¬ quotientDescent ≤ stabilizerObstruction ∧
      ¬ stabilizerObstruction ≤ quotientDescent := by
  decide

theorem no_dependency_cycle {earlier later : Archetype}
    (forward : earlier < later) : ¬ later < earlier := lt_asymm forward

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`equivariantFrame`):**
Grading involution `S_P = P - (1 - P)` is an involutive operator dressing frame (`S_P² = 1`)
that fixes `P` and `1 - P`. -/
theorem archetype_equivariantFrame_grading_involution
    {P : B} (hP : P * P = P) :
    invS P * invS P = 1 ∧
    invS P * P * invS P = P ∧
    invS P * (1 - P) * invS P = 1 - P := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 2 (`invariantComposite`):**
Dressed composite invariants `V = {N_+, N_-}` and `Σ = [N_+, N_-]` are strictly invariant
under conjugation by the dressing frame `S_P`:
`S_P * V * S_P = V` and `S_P * Σ * S_P = Σ`. -/
theorem archetype_invariantComposite_centralizer_stability
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * genV P A C * invS P = genV P A C ∧
    invS P * genSig P A C * invS P = genSig P A C ∧
    comm (invS P) (genV P A C) = 0 ∧
    comm (invS P) (genSig P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 3 (`quotientDescent`):**
Even-grade projection `evenGrade P X = P X P + (1 - P) X (1 - P)` descends invariantly under
`S_P`-conjugation (`S_P * evenGrade P X * S_P = evenGrade P X`) and equals the symmetrized
average `(X + S_P * X * S_P)`. -/
theorem archetype_quotientDescent_even_grade_projection
    {P : B} (hP : P * P = P) (X : B) :
    invS P * evenGrade P X * invS P = evenGrade P X ∧
    X + invS P * X * invS P = (2 : ℤ) • evenGrade P X := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [evenGrade]; peirce_nf hP)

/-- **Archetype 4 (`frameCocycle`):**
Dressing-frame cocycle action on the off-diagonal corners:
`S_P * N_+ = N_+ = -(N_+ * S_P)` and `S_P * N_- = -N_- = -(N_- * S_P)`. -/
theorem archetype_frameCocycle_chiral_sign_action
    {P : B} (hP : P * P = P) (A C X : B) :
    invS P * conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C * invS P = -coneMinus P C ∧
    X - invS P * X * invS P = (2 : ℤ) • oddGrade P X := by
  refine ⟨?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · simp only [oddGrade]; peirce_nf hP

/-- **Archetype 5 (`stabilizerObstruction`):**
Non-trivial stabilizer obstruction on the odd-grade sector: `comm (invS P) (genPhi P A C) = 2 • J`
and `comm (invS P) (genJ P A C) = 2 • Φ`. -/
theorem archetype_stabilizerObstruction_odd_grade_defect
    {P : B} (hP : P * P = P) (A C : B) :
    comm (invS P) (genPhi P A C) = (2 : ℤ) • genJ P A C ∧
    comm (invS P) (genJ P A C) = (2 : ℤ) • genPhi P A C := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 6 (`completeNormalForm`):**
Complete Peirce normal-form decomposition `X = evenGrade P X + oddGrade P X` and reflected
normal form `invS P * X * invS P = evenGrade P X - oddGrade P X`. -/
theorem archetype_completeNormalForm_peirce_resolution
    {P : B} (hP : P * P = P) (X : B) :
    evenGrade P X + oddGrade P X = X ∧
    invS P * X * invS P = evenGrade P X - oddGrade P X := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [evenGrade, oddGrade]; peirce_nf hP)

/-- **Master Synthesis (`dressing_field_dependency_master_synthesis`):**
Unites the partial-order branch theorems with all six non-commutative `[Ring B]`
dressing-field operator theorems. -/
theorem dressing_field_dependency_master_synthesis
    {P : B} (hP : P * P = P) (A C X : B) :
    (equivariantFrame < invariantComposite ∧ invariantComposite < quotientDescent ∧
      equivariantFrame < frameCocycle ∧ equivariantFrame < stabilizerObstruction ∧
      invariantComposite < completeNormalForm) ∧
    (invS P * invS P = 1) ∧
    (invS P * genV P A C * invS P = genV P A C) ∧
    (X + invS P * X * invS P = (2 : ℤ) • evenGrade P X) ∧
    (X - invS P * X * invS P = (2 : ℤ) • oddGrade P X) ∧
    (comm (invS P) (genPhi P A C) = (2 : ℤ) • genJ P A C) ∧
    (evenGrade P X + oddGrade P X = X) := by
  have h1 := archetype_equivariantFrame_grading_involution hP
  have h2 := archetype_invariantComposite_centralizer_stability hP A C
  have h3 := archetype_quotientDescent_even_grade_projection hP X
  have h4 := archetype_frameCocycle_chiral_sign_action hP A C X
  have h5 := archetype_stabilizerObstruction_odd_grade_defect hP A C
  have h6 := archetype_completeNormalForm_peirce_resolution hP X
  exact ⟨causal_branches, h1.1, h2.1, h3.2, h4.2.2, h5.1, h6.1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Geometry.DressingField.ProofDependency
