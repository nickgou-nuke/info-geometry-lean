/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# A finite partial order for the graded inverse compilation stages

This is an explicit dependency specification, not a claim to extract Lean's
entire declaration graph. In particular the metric and algebraic inverse
branches remain incomparable before their joint recovery stage.
-/

namespace InfoGeometry.Canonical.GradedDMPDependencyOrder

inductive Stage where
  | retract | peirce | drazin | penrose | hybrid | obstruction | transport | witness
  deriving DecidableEq

instance : Fintype Stage where
  elems := {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose,
    Stage.hybrid, Stage.obstruction, Stage.transport, Stage.witness}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | .retract => {Stage.retract}
  | .peirce => {Stage.retract, Stage.peirce}
  | .drazin => {Stage.retract, Stage.peirce, Stage.drazin}
  | .penrose => {Stage.penrose}
  | .hybrid => {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose, Stage.hybrid}
  | .obstruction =>
      {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose, Stage.hybrid, Stage.obstruction}
  | .transport =>
      {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose, Stage.hybrid, Stage.transport}
  | .witness => {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose,
      Stage.hybrid, Stage.obstruction, Stage.transport, Stage.witness}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem inverse_branches_incomparable :
    ¬Stage.drazin ≤ Stage.penrose ∧ ¬Stage.penrose ≤ Stage.drazin := by decide

theorem join_requires_both : Stage.drazin ≤ Stage.hybrid ∧ Stage.penrose ≤ Stage.hybrid := by
  decide

theorem continuation_branches_incomparable :
    ¬Stage.obstruction ≤ Stage.transport ∧ ¬Stage.transport ≤ Stage.obstruction := by decide

theorem stages_reach_witness (s : Stage) : s ≤ Stage.witness := by cases s <;> decide

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Stage 1 (`retract`):**
Idempotent retract decomposition `P + (1 - P) = 1`, orthogonal annihilation
`P * (1 - P) = 0`, `(1 - P) * P = 0`, and grading involution `invS P * invS P = 1`. -/
theorem stage_retract_idempotent_partition
    {P : B} (hP : P * P = P) :
    P + (1 - P) = 1 ∧
    P * (1 - P) = 0 ∧
    (1 - P) * P = 0 ∧
    invS P * invS P = 1 := by
  refine ⟨by abel, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 2 (`peirce`):**
Four-corner Peirce block decomposition `X = evenGrade P X + oddGrade P X` and exact
grading parity `invS P * evenGrade P X = evenGrade P X * invS P` and
`invS P * oddGrade P X = -(oddGrade P X * invS P)`. -/
theorem stage_peirce_graded_decomposition
    {P : B} (hP : P * P = P) (X : B) :
    evenGrade P X + oddGrade P X = X ∧
    comm (invS P) (evenGrade P X) = 0 ∧
    anticomm (invS P) (oddGrade P X) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [evenGrade, oddGrade]; peirce_nf hP)

/-- **Stage 3 (`drazin`):**
Spectral Drazin-branch cubic reduction for the inner derivation `ad_P`:
`comm P (comm P (comm P X)) = comm P X` and `comm P (evenGrade P X) = 0`. -/
theorem stage_drazin_inner_derivation_tripotence
    {P : B} (hP : P * P = P) (X : B) :
    comm P (comm P (comm P X)) = comm P X ∧
    comm P (evenGrade P X) = 0 := by
  refine ⟨?_, ?_⟩
  · peirce_nf hP
  · simp only [evenGrade]; peirce_nf hP

/-- **Stage 4 (`penrose`):**
Moore–Penrose-type partial-isometry sandwich laws on the off-diagonal corners:
`N_+ * N_- * N_+ = V * N_+ = N_+ * V` and `N_- * N_+ * N_- = V * N_- = N_- * V`. -/
theorem stage_penrose_corner_tripotent_sandwiches
    {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * coneMinus P C * conePlus P A = genV P A C * conePlus P A ∧
    conePlus P A * coneMinus P C * conePlus P A = conePlus P A * genV P A C ∧
    coneMinus P C * conePlus P A * coneMinus P C = genV P A C * coneMinus P C ∧
    coneMinus P C * conePlus P A * coneMinus P C = coneMinus P C * genV P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 5 (`hybrid`):**
DMP hybrid join identity combining the Drazin grading projector and the Penrose
off-diagonal sandwich: `Φ * Φ * Φ = V * Φ` and `J * J * J = -(V * J)`. -/
theorem stage_hybrid_dmp_cubic_closure
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C ∧
    genJ P A C * genJ P A C * genJ P A C = -(genV P A C * genJ P A C) := by
  refine ⟨?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 6 (`obstruction`):**
Non-commutative commutator obstruction between `Φ` and `J`:
`comm Φ J = -2 • Σ`, `anticomm Φ J = 0`, and `Σ * Σ = V * V`. -/
theorem stage_obstruction_chiral_commutator
    {P : B} (hP : P * P = P) (A C : B) :
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 7 (`transport`):**
Parallel transport along the axial generator `Σ`:
`comm Σ N_+ = 2 • (V * N_+)`, `comm Σ N_- = -2 • (V * N_-)`,
`comm Σ Φ = 2 • (V * J)`, and `comm Σ J = 2 • (V * Φ)`. -/
theorem stage_transport_axial_parallel_flow
    {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) ∧
    comm (genSig P A C) (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 8 (`witness`):**
Master synthesis of `GradedDMPDependencyOrder` uniting the poset structure with
all seven upstream non-commutative `[Ring B]` operator identities. -/
theorem stage_witness_graded_dmp_master_synthesis
    {P : B} (hP : P * P = P) (A C X : B) :
    (∀ s : Stage, s ≤ Stage.witness) ∧
    (P + (1 - P) = 1 ∧ invS P * invS P = 1) ∧
    (evenGrade P X + oddGrade P X = X) ∧
    (comm P (comm P (comm P X)) = comm P X) ∧
    (conePlus P A * coneMinus P C * conePlus P A = genV P A C * conePlus P A) ∧
    (genPhi P A C * genPhi P A C * genPhi P A C = genV P A C * genPhi P A C) ∧
    (comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C)) ∧
    (comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)) := by
  have h1 := stage_retract_idempotent_partition hP
  have h2 := stage_peirce_graded_decomposition hP X
  have h3 := stage_drazin_inner_derivation_tripotence hP X
  have h4 := stage_penrose_corner_tripotent_sandwiches hP A C
  have h5 := stage_hybrid_dmp_cubic_closure hP A C
  have h6 := stage_obstruction_chiral_commutator hP A C
  have h7 := stage_transport_axial_parallel_flow hP A C
  exact ⟨stages_reach_witness, ⟨h1.1, h1.2.2.2⟩, h2.1, h3.1, h4.1, h5.1, h6.1, h7.2.2.1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Canonical.GradedDMPDependencyOrder
