/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-! # A finite prerequisite order for the two source streams

The relation records sufficient mathematical prerequisites, not physical
causation or an extracted whole-repository declaration graph.
-/
namespace InfoGeometry.Core.PeirceSourceOrder

inductive Stage
  | algebra | support | octet | frame | trace | reflection | iteration | synthesis
  deriving DecidableEq

open Stage

instance : Fintype Stage where
  elems := {algebra, support, octet, frame, trace, reflection, iteration, synthesis}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | algebra => {algebra}
  | support => {algebra, support}
  | octet => {algebra, octet}
  | frame => {algebra, support, frame}
  | trace => {algebra, octet, trace}
  | reflection => {algebra, support,octet, reflection}
  | iteration => {algebra, support, frame, iteration}
  | synthesis => Finset.univ

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem support_octet_independent : ¬ support ≤ octet ∧ ¬ octet ≤ support := by decide

theorem trace_frame_independent : ¬ trace ≤ frame ∧ ¬ frame ≤ trace := by decide

theorem frame_precedes_iteration : frame ≤ iteration := by decide

theorem reflection_joins_inputs : support ≤ reflection ∧ octet ≤ reflection := by decide

theorem synthesis_covers (s : Stage) : s ≤ synthesis := by cases s <;> decide

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Stage 1 (`algebra`):**
Universal non-commutative Lie–Jordan derivation and graded-Leibniz identities over `[Ring B]`. -/
theorem stage_algebra_leibniz_identities (X Y Z : B) :
    comm X (Y * Z) = comm X Y * Z + Y * comm X Z ∧
    comm (X * Y) Z = X * anticomm Y Z - anticomm X Z * Y ∧
    anticomm X (Y * Z) = anticomm X Y * Z - Y * comm X Z := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]; noncomm_ring)

/-- **Stage 2 (`support`):**
Peirce support absorption and square-zero nilpotence of `N_+ = P A (1 - P)` and `N_- = (1 - P) C P`. -/
theorem stage_support_peirce_corners
    {P : B} (hP : P * P = P) (A C : B) :
    P * conePlus P A = conePlus P A ∧
    conePlus P A * P = 0 ∧
    coneMinus P C * P = coneMinus P C ∧
    P * coneMinus P C = 0 ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 3 (`octet`):**
Universal Lie–Jordan octet decomposition of associative products and Jacobi identity. -/
theorem stage_octet_lie_jordan_splitting (X Y Z : B) :
    comm X Y + comm Y X = 0 ∧
    anticomm X Y = anticomm Y X ∧
    anticomm X Y + comm X Y = (2 : ℤ) • (X * Y) ∧
    anticomm X Y - comm X Y = (2 : ℤ) • (Y * X) ∧
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]; abel
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]; noncomm_ring
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]; noncomm_ring
  · dsimp only [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]; noncomm_ring

/-- **Stage 4 (`frame`):**
Tetraktys operator frame `(Φ, J, V, Σ)` quadratic and centralizer relations. -/
theorem stage_frame_tetraktys_quadratic
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C ∧
    comm (genV P A C) (genSig P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 5 (`trace`):**
Diagonal Peirce block projection of the symplectic commutator `Σ = [N_+, N_-]` and symmetric
metric `V = {N_+, N_-}`. -/
theorem stage_trace_diagonal_block_decomposition
    {P : B} (hP : P * P = P) (A C : B) :
    peirce11 P (genSig P A C) = conePlus P A * coneMinus P C ∧
    peirce00 P (genSig P A C) = -(coneMinus P C * conePlus P A) ∧
    peirce11 P (genSig P A C) + peirce00 P (genSig P A C) = genSig P A C ∧
    peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirce11, peirce00]; peirce_nf hP)

/-- **Stage 6 (`reflection`):**
Grading involution `S_P = 2P - 1` conjugation laws on `(Φ, J, V, Σ)`. -/
theorem stage_reflection_grading_conjugation
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * invS P = 1 ∧
    invS P * genPhi P A C * invS P = -genPhi P A C ∧
    invS P * genJ P A C * invS P = -genJ P A C ∧
    invS P * genV P A C * invS P = genV P A C ∧
    invS P * genSig P A C * invS P = genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 7 (`iteration`):**
Iterated inner-derivation operator eigenvalue laws for `derivSqPhi`, `derivSqJ`, and `derivSqSig`. -/
theorem stage_iteration_double_commutator_eigenvalues
    {P : B} (hP : P * P = P) (A C : B) :
    derivSqPhi P A C (genPhi P A C) = 0 ∧
    derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    derivSqJ P A C (genPhi P A C) = -((4 : ℤ) • (genV P A C * genPhi P A C)) ∧
    derivSqSig P A C (genPhi P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    derivSqSig P A C (genJ P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [derivSqPhi, derivSqJ, derivSqSig]; peirce_nf hP)

/-- **Stage 8 (`synthesis`):**
Master synthesis of `PeirceSourceOrder` uniting the 8-stage partial order with all
seven upstream non-commutative `[Ring B]` operator theorems. -/
theorem stage_synthesis_peirce_source_master
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (∀ s : Stage, s ≤ synthesis) ∧
    (comm X (Y * Z) = comm X Y * Z + Y * comm X Z) ∧
    (conePlus P A * conePlus P A = 0 ∧ coneMinus P C * coneMinus P C = 0) ∧
    (comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0) ∧
    (genPhi P A C * genPhi P A C = genV P A C ∧ genJ P A C * genJ P A C = -genV P A C) ∧
    (peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C) ∧
    (invS P * genPhi P A C * invS P = -genPhi P A C) ∧
    (derivSqSig P A C (genPhi P A C) = -((4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C))) := by
  have h1 := stage_algebra_leibniz_identities X Y Z
  have h2 := stage_support_peirce_corners hP A C
  have h3 := stage_octet_lie_jordan_splitting X Y Z
  have h4 := stage_frame_tetraktys_quadratic hP A C
  have h5 := stage_trace_diagonal_block_decomposition hP A C
  have h6 := stage_reflection_grading_conjugation hP A C
  have h7 := stage_iteration_double_commutator_eigenvalues hP A C
  exact ⟨synthesis_covers, h1.1, h2.2.2.2.2, h3.2.2.2.2,
    ⟨h4.1, h4.2.1⟩, h5.2.2.2, h6.2.1, h7.2.2.2.1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.Core.PeirceSourceOrder
