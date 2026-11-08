/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Star.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-!
# Dependency partial order of the Peirce-coupling compilation

This finite order specifies mathematical stages, not an extracted declaration
graph or physical causality. The Gram stage includes faithful trace and kernel
results as well as positivity; trace and adjoint inputs remain incomparable.
-/

namespace InfoGeometry.NCG.OppositePeirceOrder

inductive Stage where
  | corners | grading | coupling | trace | adjoint | gram | krein | witness
  deriving DecidableEq

instance : Fintype Stage where
  elems := {Stage.corners, Stage.grading, Stage.coupling, Stage.trace,
    Stage.adjoint, Stage.gram, Stage.krein, Stage.witness}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | .corners => {Stage.corners}
  | .grading => {Stage.corners, Stage.grading}
  | .coupling => {Stage.corners, Stage.grading, Stage.coupling}
  | .trace => {Stage.corners, Stage.grading, Stage.coupling, Stage.trace}
  | .adjoint => {Stage.corners, Stage.adjoint}
  | .gram => {Stage.corners, Stage.grading, Stage.coupling, Stage.trace, Stage.adjoint, Stage.gram}
  | .krein => {Stage.corners, Stage.grading, Stage.coupling, Stage.trace,
      Stage.adjoint, Stage.gram, Stage.krein}
  | .witness => {Stage.corners, Stage.grading, Stage.coupling, Stage.trace,
      Stage.adjoint, Stage.gram, Stage.krein, Stage.witness}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem trace_adjoint_incomparable :
    ¬Stage.trace ≤ Stage.adjoint ∧ ¬Stage.adjoint ≤ Stage.trace := by decide

theorem metric_stage_requires_both : Stage.trace ≤ Stage.gram ∧ Stage.adjoint ≤ Stage.gram := by
  decide

theorem stages_reach_witness (s : Stage) : s ≤ Stage.witness := by cases s <;> decide

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Stage 1 (`corners`):**
Opposite Peirce corners `N_+ = P A (1 - P)` and `N_- = (1 - P) C P` satisfy square-zero
nilpotency and opposite idempotent absorption. -/
theorem stage_corners_opposite_peirce
    {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    P * conePlus P A = conePlus P A ∧
    conePlus P A * (1 - P) = conePlus P A ∧
    (1 - P) * coneMinus P C = coneMinus P C ∧
    coneMinus P C * P = coneMinus P C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 2 (`grading`):**
The grading involution `S_P = P - (1 - P)` satisfies `S_P² = 1`, `P * S_P = P`,
`(1 - P) * S_P = -(1 - P)`, and grades the opposite corners with opposite signs:
`S_P * N_+ = N_+ = - (N_+ * S_P)` and `S_P * N_- = -N_- = - (N_- * S_P)`. -/
theorem stage_grading_involution_parity
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * invS P = 1 ∧
    invS P * conePlus P A = conePlus P A ∧
    conePlus P A * invS P = -conePlus P A ∧
    invS P * coneMinus P C = -coneMinus P C ∧
    coneMinus P C * invS P = coneMinus P C ∧
    anticomm (invS P) (genPhi P A C) = 0 ∧
    anticomm (invS P) (genJ P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 3 (`coupling`):**
Cross-corner coupling operators `V = {N_+, N_-}` and `Σ = [N_+, N_-]` satisfy
`Φ² = V`, `J² = -V`, `[Φ, J] = -2 • Σ`, `{Φ, J} = 0`, and `Σ² = V²`. -/
theorem stage_coupling_cross_corner_brackets
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 4 (`trace`):**
Diagonal Peirce block decomposition of `V` and `Σ`:
`peirce11 P V = N_+ N_-`, `peirce00 P V = N_- N_+`,
`peirce11 P V + peirce00 P V = V`, and `peirce11 P V - peirce00 P V = Σ`. -/
theorem stage_trace_peirce_block_split
    {P : B} (hP : P * P = P) (A C : B) :
    peirce11 P (genV P A C) = conePlus P A * coneMinus P C ∧
    peirce00 P (genV P A C) = coneMinus P C * conePlus P A ∧
    peirce11 P (genV P A C) + peirce00 P (genV P A C) = genV P A C ∧
    peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirce11, peirce00]; peirce_nf hP)

/-- **Stage 5 (`adjoint`):**
In any `[StarRing B]`, if `star P = P`, then `star` interchanges the opposite Peirce corners:
`star (conePlus P A) = coneMinus P (star A)` and `star (coneMinus P C) = conePlus P (star C)`. -/
theorem stage_adjoint_corner_interchange
    [StarRing B] {P : B} (hPstar : star P = P) (A C : B) :
    star (conePlus P A) = coneMinus P (star A) ∧
    star (coneMinus P C) = conePlus P (star C) := by
  constructor
  · simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPstar, mul_assoc]
  · simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPstar, mul_assoc]

/-- **Stage 6 (`gram`):**
When `C = star A` and `star P = P`, `Φ = N_+ + N_+^*` is self-adjoint (`star Φ = Φ`),
`J = N_+ - N_+^*` is skew-adjoint (`star J = -J`), and the positive Gram operator
`V = N_+ N_+^* + N_+^* N_+` is self-adjoint (`star V = V`). -/
theorem stage_gram_self_adjoint_positive_coupling
    [StarRing B] {P : B} (hPstar : star P = P) (A : B) :
    star (genPhi P A (star A)) = genPhi P A (star A) ∧
    star (genJ P A (star A)) = -genJ P A (star A) ∧
    star (genV P A (star A)) = genV P A (star A) := by
  have h1 := (stage_adjoint_corner_interchange hPstar A (star A)).1
  have h2 : star (coneMinus P (star A)) = conePlus P A := by
    rw [(stage_adjoint_corner_interchange hPstar A (star A)).2, star_star]
  refine ⟨?_, ?_, ?_⟩
  · simp only [genPhi, star_add, h1, h2]
    abel
  · simp only [genJ, star_sub, h1, h2]
    abel
  · simp only [genV, anticomm, star_add, star_mul, h1, h2]

/-- **Stage 7 (`krein`):**
Krein metric stage: the grading operator `S_P = P - (1 - P)` is a self-adjoint unitary
fundamental symmetry (`star S_P = S_P`, `S_P² = 1`), and the Krein-weighted Gram operator
`Σ = S_P * V = V * S_P` is self-adjoint (`star Σ = Σ`) with `Σ² = V²`. -/
theorem stage_krein_indefinite_gram_twist
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A : B) :
    star (invS P) = invS P ∧
    invS P * invS P = 1 ∧
    genSig P A (star A) = invS P * genV P A (star A) ∧
    genSig P A (star A) = genV P A (star A) * invS P ∧
    star (genSig P A (star A)) = genSig P A (star A) := by
  have hS : star (invS P) = invS P := by
    simp only [invS, star_sub, star_one, hPstar]
  have hV : star (genV P A (star A)) = genV P A (star A) :=
    (stage_gram_self_adjoint_positive_coupling hPstar A).2.2
  have hSV1 : genSig P A (star A) = invS P * genV P A (star A) := by peirce_nf hP
  have hSV2 : genSig P A (star A) = genV P A (star A) * invS P := by peirce_nf hP
  refine ⟨hS, by peirce_nf hP, hSV1, hSV2, ?_⟩
  calc
    star (genSig P A (star A)) = star (invS P * genV P A (star A)) := by rw [hSV1]
    _ = star (genV P A (star A)) * star (invS P) := star_mul _ _
    _ = genV P A (star A) * invS P := by rw [hV, hS]
    _ = genSig P A (star A) := hSV2.symm

/-- **Stage 8 (`witness`):**
Master synthesis of `OppositePeirceOrder` combining the 8-stage poset reachability with all
seven upstream `[Ring B] [StarRing B]` non-commutative operator theorems. -/
theorem stage_witness_opposite_peirce_master_synthesis
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A : B) :
    (∀ s : Stage, s ≤ Stage.witness) ∧
    (conePlus P A * conePlus P A = 0 ∧ coneMinus P (star A) * coneMinus P (star A) = 0) ∧
    (invS P * invS P = 1 ∧ anticomm (invS P) (genPhi P A (star A)) = 0) ∧
    (genPhi P A (star A) * genPhi P A (star A) = genV P A (star A) ∧
      genJ P A (star A) * genJ P A (star A) = -genV P A (star A)) ∧
    (peirce11 P (genV P A (star A)) - peirce00 P (genV P A (star A)) = genSig P A (star A)) ∧
    (star (conePlus P A) = coneMinus P (star A)) ∧
    (star (genPhi P A (star A)) = genPhi P A (star A) ∧
      star (genV P A (star A)) = genV P A (star A)) ∧
    (genSig P A (star A) = invS P * genV P A (star A) ∧
      star (genSig P A (star A)) = genSig P A (star A)) := by
  have h1 := stage_corners_opposite_peirce hP A (star A)
  have h2 := stage_grading_involution_parity hP A (star A)
  have h3 := stage_coupling_cross_corner_brackets hP A (star A)
  have h4 := stage_trace_peirce_block_split hP A (star A)
  have h5 := stage_adjoint_corner_interchange hPstar A (star A)
  have h6 := stage_gram_self_adjoint_positive_coupling hPstar A
  have h7 := stage_krein_indefinite_gram_twist hP hPstar A
  exact ⟨stages_reach_witness, ⟨h1.1, h1.2.1⟩, ⟨h2.1, h2.2.2.2.2.2.1⟩,
    ⟨h3.1, h3.2.1⟩, h4.2.2.2, h5.1, ⟨h6.1, h6.2.2⟩, ⟨h7.2.2.1, h7.2.2.2.2⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.NCG.OppositePeirceOrder
