/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-! # Prerequisite poset for the signed-transport compilation

This is a sufficient mathematical stage order, not an extracted declaration
DAG or physical causality. Peirce support and metric input are independent;
cyclic trace identities do not imply positivity. Generic octet identities do
not need a Peirce projector or square-zero generators.
-/

namespace InfoGeometry.OperatorAlgebra.SignedTransportOrder

inductive Stage
  | algebra | octet | corners | nilpotent | routing | trace | metric | synthesis
  deriving DecidableEq

open Stage

instance : Fintype Stage where
  elems := {algebra, octet, corners, nilpotent, routing, trace, metric, synthesis}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | .algebra => {algebra}
  | .octet => {algebra, octet}
  | .corners => {algebra, corners}
  | .nilpotent => {algebra, nilpotent}
  | .routing => {algebra, corners, routing}
  | .trace => {algebra, trace}
  | .metric => {algebra, metric}
  | .synthesis => Finset.univ

theorem prerequisites_injective : Function.Injective prerequisites := by
  intro a b h
  have ha : a ∈ prerequisites b := by
    rw [← h]
    cases a <;> simp [prerequisites]
  have hb : b ∈ prerequisites a := by
    rw [h]
    cases b <;> simp [prerequisites]
  clear h
  cases a <;> cases b <;> simp_all [prerequisites]

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem octet_corners_independent : ¬ octet ≤ corners ∧ ¬ corners ≤ octet := by
  change ¬ prerequisites octet ⊆ prerequisites corners ∧
    ¬ prerequisites corners ⊆ prerequisites octet
  simp [prerequisites, Finset.subset_iff]

theorem routing_metric_independent : ¬ routing ≤ metric ∧ ¬ metric ≤ routing := by
  change ¬ prerequisites routing ⊆ prerequisites metric ∧
    ¬ prerequisites metric ⊆ prerequisites routing
  simp [prerequisites, Finset.subset_iff]

theorem trace_metric_independent : ¬ trace ≤ metric ∧ ¬ metric ≤ trace := by
  change ¬ prerequisites trace ⊆ prerequisites metric ∧
    ¬ prerequisites metric ⊆ prerequisites trace
  simp [prerequisites, Finset.subset_iff]

theorem synthesis_contains_all (s : Stage) : s ≤ synthesis := by
  change prerequisites s ⊆ Finset.univ
  exact Finset.subset_univ _

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Stage 1 (`algebra`):**
Universal commutator-anticommutator product decomposition over `[Ring B]`. -/
theorem stage_algebra_product_identities (X Y : B) :
    anticomm X Y + comm X Y = (2 : ℤ) • (X * Y) ∧
    anticomm X Y - comm X Y = (2 : ℤ) • (Y * X) := by
  refine ⟨?_, ?_⟩ <;>
    (dsimp only [PeirceSpine.comm, PeirceSpine.anticomm]; noncomm_ring)

/-- **Stage 2 (`octet`):**
Universal Lie–Jordan octet identities (no idempotent or nilpotency assumed):
Jacobi identity, Leibniz derivation law, and Jordan associator identity. -/
theorem stage_octet_universal_identities (X Y Z : B) :
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 ∧
    comm X (anticomm Y Z) = anticomm (comm X Y) Z + anticomm Y (comm X Z) ∧
    anticomm X (anticomm Y Z) - anticomm Y (anticomm X Z) = comm (comm X Y) Z := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (dsimp only [PeirceSpine.comm, PeirceSpine.anticomm]; noncomm_ring)

/-- **Stage 3 (`corners`):**
Idempotent Peirce corner absorption and orthogonality. -/
theorem stage_corners_peirce_absorption
    {P : B} (hP : P * P = P) (A C : B) :
    P * conePlus P A = conePlus P A ∧
    conePlus P A * (1 - P) = conePlus P A ∧
    (1 - P) * coneMinus P C = coneMinus P C ∧
    coneMinus P C * P = coneMinus P C ∧
    conePlus P A * P = 0 ∧
    P * coneMinus P C = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 4 (`nilpotent`):**
Square-zero nilpotency of same-corner products `N_+ N_+' = 0` and `N_- N_-' = 0`. -/
theorem stage_nilpotent_same_corner_products
    {P : B} (hP : P * P = P) (A A' C C' : B) :
    conePlus P A * conePlus P A' = 0 ∧
    coneMinus P C * coneMinus P C' = 0 ∧
    sandwichCross P A C (genPhi P A C) = 0 ∧
    sandwichCross P A C (genJ P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · simp only [sandwichCross]; peirce_nf hP
  · simp only [sandwichCross]; peirce_nf hP

/-- **Stage 5 (`routing`):**
Signed transport routing between `Φ = N_+ + N_-` and `J = N_+ - N_-` under the grading
involution `S_P = P - (1 - P)`:
`S_P * Φ = J = - (Φ * S_P)` and `S_P * J = Φ = - (J * S_P)`. -/
theorem stage_routing_signed_corner_transport
    {P : B} (hP : P * P = P) (A C : B) :
    invS P * genPhi P A C = genJ P A C ∧
    genPhi P A C * invS P = -genJ P A C ∧
    invS P * genJ P A C = genPhi P A C ∧
    genJ P A C * invS P = -genPhi P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 6 (`trace`):**
Diagonal Peirce block projection of `Σ = [N_+, N_-]` and `V = {N_+, N_-}`. -/
theorem stage_trace_block_projection
    {P : B} (hP : P * P = P) (A C : B) :
    peirce11 P (genSig P A C) = conePlus P A * coneMinus P C ∧
    peirce00 P (genSig P A C) = -(coneMinus P C * conePlus P A) ∧
    peirce11 P (genV P A C) + peirce00 P (genV P A C) = genV P A C ∧
    peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirce11, peirce00]; peirce_nf hP)

/-- **Stage 7 (`metric`):**
Symmetric metric operator `V = {N_+, N_-}` and signed symplectic operator `Σ = [N_+, N_-]`
satisfy `Φ² = V`, `J² = -V`, `Σ = S_P * V = V * S_P`, and `Σ² = V²`. -/
theorem stage_metric_signed_gram_identities
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genSig P A C = invS P * genV P A C ∧
    genSig P A C = genV P A C * invS P ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage 8 (`synthesis`):**
Master synthesis of `SignedTransportOrder` uniting the 8-stage poset reachability with all
seven upstream `[Ring B]` non-commutative signed-transport theorems. -/
theorem stage_synthesis_signed_transport_master
    {P : B} (hP : P * P = P) (A A' C C' X Y Z : B) :
    (∀ s : Stage, s ≤ synthesis) ∧
    (anticomm X Y + comm X Y = (2 : ℤ) • (X * Y)) ∧
    (anticomm X (anticomm Y Z) - anticomm Y (anticomm X Z) = comm (comm X Y) Z) ∧
    (P * conePlus P A = conePlus P A ∧ coneMinus P C * P = coneMinus P C) ∧
    (conePlus P A * conePlus P A' = 0 ∧ coneMinus P C * coneMinus P C' = 0) ∧
    (invS P * genPhi P A C = genJ P A C ∧ invS P * genJ P A C = genPhi P A C) ∧
    (peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C) ∧
    (genSig P A C = invS P * genV P A C ∧
      genSig P A C * genSig P A C = genV P A C * genV P A C) := by
  have h1 := stage_algebra_product_identities X Y
  have h2 := stage_octet_universal_identities X Y Z
  have h3 := stage_corners_peirce_absorption hP A C
  have h4 := stage_nilpotent_same_corner_products hP A A' C C'
  have h5 := stage_routing_signed_corner_transport hP A C
  have h6 := stage_trace_block_projection hP A C
  have h7 := stage_metric_signed_gram_identities hP A C
  exact ⟨synthesis_contains_all, h1.1, h2.2.2, ⟨h3.1, h3.2.2.2.1⟩, ⟨h4.1, h4.2.1⟩,
    ⟨h5.1, h5.2.2.1⟩, h6.2.2.2, ⟨h7.2.2.1, h7.2.2.2.2⟩⟩

end NonCommutativeOperatorRealization

end InfoGeometry.OperatorAlgebra.SignedTransportOrder
