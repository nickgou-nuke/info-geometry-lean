/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.WheelerSingleCommutatorHistoricalPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.IKKTLaxHolographicDarkCondensatePoset

/-!
# Five-Textbook Rosetta Stone, Emergent Nilpotent Novelty, Eighth-Order Commutator–Tomita
# Frontiers, Complete Historical Physics Dictionary (`𝔉𝔓₁..𝔉𝔓₁₀`), and Decadic Unruh Ladders
# Poset (`ℌ𝔗₁ ≺ ⋯ ≺ ℌ𝔗₅`)

This module formalizes the remaining standalone intermediate and frontier theorems from the
AI Studio epistemic compilation (`Fences #12, #25, #29, #33, #35, #37, #40, #45, #47, #49, #51`)
over an arbitrary associative (noncommutative) ring `B` (`[Ring B]`):

* `HT1` (`node1_five_textbook_rosetta_and_emergent_nilpotent_novelty`):
  The Five-Textbook Rosetta Stone (`five_textbook_silos_rosetta_stone`) and the Master Theorem
  of Emergent Novelty from Disjoint Nilpotents (`emergent_novelty_from_disjoint_nilpotents`),
  showing how non-commutative cross-terms of square-zero/idempotent primitives generate the
  metric `V`, Hodge Laplacian `[V, Z]`, rotating-ball equilibria, and cubic Bruhat sag `+V³`.
* `HT2` (`node2_wheeler_primordial_distinction_and_two_bit_24_tower`):
  Wheeler's Primordial Distinction Theorem (`wheeler_it_from_noncommutative_bit`), the
  7-stage Inevitability Theorem (`wheeler_how_could_it_have_been_otherwise`), pure 1-bit
  intrinsic modular Lax transport (`one_bit_single_operator_genesis_and_intrinsic_lax_transport`),
  and the complete 2-bit Boolean XOR/XNOR `24 = 4!` Lagrange spectral resolution of `24 • Z`
  across all five horizon grades (`two_commuting_bits_xor_xnor_five_graded_24_tower`).
* `HT3` (`node3_eighth_order_three_frontiers_commutator_ladder_tomita_well`):
  - **Frontier 1 (`frontier1_explicit_commutator_metric_spin_and_riemann_curvature`)**:
    Explicit polynomial expansion `V = P X² P + X P X - P X P X - X P X P`, Weitzenböck
    commutator `[d_+, d_-](Σ) = [J, Φ]² = 4 J⁴ = 4 V²`, and 4th/5th-order Cotton/centrifugal
    nested commutator identities `[[Φ, [Φ, J]], Φ] = 8 V Σ` and
    `[[J, Φ], [[J, Φ], Φ]] + 4 V [J, [J, Φ]] = 0`.
  - **Frontier 2 (`frontier2_nilpotent_differentials_climb_five_graded_maurer_cartan_tower`)**:
    Nilpotent differentials `d_out/in² = 0` climbing the 2-bit 5-graded tower:
    `d_tot(H) = -(N_{+1} - N_{-1})`, `d_tot²(H) = [V_PK, H] = -2(N_{+2} - N_{-2})`, and
    unipotent Maurer–Cartan dressing `g⁻¹ H g = H + (N_{+1} - N_{+2})`.
  - **Frontier 3 (`frontier3_tomita_takesaki_modular_laplacian_parabolic_well_bridge`)**:
    Twin-bimodule Tomita–Takesaki modular Laplacian `δ_K²(Φ) = L_{K²}(Φ) + R_{K²}(Φ) - 2 C_K(Φ)`
    at `K = J` and `K = Σ`, proving `C_Σ(Φ) + V C_J(Φ) = 0` and `δ_Σ²(Φ) + V δ_J²(Φ) = 0`.
* `HT4` (`node4_named_historical_physics_dictionary_FP1_to_FP10`):
  Explicit named operator dictionary (`S_Eddington`, `X_secular_even`, `xi_zitter_odd`,
  `v_zitter`, `ds_FockIvanenko`, `l_NP`, `n_NP`, `V_Jordan`, `Sigma_Fock`, `u_osmotic`,
  `v_coriolis`, `a_Bohm_cent`, `a_Sakharov_well`, `G_FW_plus/minus`, `P_FW_plus/minus`,
  `S_FW_plus/minus`, `NomizuRiemann`), inverse Foldy–Wouthuysen decoupling, universal `1 : 1 : 2`
  Tomita–Sakharov partition of all three metriplectic forces, and complete 5-graded XOR spectrum.
* `HT5` (`node5_two_faces_and_decadic_polynomial_unruh_generating_ladders`):
  Quantum Mechanics `(J, Σ)` and Gravity `(Φ, V)` as two chiral faces of one operator reality
  (`quantum_and_gravity_are_two_faces_of_one_operator_reality`), Sheet-Gramian Bott diamond,
  telescoping polynomial identities (without an inverse or convergence claim)
  `(1 + J²)(1 - J² + J⁴) = 1 + J⁶ = 1 - V³` and
  `(1 + J²)(J - J³ + J⁵) = J + J⁷`, and degree-5 Unruh equilibrium
  `[K_Unruh, [K_Unruh, Φ]] = 4[P, J⁵] = -V[J, [J, Φ]]`.

## i. Overview

This finite-stage module collects algebraic frontiers over arbitrary noncommutative `[Ring B]`.

## ii. Key results

It proves the stated commutator, graded, named-operator, Foldy–Wouthuysen, and polynomial
identities under explicit hypotheses. Polynomial ladder identities do not assert inverses or
convergence.

## iii. Table of contents

1. Emergent nilpotent identities and ranked source results.
2. Eighth-order commutator and finite graded-tower identities.
3. Named historical operator dictionary and Foldy–Wouthuysen results.
4. Decadic polynomial ladders and degree-five identities.

## iv. References

The module imports the Souriau, Amari, Wheeler, and IKKT Peirce-Spine owner modules listed in
the import block above. Their analytic and physical interpretations are not asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.WheelerSingleCommutatorHistoricalPoset

universe u
variable {B : Type u} [Ring B]

/-! ### Ranked Node Enumeration (`ℌ𝔗₁ < ⋯ < ℌ𝔗₅`)

This rank order records presentation order only; it does not assert that every earlier node is a
logical prerequisite of every later node. Dependencies are those actually used by theorem proofs. -/

/-- The five labels in the Historical Dictionary, Tomita Frontiers & polynomial ladder synthesis. -/
inductive HistoricalTomitaFrontierNode : Type
  | HT1_FiveTextbookRosettaEmergentNovelty
  | HT2_WheelerDistinctionTwoBit24Tower
  | HT3_EighthOrderCommutatorTomitaFrontiers
  | HT4_HistoricalPhysicsDictionaryFP1ToFP10
  | HT5_TwoFacesDecadicResolventUnruhLadders
  deriving DecidableEq, Repr

instance : Inhabited HistoricalTomitaFrontierNode :=
  ⟨.HT1_FiveTextbookRosettaEmergentNovelty⟩

/-- Monotone rank embedding `ℌ𝔗_k ↦ k`. -/
def HistoricalTomitaFrontierNode.rank : HistoricalTomitaFrontierNode → ℕ
  | .HT1_FiveTextbookRosettaEmergentNovelty => 1
  | .HT2_WheelerDistinctionTwoBit24Tower => 2
  | .HT3_EighthOrderCommutatorTomitaFrontiers => 3
  | .HT4_HistoricalPhysicsDictionaryFP1ToFP10 => 4
  | .HT5_TwoFacesDecadicResolventUnruhLadders => 5

instance : PartialOrder HistoricalTomitaFrontierNode where
  le a b := a.rank ≤ b.rank
  lt a b := a.rank < b.rank
  le_refl a := Nat.le_refl a.rank
  le_trans _ _ _ hab hbc := Nat.le_trans hab hbc
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm a b hab hba := by
    revert hab hba; cases a <;> cases b <;> decide

instance : DecidableRel (@LE.le HistoricalTomitaFrontierNode _) :=
  fun a b => Nat.decLe a.rank b.rank

instance : DecidableRel (@LT.lt HistoricalTomitaFrontierNode _) :=
  fun a b => Nat.decLt a.rank b.rank

/-! ### Node `ℌ𝔗₁`: Five-Textbook Rosetta Stone & Emergent Novelty from Disjoint Nilpotents -/

/-- **The Five-Textbook Rosetta Stone Theorem (`five_textbook_silos_rosetta_stone`)**:
In any associative ring `B` with idempotent `P * P = P`, the objects of Ring Theory (`Q_±`),
General Relativity (`V, Φ`), Quantum Mechanics (`Σ`), Exterior Calculus (`d_±`), and
Metriplectic Control/Thermodynamics (`-[Φ, [Φ, J]]`) satisfy the unified bridge laws. -/
lemma five_textbook_silos_rosetta_stone
    (P X Y Z : B) (hP : P * P = P) :
    let np := N_plus P X
    let nm := N_minus P Y
    let qp := Q_pos P X Y
    let qm := Q_neg P X Y
    let ph := Phi_v P X Y
    let j  := J_mc P X Y
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    qp + qp = v + s ∧
    qm + qm = v - s ∧
    qp * qm = 0 ∧
    qm * qp = 0 ∧
    d_plus P X nm = v ∧
    d_minus P Y np = v ∧
    d_plus P X ph = v ∧
    ph * ph = v ∧
    s * s = v * v ∧
    comm v s = 0 ∧
    d_plus P X (d_minus P Y Z) + d_minus P Y (d_plus P X Z) = comm v Z ∧
    - comm ph (comm ph j) + (comm s ph + comm s ph) = 0 ∧
    comm s (comm s ph) + v * comm j (comm j ph) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [Q_pos, Q_neg, Phi_v, J_mc, V_met, Sigma_sp,
                d_plus, d_minus, chiralConj, comm]
    amari_peirce_nf hP

/-- **Master Theorem of Emergent Novelty (`emergent_novelty_from_disjoint_nilpotents`)**:
Every isolated primitive has a trivial self-square (`N_+² = 0`, `N_-² = 0`, `d_+² = 0`, `d_-² = 0`,
`P̂_+² = P̂_+`, `P̂_-² = P̂_-`), yet the noncommutative cross-terms of their sums generate:
1. The gravitational/Fisher metric `V` and spin-square equivalence `Σ² = V²`,
2. The Hodge–de Rham Laplacian `[V, Z]`,
3. The 1st- and 2nd-order Souriau–Brockett–Amari rotating-ball equilibria,
4. The cubic Bruhat projector sag `+V³`. -/
lemma emergent_novelty_from_disjoint_nilpotents
    (P X Y Z : B) (hP : P * P = P) :
    let np := N_plus P X
    let nm := N_minus P Y
    let ph := Phi_v P X Y
    let j  := J_mc P X Y
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    let Pe := P_hat_plus P X Y
    let Pm := P_hat_minus P X Y
    np * np = 0 ∧
    nm * nm = 0 ∧
    (np + nm) * (np + nm) - (np * np + nm * nm) = v ∧
    s * s = v * v ∧
    d_plus P X (d_plus P X Z) = 0 ∧
    d_minus P Y (d_minus P Y Z) = 0 ∧
    d_sum P X Y (d_sum P X Y Z) - (d_plus P X (d_plus P X Z) + d_minus P Y (d_minus P Y Z)) = comm v Z ∧
    (d_sum P X Y s + d_sum P X Y s) + (comm s ph + comm s ph) = 0 ∧
    - comm ph (comm ph j) + (comm s ph + comm s ph) = 0 ∧
    comm s (comm s ph) + v * (d_diff P X Y s + d_diff P X Y s) = 0 ∧
    comm s (comm s ph) + v * comm j (comm j ph) = 0 ∧
    Pe * Pe = Pe ∧
    Pm * Pm = Pm ∧
    ((Pe + Pm) * (Pe + Pm) - (Pe * Pe + Pm * Pm)) - (Pe + Pm) = v * v * v := by
  refine ⟨N_plus_sq hP X, N_minus_sq hP Y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg,
                d_sum, d_diff, d_plus, d_minus, chiralConj,
                P_hat_plus, P_hat_minus, Psi1, comm]
    amari_peirce_nf hP

/-! ### Node `ℌ𝔗₂`: Wheeler's Primordial Distinction & Complete 5-Graded `24 = 4!` Lagrange Algebra -/

/-- Grade-0 `24 = 4!` Lagrange polynomial `Poly24_0(H, Z) = 6 ad_H⁴(Z) - 30 ad_H²(Z) + 24 Z`. -/
def Poly24_0 (H Z : B) : B := 6 • adH4 H Z - 30 • adH2 H Z + 24 • Z

/-- Grade-`+1` `24 = 4!` Lagrange polynomial `Poly24_pos1(H, Z) = -4 ad_H⁴(Z) - 4 ad_H³(Z) + 16 ad_H²(Z) + 16 ad_H(Z)`. -/
def Poly24_pos1 (H Z : B) : B := - (4 • adH4 H Z) - 4 • adH3 H Z + 16 • adH2 H Z + 16 • adH H Z

/-- Grade-`-1` `24 = 4!` Lagrange polynomial `Poly24_neg1(H, Z) = -4 ad_H⁴(Z) + 4 ad_H³(Z) + 16 ad_H²(Z) - 16 ad_H(Z)`. -/
def Poly24_neg1 (H Z : B) : B := - (4 • adH4 H Z) + 4 • adH3 H Z + 16 • adH2 H Z - 16 • adH H Z

lemma Poly24_0_add (H A B_op : B) :
    Poly24_0 H (A + B_op) = Poly24_0 H A + Poly24_0 H B_op := by
  dsimp only [Poly24_0, adH4, adH3, adH2, adH]; noncomm_ring

lemma Poly24_pos1_add (H A B_op : B) :
    Poly24_pos1 H (A + B_op) = Poly24_pos1 H A + Poly24_pos1 H B_op := by
  dsimp only [Poly24_pos1, adH4, adH3, adH2, adH]; noncomm_ring

lemma Poly24_neg1_add (H A B_op : B) :
    Poly24_neg1 H (A + B_op) = Poly24_neg1 H A + Poly24_neg1 H B_op := by
  dsimp only [Poly24_neg1, adH4, adH3, adH2, adH]; noncomm_ring

lemma Poly24_all_on_grade_zero {H U : B} (h0 : adH H U = 0) :
    Poly24_0 H U = 24 • U ∧
    Poly24_pos1 H U = 0 ∧
    Poly24_neg1 H U = 0 ∧
    Poly24_pos2 H U = 0 ∧
    Poly24_neg2 H U = 0 := by
  have h00 : adH H (0 : B) = 0 := by unfold adH; simp
  have h2 : adH2 H U = 0 := by unfold adH2; rw [h0, h00]
  have h3 : adH3 H U = 0 := by unfold adH3; rw [h2, h00]
  have h4 : adH4 H U = 0 := by unfold adH4; rw [h3, h00]
  refine ⟨?_, ?_, ?_, (Poly24_on_grade_zero h0).1, (Poly24_on_grade_zero h0).2⟩
  · unfold Poly24_0; rw [h2, h4]; abel
  · unfold Poly24_pos1; rw [h0, h2, h3, h4]; abel
  · unfold Poly24_neg1; rw [h0, h2, h3, h4]; abel

lemma Poly24_all_on_grade_pos1 {H U : B} (h1 : adH H U = U) :
    Poly24_0 H U = 0 ∧
    Poly24_pos1 H U = 24 • U ∧
    Poly24_neg1 H U = 0 ∧
    Poly24_pos2 H U = 0 ∧
    Poly24_neg2 H U = 0 := by
  have h2 : adH2 H U = U := by unfold adH2; rw [h1, h1]
  have h3 : adH3 H U = U := by unfold adH3; rw [h2, h1]
  have h4 : adH4 H U = U := by unfold adH4; rw [h3, h1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Poly24_0; rw [h2, h4]; abel
  · unfold Poly24_pos1; rw [h1, h2, h3, h4]; abel
  · unfold Poly24_neg1; rw [h1, h2, h3, h4]; abel
  · unfold Poly24_pos2; rw [h1, h2, h3, h4]; abel
  · unfold Poly24_neg2; rw [h1, h2, h3, h4]; abel

lemma Poly24_all_on_grade_neg1 {H U : B} (hm1 : adH H U = -U) :
    Poly24_0 H U = 0 ∧
    Poly24_pos1 H U = 0 ∧
    Poly24_neg1 H U = 24 • U ∧
    Poly24_pos2 H U = 0 ∧
    Poly24_neg2 H U = 0 := by
  have h_neg : ∀ W : B, adH H (-W) = - adH H W := fun W => by
    unfold adH; simp only [mul_neg, neg_mul]; abel
  have h2 : adH2 H U = U := by unfold adH2; rw [hm1, h_neg, hm1, neg_neg]
  have h3 : adH3 H U = -U := by unfold adH3; rw [h2, hm1]
  have h4 : adH4 H U = U := by unfold adH4; rw [h3, h_neg, hm1, neg_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Poly24_0; rw [h2, h4]; abel
  · unfold Poly24_pos1; rw [hm1, h2, h3, h4]; abel
  · unfold Poly24_neg1; rw [hm1, h2, h3, h4]; abel
  · unfold Poly24_pos2; rw [hm1, h2, h3, h4]; abel
  · unfold Poly24_neg2; rw [hm1, h2, h3, h4]; abel

lemma Poly24_all_on_grade_pos2 {H U : B} (hL : H * U = U) (hR : U * H = -U) :
    Poly24_0 H U = 0 ∧
    Poly24_pos1 H U = 0 ∧
    Poly24_neg1 H U = 0 ∧
    Poly24_pos2 H U = 24 • U ∧
    Poly24_neg2 H U = 0 := by
  have h1 : adH H U = U + U := by unfold adH; rw [hL, hR]; abel
  have h2 : adH2 H U = (U + U) + (U + U) := by
    unfold adH2; rw [h1]; unfold adH
    simp only [mul_add, add_mul, hL, hR]; abel
  have h3 : adH3 H U = ((U + U) + (U + U)) + ((U + U) + (U + U)) := by
    unfold adH3; rw [h2]; unfold adH
    simp only [mul_add, add_mul, hL, hR]; abel
  have h4 : adH4 H U =
      (((U + U) + (U + U)) + ((U + U) + (U + U))) +
      (((U + U) + (U + U)) + ((U + U) + (U + U))) := by
    unfold adH4; rw [h3]; unfold adH
    simp only [mul_add, add_mul, hL, hR]; abel
  refine ⟨?_, ?_, ?_, (Poly24_on_grade_pos2 hL hR).1, (Poly24_on_grade_pos2 hL hR).2⟩
  · unfold Poly24_0; rw [h2, h4]; abel
  · unfold Poly24_pos1; rw [h1, h2, h3, h4]; abel
  · unfold Poly24_neg1; rw [h1, h2, h3, h4]; abel

lemma Poly24_all_on_grade_neg2 {H U : B} (hL : H * U = -U) (hR : U * H = U) :
    Poly24_0 H U = 0 ∧
    Poly24_pos1 H U = 0 ∧
    Poly24_neg1 H U = 0 ∧
    Poly24_pos2 H U = 0 ∧
    Poly24_neg2 H U = 24 • U := by
  have h1 : adH H U = - (U + U) := by unfold adH; rw [hL, hR]; abel
  have h2 : adH2 H U = (U + U) + (U + U) := by
    unfold adH2; rw [h1]; unfold adH
    simp only [mul_neg, neg_mul, mul_add, add_mul, hL, hR]; abel
  have h3 : adH3 H U = - (((U + U) + (U + U)) + ((U + U) + (U + U))) := by
    unfold adH3; rw [h2]; unfold adH
    simp only [mul_add, add_mul, hL, hR]; abel
  have h4 : adH4 H U =
      (((U + U) + (U + U)) + ((U + U) + (U + U))) +
      (((U + U) + (U + U)) + ((U + U) + (U + U))) := by
    unfold adH4; rw [h3]; unfold adH
    simp only [mul_neg, neg_mul, mul_add, add_mul, hL, hR]; abel
  refine ⟨?_, ?_, ?_, (Poly24_on_grade_neg2 hL hR).1, (Poly24_on_grade_neg2 hL hR).2⟩
  · unfold Poly24_0; rw [h2, h4]; abel
  · unfold Poly24_pos1; rw [h1, h2, h3, h4]; abel
  · unfold Poly24_neg1; rw [h1, h2, h3, h4]; abel

/-- **Wheeler's Primordial Distinction Theorem (`wheeler_it_from_noncommutative_bit`)**:
Given a single idempotent `P * P = P` and operator `X : B`, the 1st commutator `J = [P, X]`
and 2nd commutator `Φ = [P, [P, X]]` automatically satisfy all six laws of noncommutative
spacetime, exterior calculus, and metriplectic gravity. -/
lemma wheeler_it_from_noncommutative_bit
    (P X Z : B) (hP : P * P = P) :
    let sp := S_P P
    let j  := J_1 P X
    let ph := Phi_1 P X
    let np := N_plus_1 P X
    let nm := N_minus_1 P X
    let v  := V_1 P X
    let s  := Sigma_1 P X
    np = P * X * (1 - P) ∧
    nm = (1 - P) * X * P ∧
    np * np = 0 ∧
    nm * nm = 0 ∧
    j  = np - nm ∧
    ph = np + nm ∧
    comm P ph = j ∧
    v = anticomm np nm ∧
    j * j = - v ∧
    s = comm np nm ∧
    s = - (ph * j) ∧
    s = sp * v ∧
    s * s = v * v ∧
    comm v j = 0 ∧ comm v ph = 0 ∧ comm v s = 0 ∧
    comm P v = 0 ∧ comm P s = 0 ∧
    d_plus_1 P X (d_plus_1 P X Z) = 0 ∧
    d_minus_1 P X (d_minus_1 P X Z) = 0 ∧
    d_plus_1 P X nm = v ∧
    d_minus_1 P X np = v ∧
    d_plus_1 P X (d_minus_1 P X Z) + d_minus_1 P X (d_plus_1 P X Z) = comm v Z ∧
    - comm ph (comm ph j) + 2 • comm s ph = 0 ∧
    comm s (comm s ph) + v * comm j (comm j ph) = 0 := by
  refine ⟨N_plus_1_eq hP X, N_minus_1_eq hP X, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · try dsimp only [d_plus_1, d_minus_1, chiralConj]
    try rw [N_plus_1_eq hP X]
    try rw [N_minus_1_eq hP X]
    try rw [J_1_eq P X]
    try rw [Phi_1_eq hP X]
    try rw [V_1_eq hP X]
    try rw [Sigma_1_eq hP X]
    try dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm, anticomm]
    amari_peirce_nf hP

/-- **Wheeler "How Could It Have Been Otherwise?" Inevitability Theorem (`wheeler_how_could_it_have_been_otherwise`)**:
From `hP : P * P = P` and orthogonal horizon pair `(P₁, P₂)`, all seven laws of 3-graded logic,
space/time signature, Wheeler–Gödel–Heisenberg identity, rotating-ball equilibrium, Kähler–Weitzenböck
calculus, Bruhat self-closure, and `24 = 4!` 5-graded contact extraction follow inevitably. -/
lemma wheeler_how_could_it_have_been_otherwise
    (P X Y Z P1 P2 : B)
    (hP : P * P = P)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let sp   := S_P P
    let np   := N_plus P X
    let nm   := N_minus P Y
    let ph   := Phi_v P X Y
    let j    := J_mc P X Y
    let v    := V_met P X Y
    let s    := Sigma_sp P X Y
    let phat := P_hat_plus P X Y
    let H    := P1 - P2
    np * np = 0 ∧ nm * nm = 0 ∧
    comm P (comm P (comm P X)) = comm P X ∧
    sp * sp = 1 ∧ sp * ph = j ∧
    ph * ph = v ∧ j * j = - v ∧
    (P + ph) * (P + ph) - (P + ph) = v ∧
    s = sp * v ∧ s * s = v * v ∧
    - comm ph (comm ph j) + (comm s ph + comm s ph) = 0 ∧
    comm s (comm s ph) + v * comm j (comm j ph) = 0 ∧
    comm P v = 0 ∧ comm P s = 0 ∧
    d_plus P X (d_plus P X Z) = 0 ∧
    d_plus P X nm = v ∧ d_plus P X v = 0 ∧
    d_sum P X Y (d_diff P X Y Z) + d_diff P X Y (d_sum P X Y Z) = 0 ∧
    d_plus P X (d_minus P Y Z) + d_minus P Y (d_plus P X Z) = comm v Z ∧
    d_plus P X (d_minus P Y s) - d_minus P Y (d_plus P X s) = 4 • (v * v) ∧
    G_bruhat_e P X Y * G_bruhat_eInv P X Y = 1 ∧
    G_bruhat_e P X Y * P * G_bruhat_eInv P X Y = phat ∧
    2 • phat = 2 • (P + ph - s) + d_plus P X s ∧
    phat * phat = phat ∧
    H * (H * H) = H ∧
    adH5 H Z - 5 • adH3 H Z + 4 • adH H Z = 0 ∧
    Poly24_pos2 H Z = 24 • (P1 * Z * P2) := by
  intro sp np nm ph j v s phat H
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  have hH_cub : H * (H * H) = H := by
    dsimp only [H]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  set P0 := 1 - P1 - P2
  have hZ_decomp :
      Z = (P1 * Z * P1 + P0 * Z * P0 + P2 * Z * P2) +
          (P1 * Z * P0 + P0 * Z * P2) +
          (P0 * Z * P1 + P2 * Z * P0) +
          (P1 * Z * P2) +
          (P2 * Z * P1) := by
    dsimp only [P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hZ0 : adH H (P1 * Z * P1 + P0 * Z * P0 + P2 * Z * P2) = 0 := by
    dsimp only [adH, H, P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hZp1 : adH H (P1 * Z * P0 + P0 * Z * P2) = P1 * Z * P0 + P0 * Z * P2 := by
    dsimp only [adH, H, P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hZm1 : adH H (P0 * Z * P1 + P2 * Z * P0) = - (P0 * Z * P1 + P2 * Z * P0) := by
    dsimp only [adH, H, P0]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hZp2_L : H * (P1 * Z * P2) = P1 * Z * P2 := by
    dsimp only [H]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hZp2_R : (P1 * Z * P2) * H = - (P1 * Z * P2) := by
    dsimp only [H]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hZm2_L : H * (P2 * Z * P1) = - (P2 * Z * P1) := by
    dsimp only [H]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have hZm2_R : (P2 * Z * P1) * H = P2 * Z * P1 := by
    dsimp only [H]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_pos2 : Poly24_pos2 H Z = 24 • (P1 * Z * P2) := by
    conv_lhs => rw [hZ_decomp]
    rw [Poly24_pos2_add, Poly24_pos2_add, Poly24_pos2_add, Poly24_pos2_add,
        (Poly24_all_on_grade_zero hZ0).2.2.2.1,
        (Poly24_all_on_grade_pos1 hZp1).2.2.2.1,
        (Poly24_all_on_grade_neg1 hZm1).2.2.2.1,
        (Poly24_all_on_grade_pos2 hZp2_L hZp2_R).2.2.2.1,
        (Poly24_all_on_grade_neg2 hZm2_L hZm2_R).2.2.2.1]
    abel
  refine ⟨N_plus_sq hP X, N_minus_sq hP Y, ?_, S_P_sq hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hH_cub, tripotent_quintic_adH hH_cub Z, h_pos2⟩
  · dsimp only [comm]; peirce_base_nf hP
  all_goals
    dsimp only [sp, np, nm, ph, j, v, s, phat,
                Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg,
                chiralConj, d_plus, d_minus, d_sum, d_diff,
                G_bruhat_e, G_bruhat_eInv, P_hat_plus, Psi1, comm]
    amari_peirce_nf hP

/-- **Pure 1-Bit Single-Operator Genesis & Intrinsic Modular Lax Transport (`one_bit_single_operator_genesis_and_intrinsic_lax_transport`)**:
From `hP : P * P = P` and `X : B`, proves all commutator genesis identities, rotating-ball
equilibria, Kähler–Weitzenböck calculus, and intrinsic modular Lax transport
`[P, P̂_±] = [-Φ G_±⁻¹, P̂_±] = J ∓ V Φ`. -/
lemma one_bit_single_operator_genesis_and_intrinsic_lax_transport
    (P X Z : B) (hP : P * P = P) :
    let sp  := S_P P
    let nm  := N_minus_1 P X
    let j   := J_1 P X
    let ph  := Phi_1 P X
    let v   := V_1 P X
    let s   := Sigma_1 P X
    let Gp  := G_plus_1 P X
    let GpI := G_plus_inv_1 P X
    let Gm  := G_minus_1 P X
    let GmI := G_minus_inv_1 P X
    let Php := P_hat_plus_1 P X
    let Phm := P_hat_minus_1 P X
    j  = comm P X ∧
    ph = comm P (comm P X) ∧
    comm P ph = j ∧
    v  = - (comm P X * comm P X) ∧
    v  = ph * ph ∧
    s  = comm P X * comm P (comm P X) ∧
    s  = sp * v ∧
    s * s = v * v ∧
    - comm ph (comm ph j) + 2 • comm s ph = 0 ∧
    comm s (comm s ph) + v * comm j (comm j ph) = 0 ∧
    d_plus_1 P X nm = v ∧
    d_plus_1 P X (d_minus_1 P X Z) + d_minus_1 P X (d_plus_1 P X Z) = comm v Z ∧
    d_plus_1 P X (d_minus_1 P X s) - d_minus_1 P X (d_plus_1 P X s) = 4 • (v * v) ∧
    Gp * P * GpI = Php ∧ Gm * P * GmI = Phm ∧
    Php * Php = Php ∧ Phm * Phm = Phm ∧
    comm P Gp = - ph ∧
    comm P Gm = - ph ∧
    comm P Php = comm (- ph * GpI) Php ∧
    comm P Phm = comm (- ph * GmI) Phm ∧
    comm P Php = j + P * (j * j * j) ∧
    comm P Phm = j + (j * j * j) * P ∧
    comm P Phm - comm P Php = v * ph := by
  have hsato := bloch_schrieffer_wolff_bruhat_and_sato_lax_flow P X hP
  refine ⟨rfl, rfl, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          hsato.2.2.2.1, hsato.2.2.2.2.1, hsato.2.2.2.2.2.2.2.2.1, hsato.2.2.2.2.2.2.2.2.2.1,
          ?_, ?_,
          hsato.2.2.2.2.2.2.2.2.2.2.2.2.1, hsato.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hsato.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hsato.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hsato.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ <;>
  · try dsimp only [G_plus_1, G_minus_1, d_plus_1, d_minus_1, chiralConj]
    try rw [N_plus_1_eq hP X]
    try rw [N_minus_1_eq hP X]
    try rw [J_1_eq P X]
    try rw [Phi_1_eq hP X]
    try rw [V_1_eq hP X]
    try rw [Sigma_1_eq hP X]
    try dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm]
    amari_peirce_nf hP

/-- **Two-Bit Boolean XOR/XNOR Genesis of the 5-Graded `24 = 4!` Horizon Tower (`two_commuting_bits_xor_xnor_five_graded_24_tower`)**:
For any two commuting idempotents `P² = P`, `Q² = Q`, `Q * P = P * Q`, let `P₁ = P(1 - Q)`,
`P₂ = (1 - P)Q`, `H = P - Q`, and `P₀ = 1 - H²`:
1. `P₁`, `P₂`, `P₀` are mutually orthogonal idempotents summing to `1`, with `H³ = H`.
2. All five `24 = 4!` Lagrange polynomials `Poly24_k(H, Z)` extract the exact Peirce horizon
   grades of `24 • Z` and sum to `24 • Z`. -/
lemma two_commuting_bits_xor_xnor_five_graded_24_tower
    (P Q Z : B)
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : Q * P = P * Q) :
    let P1 := P * (1 - Q)
    let P2 := (1 - P) * Q
    let H  := P - Q
    let P0 := 1 - H * H
    P1 * P1 = P1 ∧ P2 * P2 = P2 ∧ P0 * P0 = P0 ∧
    P1 * P2 = 0 ∧ P2 * P1 = 0 ∧ P1 + P0 + P2 = 1 ∧
    H = P1 - P2 ∧ H * H = P1 + P2 ∧ H * (H * H) = H ∧
    adH5 H Z - 5 • adH3 H Z + 4 • adH H Z = 0 ∧
    Poly24_pos2 H Z = 24 • (P1 * Z * P2) ∧
    Poly24_neg2 H Z = 24 • (P2 * Z * P1) ∧
    Poly24_pos1 H Z = 24 • (P1 * Z * P0 + P0 * Z * P2) ∧
    Poly24_neg1 H Z = 24 • (P0 * Z * P1 + P2 * Z * P0) ∧
    Poly24_0    H Z = 24 • (P1 * Z * P1 + P0 * Z * P0 + P2 * Z * P2) ∧
    Poly24_neg2 H Z + Poly24_neg1 H Z + Poly24_0 H Z +
      Poly24_pos1 H Z + Poly24_pos2 H Z = 24 • Z := by
  intro P1 P2 H P0
  have proj_P  : ∀ W : B, P * (P * W) = P * W       := fun W => by rw [← mul_assoc, hP]
  have proj_Q  : ∀ W : B, Q * (Q * W) = Q * W       := fun W => by rw [← mul_assoc, hQ]
  have comm_QP : ∀ W : B, Q * (P * W) = P * (Q * W) := fun W => by rw [← mul_assoc, hPQ, mul_assoc]
  have h1 : P1 * P1 = P1 := by dsimp only [P1]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have h2 : P2 * P2 = P2 := by dsimp only [P2]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have h0 : P0 * P0 = P0 := by dsimp only [P0, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have h12 : P1 * P2 = 0 := by dsimp only [P1, P2]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have h21 : P2 * P1 = 0 := by dsimp only [P1, P2]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hsum : P1 + P0 + P2 = 1 := by dsimp only [P1, P2, P0, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hH_eq : H = P1 - P2 := by dsimp only [H, P1, P2]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hH2_eq : H * H = P1 + P2 := by dsimp only [H, P1, P2]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hH3 : H * (H * H) = H := by dsimp only [H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  set U0   := P1 * Z * P1 + P0 * Z * P0 + P2 * Z * P2
  set Up1  := P1 * Z * P0 + P0 * Z * P2
  set Um1  := P0 * Z * P1 + P2 * Z * P0
  set Up2  := P1 * Z * P2
  set Um2  := P2 * Z * P1
  have hZ_decomp : Z = U0 + Up1 + Um1 + Up2 + Um2 := by
    dsimp only [U0, Up1, Um1, Up2, Um2, P1, P2, P0, H]
    xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hU0 : adH H U0 = 0 := by
    dsimp only [adH, U0, P1, P2, P0, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUp1 : adH H Up1 = Up1 := by
    dsimp only [adH, Up1, P1, P2, P0, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUm1 : adH H Um1 = -Um1 := by
    dsimp only [adH, Um1, P1, P2, P0, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUp2_L : H * Up2 = Up2 := by
    dsimp only [Up2, P1, P2, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUp2_R : Up2 * H = -Up2 := by
    dsimp only [Up2, P1, P2, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUm2_L : H * Um2 = -Um2 := by
    dsimp only [Um2, P1, P2, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hUm2_R : Um2 * H = Um2 := by
    dsimp only [Um2, P1, P2, H]; xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have h_pos2 : Poly24_pos2 H Z = 24 • Up2 := by
    conv_lhs => rw [hZ_decomp]
    rw [Poly24_pos2_add, Poly24_pos2_add, Poly24_pos2_add, Poly24_pos2_add,
        (Poly24_all_on_grade_zero hU0).2.2.2.1,
        (Poly24_all_on_grade_pos1 hUp1).2.2.2.1,
        (Poly24_all_on_grade_neg1 hUm1).2.2.2.1,
        (Poly24_all_on_grade_pos2 hUp2_L hUp2_R).2.2.2.1,
        (Poly24_all_on_grade_neg2 hUm2_L hUm2_R).2.2.2.1]
    abel
  have h_neg2 : Poly24_neg2 H Z = 24 • Um2 := by
    conv_lhs => rw [hZ_decomp]
    rw [Poly24_neg2_add, Poly24_neg2_add, Poly24_neg2_add, Poly24_neg2_add,
        (Poly24_all_on_grade_zero hU0).2.2.2.2,
        (Poly24_all_on_grade_pos1 hUp1).2.2.2.2,
        (Poly24_all_on_grade_neg1 hUm1).2.2.2.2,
        (Poly24_all_on_grade_pos2 hUp2_L hUp2_R).2.2.2.2,
        (Poly24_all_on_grade_neg2 hUm2_L hUm2_R).2.2.2.2]
    abel
  have h_pos1 : Poly24_pos1 H Z = 24 • Up1 := by
    conv_lhs => rw [hZ_decomp]
    rw [Poly24_pos1_add, Poly24_pos1_add, Poly24_pos1_add, Poly24_pos1_add,
        (Poly24_all_on_grade_zero hU0).2.1,
        (Poly24_all_on_grade_pos1 hUp1).2.1,
        (Poly24_all_on_grade_neg1 hUm1).2.1,
        (Poly24_all_on_grade_pos2 hUp2_L hUp2_R).2.1,
        (Poly24_all_on_grade_neg2 hUm2_L hUm2_R).2.1]
    abel
  have h_neg1 : Poly24_neg1 H Z = 24 • Um1 := by
    conv_lhs => rw [hZ_decomp]
    rw [Poly24_neg1_add, Poly24_neg1_add, Poly24_neg1_add, Poly24_neg1_add,
        (Poly24_all_on_grade_zero hU0).2.2.1,
        (Poly24_all_on_grade_pos1 hUp1).2.2.1,
        (Poly24_all_on_grade_neg1 hUm1).2.2.1,
        (Poly24_all_on_grade_pos2 hUp2_L hUp2_R).2.2.1,
        (Poly24_all_on_grade_neg2 hUm2_L hUm2_R).2.2.1]
    abel
  have h_zero : Poly24_0 H Z = 24 • U0 := by
    conv_lhs => rw [hZ_decomp]
    rw [Poly24_0_add, Poly24_0_add, Poly24_0_add, Poly24_0_add,
        (Poly24_all_on_grade_zero hU0).1,
        (Poly24_all_on_grade_pos1 hUp1).1,
        (Poly24_all_on_grade_neg1 hUm1).1,
        (Poly24_all_on_grade_pos2 hUp2_L hUp2_R).1,
        (Poly24_all_on_grade_neg2 hUm2_L hUm2_R).1]
    abel
  refine ⟨h1, h2, h0, h12, h21, hsum, hH_eq, hH2_eq, hH3,
          tripotent_quintic_adH hH3 Z, h_pos2, h_neg2, h_pos1, h_neg1, h_zero, ?_⟩
  · rw [h_neg2, h_neg1, h_zero, h_pos1, h_pos2]
    calc 24 • Um2 + 24 • Um1 + 24 • U0 + 24 • Up1 + 24 • Up2
      _ = 24 • (U0 + Up1 + Um1 + Up2 + Um2) := by abel
      _ = 24 • Z := by rw [← hZ_decomp]

/-! ### Node `ℌ𝔗₃`: Eighth-Order Three-Frontier Synthesis (Commutator Curvature, 5-Graded Climb & Tomita Well) -/

/-- **Frontier 1 (`frontier1_explicit_commutator_metric_spin_and_riemann_curvature`)**:
Explicit polynomial expansion `V = P X² P + X P X - P X P X - X P X P = -[P, X]²`,
tautological Coriolis–Brockett equivalence `2[Σ, Φ] = [[J, Φ], Φ] = [Φ, [Φ, J]]`,
Weitzenböck curvature `[d_+, d_-](Σ) = [J, Φ]² = 4 J⁴ = 4 V²`, and 4th/5th-order
Cotton/centrifugal nested commutator identities `[[Φ, [Φ, J]], Φ] = 8 V Σ` and
`[[J, Φ], [[J, Φ], Φ]] + 4 V [J, [J, Φ]] = 0`. -/
lemma frontier1_explicit_commutator_metric_spin_and_riemann_curvature
    (P X Z : B) (hP : P * P = P) :
    let j  := J_1 P X
    let ph := Phi_1 P X
    let v  := V_1 P X
    let s  := Sigma_1 P X
    v = P * X * X * P + X * P * X - P * X * P * X - X * P * X * P ∧
    v = ph * ph ∧
    2 • s = comm j ph ∧
    anticomm j ph = 0 ∧
    2 • comm s ph = comm (comm j ph) ph ∧
    comm (comm j ph) ph = comm ph (comm ph j) ∧
    d_plus_1 P X (d_minus_1 P X Z) + d_minus_1 P X (d_plus_1 P X Z) = - comm (j * j) Z ∧
    d_plus_1 P X (d_minus_1 P X s) - d_minus_1 P X (d_plus_1 P X s) = comm j ph * comm j ph ∧
    comm j ph * comm j ph = 4 • (j * j * j * j) ∧
    comm j ph * comm j ph = 4 • (v * v) ∧
    comm (comm ph (comm ph j)) ph = 8 • (v * s) ∧
    comm (comm j ph) (comm (comm j ph) ph) + 4 • (v * comm j (comm j ph)) = 0 := by
  intro j ph v s
  have h1 : v = P * X * X * P + X * P * X - P * X * P * X - X * P * X * P := by
    dsimp only [v, V_1, J_1, comm]; peirce_base_nf hP
  have h2s : comm j ph = 2 • s := by
    dsimp only [j, ph, s]; rw [J_1_eq P X, Phi_1_eq hP X, Sigma_1_eq hP X]
    dsimp only [Phi_v, J_mc, Sigma_sp, Q_pos, Q_neg, comm]; amari_peirce_nf hP
  have h_phphj : comm ph (comm ph j) = 4 • (v * j) := by
    dsimp only [j, ph, v]; rw [J_1_eq P X, Phi_1_eq hP X, V_1_eq hP X]
    dsimp only [Phi_v, J_mc, V_met, Q_pos, Q_neg, comm]; amari_peirce_nf hP
  have h_cotton : comm (comm ph (comm ph j)) ph = 8 • (v * s) := by
    rw [h_phphj]
    have h_lin4 : comm (4 • (v * j)) ph = 4 • comm (v * j) ph := by
      have hleft : ∀ n : ℕ, (n • (v * j)) * ph = n • ((v * j) * ph) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [succ_nsmul, add_mul, ih, succ_nsmul]
      have hright : ∀ n : ℕ, ph * (n • (v * j)) = n • (ph * (v * j)) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [succ_nsmul, mul_add, ih, succ_nsmul]
      unfold comm
      rw [hleft, hright]
      abel
    have h_vj_ph : comm (v * j) ph = 2 • (v * s) := by
      dsimp only [j, ph, v, s]; rw [J_1_eq P X, Phi_1_eq hP X, V_1_eq hP X, Sigma_1_eq hP X]
      dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm]; amari_peirce_nf hP
    rw [h_lin4, h_vj_ph]
    abel
  have h_cent5 : comm (comm j ph) (comm (comm j ph) ph) + 4 • (v * comm j (comm j ph)) = 0 := by
    have h_lin : comm (comm j ph) (comm (comm j ph) ph) = 4 • comm s (comm s ph) := by
      rw [h2s]
      unfold comm
      simp only [two_nsmul, add_mul, mul_add, sub_mul, mul_sub]
      abel
    have h4 := (node4_rotating_ball_parabolic_entropy_well_and_dewitt_lock P X X hP).2.2.2.2.2.1
    rw [← J_1_eq P X, ← Phi_1_eq hP X, ← V_1_eq hP X, ← Sigma_1_eq hP X] at h4
    have h_sum4 : 4 • comm s (comm s ph) + 4 • (v * comm j (comm j ph)) =
        4 • (comm s (comm s ph) + v * comm j (comm j ph)) := by abel
    rw [h_lin, h_sum4, h4, smul_zero]
  refine ⟨h1, ?_, h2s.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_cotton, h_cent5⟩ <;>
  · dsimp only [j, ph, v, s, d_plus_1, d_minus_1, chiralConj]
    try rw [N_plus_1_eq hP X]
    try rw [N_minus_1_eq hP X]
    try rw [J_1_eq P X]
    try rw [Phi_1_eq hP X]
    try rw [V_1_eq hP X]
    try rw [Sigma_1_eq hP X]
    try dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm, anticomm]
    amari_peirce_nf hP

/-- Two-bit horizon operators for Frontier 2 (`H = P - Q`). -/
def P1_bit   (P Q : B)   : B := P * (1 - Q)
def P2_bit   (P Q : B)   : B := (1 - P) * Q
def H_bit    (P Q : B)   : B := P - Q
def P_hor2   (P Q : B)   : B := H_bit P Q * H_bit P Q
def P0_bit   (P Q : B)   : B := 1 - P_hor2 P Q
def S_par2   (P Q : B)   : B := P_hor2 P Q + P_hor2 P Q - 1

def Psi_out2 (P Q X : B) : B := P_hor2 P Q * comm (P_hor2 P Q) X
def Psi_in2  (P Q X : B) : B := - (comm (P_hor2 P Q) X * P_hor2 P Q)
def V_PK2    (P Q X : B) : B := anticomm (Psi_out2 P Q X) (Psi_in2 P Q X)

def N_pos1_2 (P Q X : B) : B := P1_bit P Q * X * P0_bit P Q + P0_bit P Q * X * P2_bit P Q
def N_neg1_2 (P Q X : B) : B := P0_bit P Q * X * P1_bit P Q + P2_bit P Q * X * P0_bit P Q
def N_pos2_2 (P Q X : B) : B := N_pos1_2 P Q X * N_pos1_2 P Q X
def N_neg2_2 (P Q X : B) : B := N_neg1_2 P Q X * N_neg1_2 P Q X

def parConj2 (P Q Z : B)   : B := S_par2 P Q * Z * S_par2 P Q
def d_out2   (P Q X Z : B) : B := Psi_out2 P Q X * Z - parConj2 P Q Z * Psi_out2 P Q X
def d_in2    (P Q X Z : B) : B := Psi_in2 P Q X * Z - parConj2 P Q Z * Psi_in2 P Q X
def d_tot2   (P Q X Z : B) : B := d_out2 P Q X Z + d_in2 P Q X Z

/-- **Frontier 2 (`frontier2_nilpotent_differentials_climb_five_graded_maurer_cartan_tower`)**:
For two commuting bits `P² = P`, `Q² = Q`, `Q * P = P * Q` with `H = P - Q`:
1. `Ψ_out² = Ψ_in² = 0` and `d_out²(Z) = d_in²(Z) = 0`.
2. 1st exterior derivative of `H` births grade `±1`: `d_tot(H) = -(N_{+1} - N_{-1})`.
3. 2nd exterior derivative of `H` births grade `±2`: `d_tot²(H) = [V_PK, H] = -2(N_{+2} - N_{-2})`.
4. Unipotent Super-Grassmannian Maurer–Cartan dressing: for `g = 1 + N_{+1}` and
   `g_inv = 1 - N_{+1} + N_{+2}`, `g * g_inv = 1`, `g_inv * g = 1`,
   `θ_H := g_inv * [H, g] = N_{+1} - N_{+2}`, and `g_inv * H * g = H + θ_H`. -/
lemma frontier2_nilpotent_differentials_climb_five_graded_maurer_cartan_tower
    (P Q X Z : B)
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : Q * P = P * Q) :
    let H     := H_bit P Q
    let np1   := N_pos1_2 P Q X
    let nm1   := N_neg1_2 P Q X
    let np2   := N_pos2_2 P Q X
    let nm2   := N_neg2_2 P Q X
    let vPK   := V_PK2 P Q X
    let g     := 1 + np1
    let g_inv := 1 - np1 + np2
    let θ_H   := g_inv * comm H g
    Psi_out2 P Q X * Psi_out2 P Q X = 0 ∧
    Psi_in2 P Q X * Psi_in2 P Q X = 0 ∧
    d_out2 P Q X (d_out2 P Q X Z) = 0 ∧
    d_in2 P Q X (d_in2 P Q X Z) = 0 ∧
    d_tot2 P Q X H = - (np1 - nm1) ∧
    d_tot2 P Q X (d_tot2 P Q X H) = comm vPK H ∧
    d_tot2 P Q X (d_tot2 P Q X H) = - (2 • (np2 - nm2)) ∧
    g * g_inv = 1 ∧
    g_inv * g = 1 ∧
    θ_H = np1 - np2 ∧
    g_inv * H * g = H + θ_H := by
  intro H np1 nm1 np2 nm2 vPK g g_inv θ_H
  have h2bit := two_commuting_bits_xor_xnor_five_graded_24_tower P Q Z hP hQ hPQ
  set P1 := P1_bit P Q
  set P2 := P2_bit P Q
  have h1 : P1 * P1 = P1 := h2bit.1
  have h2 : P2 * P2 = P2 := h2bit.2.1
  have h12 : P1 * P2 = 0 := h2bit.2.2.2.1
  have h21 : P2 * P1 = 0 := h2bit.2.2.2.2.1
  have hH_eq : H = H_weyl P1 P2 := h2bit.2.2.2.2.2.2.1
  have hP_hor_eq : P_hor2 P Q = P_hor3 P1 P2 := h2bit.2.2.2.2.2.2.2.1
  have hP0_eq : P0_bit P Q = P0_waist P1 P2 := by
    dsimp only [P0_bit, P0_waist]; rw [hP_hor_eq]; dsimp only [P_hor3]; abel
  have hP_hor : P_hor2 P Q * P_hor2 P Q = P_hor2 P Q := by
    rw [hP_hor_eq]; exact P_hor3_idem h1 h2 h12 h21
  have h_out_eq : Psi_out2 P Q X = N_plus (P_hor2 P Q) X := N_plus_1_eq hP_hor X
  have h_in_eq  : Psi_in2 P Q X = N_minus (P_hor2 P Q) X := N_minus_1_eq hP_hor X
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  have h_out3 : Psi_out2 P Q X = Psi_out3 P1 P2 X X := by
    rw [h_out_eq, hP_hor_eq, Psi_out3_eq_N_plus h1 h2 h12 h21 X X]
    dsimp only [N_plus, P_hor3]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_in3 : Psi_in2 P Q X = Psi_in3 P1 P2 X X := by
    rw [h_in_eq, hP_hor_eq, Psi_in3_eq_N_minus h1 h2 h12 h21 X X]
    dsimp only [N_minus, P_hor3]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_vPK3 : vPK = V_PK3 P1 P2 X X := by
    dsimp only [vPK, V_PK2, V_PK3]; rw [h_out3, h_in3]
  have h_np1_eq : N_pos1_2 P Q X = N_pos1_3 P1 P2 X := by
    dsimp only [N_pos1_2, N_pos1_3]; rw [hP0_eq]
  have h_nm1_eq : N_neg1_2 P Q X = N_neg1_3 P1 P2 X := by
    dsimp only [N_neg1_2, N_neg1_3]; rw [hP0_eq]
  have h_dtot : ∀ W : B, d_tot2 P Q X W = d_sum (P_hor2 P Q) X X W := fun W => by
    dsimp only [d_tot2, d_out2, d_in2, parConj2, S_par2, d_sum, d_plus, d_minus, chiralConj, S_P]
    rw [h_out_eq, h_in_eq]
  have h_dtot_sq : d_tot2 P Q X (d_tot2 P Q X H) = comm vPK H := by
    rw [h_dtot (d_tot2 P Q X H), h_dtot H]
    have h_lap := (parakahler_sum_and_difference_of_exterior_connections (P_hor2 P Q) X X H hP_hor).2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [h_lap]
    dsimp only [vPK, V_PK2, V_met, Q_pos, Q_neg, anticomm]
    rw [h_out_eq, h_in_eq]
  have h_dtot_H : d_tot2 P Q X H = - (np1 - nm1) := by
    have h_Spar_H : parConj2 P Q H = H := by
      dsimp only [parConj2, S_par2]; rw [hP_hor_eq, hH_eq]
      dsimp only [P_hor3, H_weyl]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
    have h_w1 := dual_weyl_and_parakahler_partition_of_odd_vielbein P1 P2 X X h1 h2 h12 h21
    dsimp only [d_tot2, d_out2, d_in2, np1, nm1]
    rw [h_Spar_H, h_out3, h_in3, hH_eq, h_np1_eq, h_nm1_eq]
    have h_comm_ph : Psi_out3 P1 P2 X X * H_weyl P1 P2 - H_weyl P1 P2 * Psi_out3 P1 P2 X X +
        (Psi_in3 P1 P2 X X * H_weyl P1 P2 - H_weyl P1 P2 * Psi_in3 P1 P2 X X) =
        - comm (H_weyl P1 P2) (Phi_odd3 P1 P2 X X) := by
      dsimp only [Phi_odd3, comm]; noncomm_ring
    rw [h_comm_ph, h_w1.2.2.2.2.2.2.1]
    dsimp only [J_Weyl3]
  have h_w2 := fundamental_weyl_to_parakahler_metric_bridge P1 P2 X X h1 h2 h12 h21
  have h_vPK_eq : vPK = V1_weyl3 P1 P2 X X + np2 + nm2 := by
    rw [h_vPK3]
    dsimp only [np2, nm2, N_pos2_2, N_neg2_2]
    rw [h_np1_eq, h_nm1_eq]
    exact h_w2.1
  have h7 := node7_log_radial_modular_time_and_five_graded_weyl_invariance P1 P2 X X h1 h2 h12 h21
  have h_v1_0 : comm H (V1_weyl3 P1 P2 X X) = 0 := by rw [hH_eq]; exact h7.2.2.2.2.2.2.2.2.1
  have h_np1_comm : comm H np1 = np1 := by
    dsimp only [np1]; rw [hH_eq, h_np1_eq]; exact h7.2.2.2.2.1
  have h_np2_comm : comm H np2 = 2 • np2 := by
    dsimp only [np2, N_pos2_2]; rw [hH_eq, h_np1_eq]; exact h7.2.2.2.2.2.2.1
  have h_nm2_comm : comm H nm2 = - (2 • nm2) := by
    dsimp only [nm2, N_neg2_2]; rw [hH_eq, h_nm1_eq]; exact h7.2.2.2.2.2.2.2.1
  have h_np3_0 : np1 * (np1 * np1) = 0 := by
    dsimp only [np1]; rw [h_np1_eq]
    dsimp only [N_pos1_3, P0_waist]; parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_np3_0' : (np1 * np1) * np1 = 0 := by
    rw [mul_assoc]; exact h_np3_0
  have h_comm_vPK_H : comm vPK H = - (2 • (np2 - nm2)) := by
    have h_skew : comm vPK H = - comm H vPK := by unfold comm; abel
    rw [h_skew, h_vPK_eq, comm_add_right, comm_add_right, h_v1_0, h_np2_comm, h_nm2_comm]
    abel
  have h_g_r : g * g_inv = 1 := by
    dsimp only [g, g_inv, np2, N_pos2_2]
    change (1 + np1) * (1 - np1 + np1 * np1) = 1
    calc (1 + np1) * (1 - np1 + np1 * np1)
      _ = 1 + np1 * (np1 * np1) := by noncomm_ring
      _ = 1 := by rw [h_np3_0, add_zero]
  have h_g_l : g_inv * g = 1 := by
    dsimp only [g, g_inv, np2, N_pos2_2]
    change (1 - np1 + np1 * np1) * (1 + np1) = 1
    calc (1 - np1 + np1 * np1) * (1 + np1)
      _ = 1 + (np1 * np1) * np1 := by noncomm_ring
      _ = 1 := by rw [h_np3_0', add_zero]
  have h_comm_Hg : comm H g = np1 := by
    dsimp only [g]
    have h_c1 : comm H (1 + np1) = comm H np1 := by unfold comm; noncomm_ring
    rw [h_c1, h_np1_comm]
  have h_theta : θ_H = np1 - np2 := by
    dsimp only [θ_H]; rw [h_comm_Hg]
    dsimp only [g_inv, np2, N_pos2_2]
    change (1 - np1 + np1 * np1) * np1 = np1 - np1 * np1
    calc (1 - np1 + np1 * np1) * np1
      _ = np1 - np1 * np1 + (np1 * np1) * np1 := by noncomm_ring
      _ = np1 - np1 * np1 := by rw [h_np3_0', add_zero]
  refine ⟨?_, ?_, ?_, ?_, h_dtot_H, h_dtot_sq, ?_, h_g_r, h_g_l, h_theta, ?_⟩
  · rw [h_out_eq]; exact N_plus_sq hP_hor X
  · rw [h_in_eq]; exact N_minus_sq hP_hor X
  · dsimp only [d_out2, parConj2, S_par2]; rw [h_out_eq]
    change d_plus (P_hor2 P Q) X (d_plus (P_hor2 P Q) X Z) = 0
    dsimp only [d_plus, chiralConj]; amari_peirce_nf hP_hor
  · dsimp only [d_in2, parConj2, S_par2]; rw [h_in_eq]
    change d_minus (P_hor2 P Q) X (d_minus (P_hor2 P Q) X Z) = 0
    dsimp only [d_minus, chiralConj]; amari_peirce_nf hP_hor
  · rw [h_dtot_sq, h_comm_vPK_H]
  · dsimp only [θ_H]
    calc g_inv * H * g
      _ = (g_inv * g) * H + g_inv * (H * g - g * H) := by noncomm_ring
      _ = H + g_inv * comm H g := by rw [h_g_l, one_mul]; rfl

/-- Modular Laplacian `modLapl(K, Z) = δ_K(δ_K(Z))`. -/
def modLapl (K Z : B) : B := modularDeriv K (modularDeriv K Z)

/-- **Frontier 3 (`frontier3_tomita_takesaki_modular_laplacian_parabolic_well_bridge`)**:
Twin-bimodule Tomita–Takesaki modular Laplacian `δ_K²(Φ) = L_{K²}(Φ) + R_{K²}(Φ) - 2 C_K(Φ)`
evaluated at `K = J` (`V δ_J²(Φ) = -4 V² Φ`) and `K = Σ` (`δ_Σ²(Φ) = +4 V² Φ`), proving
exact twin-vacuum and modular Laplacian cancellation `C_Σ(Φ) + V C_J(Φ) = 0` and
`δ_Σ²(Φ) + V δ_J²(Φ) = 0`. -/
lemma frontier3_tomita_takesaki_modular_laplacian_parabolic_well_bridge
    (P X K : B) (hP : P * P = P) :
    let j  := J_1 P X
    let ph := Phi_1 P X
    let v  := V_1 P X
    let s  := Sigma_1 P X
    modLapl K ph = leftMul (K * K) ph + rightMul (K * K) ph - 2 • twinCrossCorrelation K ph ∧
    leftMul (j * j) ph  = - (v * ph) ∧
    rightMul (j * j) ph = - (v * ph) ∧
    twinCrossCorrelation j ph = v * ph ∧
    v * modLapl j ph    = - (4 • (v * v * ph)) ∧
    leftMul (s * s) ph  = v * v * ph ∧
    rightMul (s * s) ph = v * v * ph ∧
    twinCrossCorrelation s ph = - (v * v * ph) ∧
    modLapl s ph        = 4 • (v * v * ph) ∧
    twinCrossCorrelation s ph + v * twinCrossCorrelation j ph = 0 ∧
    modLapl s ph + v * modLapl j ph = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [modLapl, modularDeriv, leftMul, rightMul, twinCrossCorrelation]
    simp only [sub_mul, mul_sub, mul_assoc]; abel
  all_goals
    dsimp only [modLapl, modularDeriv, leftMul, rightMul, twinCrossCorrelation]
    try rw [J_1_eq P X]
    try rw [Phi_1_eq hP X]
    try rw [V_1_eq hP X]
    try rw [Sigma_1_eq hP X]
    dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg]
    amari_peirce_nf hP

/-! ### Node `ℌ𝔗₄`: Named Historical Physics Operator Dictionary (`𝔉𝔓₁..𝔉𝔓₁₀`) -/

/-- `𝔉𝔓₁`: Cartan–Eddington selective involution `S_Eddington(P) = 2P - 1`. -/
def S_Eddington     (P : B)   : B := P + P - 1
/-- `𝔉𝔓₁`: Secular even operator part `X_even = P X P + (1 - P) X (1 - P)`. -/
def X_secular_even  (P X : B) : B := P * X * P + (1 - P) * X * (1 - P)
/-- `𝔉𝔓₂`: Schrödinger *Zitterbewegung* odd amplitude `ξ = P X (1 - P) + (1 - P) X P`. -/
def xi_zitter_odd   (P X : B) : B := P * X * (1 - P) + (1 - P) * X * P
/-- `𝔉𝔓₂`: Schrödinger *Zitterbewegung* velocity `v_Z = [P, X]`. -/
def v_zitter        (P X : B) : B := comm P X
/-- `𝔉𝔓₃`: Fock–Ivanenko operator line element `ds = [P, [P, X]]`. -/
def ds_FockIvanenko (P X : B) : B := comm P (comm P X)
/-- `𝔉𝔓₄`: Newman–Penrose outgoing null ray `l = P[P, X]`. -/
def l_NP            (P X : B) : B := P * comm P X
/-- `𝔉𝔓₄`: Newman–Penrose ingoing null ray `n = -[P, X]P`. -/
def n_NP            (P X : B) : B := - (comm P X * P)
/-- `𝔉𝔓₄`: Jordan `r`-number metric `V_Jordan = {l, n}`. -/
def V_Jordan        (P X : B) : B := anticomm (l_NP P X) (n_NP P X)
/-- `𝔉𝔓₄`: Fock spin bivector `Σ_Fock = [l, n]`. -/
def Sigma_Fock      (P X : B) : B := comm (l_NP P X) (n_NP P X)
/-- `𝔉𝔓₅`: De Broglie–Madelung osmotic velocity `u_osm = -[ds, [ds, v_Z]]`. -/
def u_osmotic       (P X : B) : B := - comm (ds_FockIvanenko P X) (comm (ds_FockIvanenko P X) (v_zitter P X))
/-- `𝔉𝔓₅`: Rotational Coriolis velocity `v_coriolis = 2[Σ_Fock, ds]`. -/
def v_coriolis      (P X : B) : B := 2 • comm (Sigma_Fock P X) (ds_FockIvanenko P X)
/-- `𝔉𝔓₅`: Bohm quantum-potential centrifugal acceleration `a_Bohm = [Σ_Fock, [Σ_Fock, ds]]`. -/
def a_Bohm_cent     (P X : B) : B := comm (Sigma_Fock P X) (comm (Sigma_Fock P X) (ds_FockIvanenko P X))
/-- `𝔉𝔓₅`: Sakharov gravitational well restoration `a_Well = V_Jordan [v_Z, [v_Z, ds]]`. -/
def a_Sakharov_well (P X : B) : B := V_Jordan P X * comm (v_zitter P X) (comm (v_zitter P X) (ds_FockIvanenko P X))
/-- `𝔉𝔓₆`: Kähler forward inner differential `d_Kahler_l`. -/
def d_Kahler_l      (P X Z : B) : B := l_NP P X * Z - chiralConj P Z * l_NP P X
/-- `𝔉𝔓₆`: Kähler backward inner differential `d_Kahler_n`. -/
def d_Kahler_n      (P X Z : B) : B := n_NP P X * Z - chiralConj P Z * n_NP P X
/-- `𝔉𝔓₇`: Sakharov–Tomita twin-vacuum correlation `C_K(Z) = K * Z * K`. -/
def twinVacuumCorr  (K Z : B) : B := K * Z * K
/-- `𝔉𝔓₈`: Foldy–Wouthuysen / Schwinger Bruhat gauges and degree-3 decoupled projectors. -/
def G_FW_plus       (P X : B) : B := (1 - l_NP P X) * (1 + n_NP P X)
def G_FW_plus_inv   (P X : B) : B := (1 - n_NP P X) * (1 + l_NP P X)
def G_FW_minus      (P X : B) : B := (1 + n_NP P X) * (1 - l_NP P X)
def G_FW_minus_inv  (P X : B) : B := (1 + l_NP P X) * (1 - n_NP P X)
def P_FW_plus       (P X : B) : B :=
  P + ds_FockIvanenko P X - Sigma_Fock P X + P * (v_zitter P X * v_zitter P X * v_zitter P X)
def P_FW_minus      (P X : B) : B :=
  P + ds_FockIvanenko P X - Sigma_Fock P X - (v_zitter P X * v_zitter P X * v_zitter P X) * P
def S_FW_plus       (P X : B) : B := P_FW_plus P X + P_FW_plus P X - 1
def S_FW_minus      (P X : B) : B := P_FW_minus P X + P_FW_minus P X - 1

/-- **Theorem 1 (`𝔉𝔓₁–𝔉𝔓₅` — Cartan, Eddington, Schrödinger, Fock–Ivanenko, Jordan, NP & de Broglie)**:
Formalizes the exact operator identities of `𝔉𝔓₁..𝔉𝔓₅`. -/
lemma archetypes_FP1_to_FP5_zitterbewegung_fock_jordan_debroglie
    (P X : B) (hP : P * P = P) :
    let sp  := S_Eddington P
    let xev := X_secular_even P X
    let xi  := xi_zitter_odd P X
    let vz  := v_zitter P X
    let ds  := ds_FockIvanenko P X
    let l   := l_NP P X
    let n   := n_NP P X
    let v   := V_Jordan P X
    let s   := Sigma_Fock P X
    xev + xi = X ∧ comm P xev = 0 ∧ sp * sp = 1 ∧
    xi = ds ∧ comm P xi = vz ∧ comm P vz = xi ∧ comm vz xi = 2 • s ∧
    ds * ds = v ∧ vz * vz = - v ∧ anticomm vz ds = 0 ∧
    l * l = 0 ∧ n * n = 0 ∧ l + n = ds ∧ l - n = vz ∧
    comm P l = l ∧ comm P n = - n ∧ comm P v = 0 ∧ comm P s = 0 ∧
    s = sp * v ∧ s * s = v * v ∧
    u_osmotic P X + v_coriolis P X = 0 ∧
    a_Bohm_cent P X + a_Sakharov_well P X = 0 := by
  have hl : l_NP P X = N_plus P X := N_plus_1_eq hP X
  have hn : n_NP P X = N_minus P X := N_minus_1_eq hP X
  have hvz : v_zitter P X = J_mc P X X := J_1_eq P X
  have hds : ds_FockIvanenko P X = Phi_v P X X := Phi_1_eq hP X
  have hxi : xi_zitter_odd P X = Phi_v P X X := rfl
  refine ⟨?_, ?_, S_P_sq hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [X_secular_even, xi_zitter_odd]; peirce_base_nf hP
  · dsimp only [X_secular_even, comm]; peirce_base_nf hP
  · rw [hxi, hds]
  all_goals
    try dsimp only [S_Eddington, V_Jordan, Sigma_Fock,
                    u_osmotic, v_coriolis, a_Bohm_cent, a_Sakharov_well]
    try rw [hl]
    try rw [hn]
    try rw [hvz]
    try rw [hds]
    try rw [hxi]
    try dsimp only [Phi_v, J_mc, comm, anticomm]
    amari_peirce_nf hP

/-- **Theorem 2 (`𝔉𝔓₆–𝔉𝔓₈` — Kähler Calculus, `1:1:2` Sakharov Partition & Degree-3 Foldy–Wouthuysen)**:
Formalizes the Kähler inner differential calculus, the `1 : 1 : 2` Tomita–Sakharov partition of
the centrifugal force, and the degree-3 Foldy–Wouthuysen decoupling `P_FW_±² = P_FW_±`. -/
lemma archetypes_FP6_to_FP8_kahler_sakharov_1_1_2_and_foldy_wouthuysen
    (P X Z : B) (hP : P * P = P) :
    let vz  := v_zitter P X
    let ds  := ds_FockIvanenko P X
    let n   := n_NP P X
    let v   := V_Jordan P X
    let s   := Sigma_Fock P X
    let Gp  := G_FW_plus P X
    let GpI := G_FW_plus_inv P X
    let Pp  := P_FW_plus P X
    let Pm  := P_FW_minus P X
    d_Kahler_l P X (d_Kahler_l P X Z) = 0 ∧
    d_Kahler_n P X (d_Kahler_n P X Z) = 0 ∧
    d_Kahler_l P X n = v ∧
    d_Kahler_l P X (d_Kahler_n P X Z) + d_Kahler_n P X (d_Kahler_l P X Z) = comm v Z ∧
    d_Kahler_l P X (d_Kahler_n P X s) - d_Kahler_n P X (d_Kahler_l P X s) = 4 • (v * v) ∧
    (s * s) * ds = (v * v) * ds ∧
    ds * (s * s) = (v * v) * ds ∧
    (- (2 • twinVacuumCorr s ds) : B) = 2 • ((v * v) * ds) ∧
    (s * s) * ds + ds * (s * s) - 2 • twinVacuumCorr s ds = a_Bohm_cent P X ∧
    twinVacuumCorr s ds + v * twinVacuumCorr vz ds = 0 ∧
    Gp * GpI = 1 ∧
    Gp * P * GpI = Pp ∧
    Pp * Pp = Pp ∧ Pm * Pm = Pm ∧
    Pm - Pp = - (vz * vz * vz) ∧
    comm P Pp = vz + P * (vz * vz * vz) ∧
    comm P Pm = vz + (vz * vz * vz) * P ∧
    comm P Pm - comm P Pp = v * ds := by
  have hl : l_NP P X = N_plus P X := N_plus_1_eq hP X
  have hn : n_NP P X = N_minus P X := N_minus_1_eq hP X
  have hvz : v_zitter P X = J_mc P X X := J_1_eq P X
  have hds : ds_FockIvanenko P X = Phi_v P X X := Phi_1_eq hP X
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · try dsimp only [G_FW_plus, G_FW_plus_inv, P_FW_plus, P_FW_minus,
                    d_Kahler_l, d_Kahler_n, chiralConj,
                    twinVacuumCorr, a_Bohm_cent, V_Jordan, Sigma_Fock]
    try rw [hl]
    try rw [hn]
    try rw [hvz]
    try rw [hds]
    try dsimp only [Phi_v, J_mc, comm, anticomm]
    amari_peirce_nf hP

/-- **Inverse Foldy–Wouthuysen Decoupling & Metric Gauge Invariance (`foldy_wouthuysen_inverse_decoupling_and_metric_gauge_invariance`)**:
`G_±⁻¹ P_FW_± G_± = P`, `[G_±, V] = 0`, `G_± V G_±⁻¹ = V`, and `G_± Σ G_±⁻¹ = V S_FW_±`. -/
lemma foldy_wouthuysen_inverse_decoupling_and_metric_gauge_invariance
    (P X : B) (hP : P * P = P) :
    let v   := V_Jordan P X
    let s   := Sigma_Fock P X
    let Gp  := G_FW_plus P X
    let GpI := G_FW_plus_inv P X
    let Gm  := G_FW_minus P X
    let GmI := G_FW_minus_inv P X
    let Pp  := P_FW_plus P X
    let Pm  := P_FW_minus P X
    let Sp  := S_FW_plus P X
    let Sm  := S_FW_minus P X
    GpI * Pp * Gp = P ∧
    GmI * Pm * Gm = P ∧
    comm Gp v = 0 ∧
    comm Gm v = 0 ∧
    Gp * v * GpI = v ∧
    Gm * v * GmI = v ∧
    Gp * s * GpI = v * Sp ∧
    Gm * s * GmI = v * Sm ∧
    (Gp * s * GpI) * (Gp * s * GpI) = v * v := by
  have hl : l_NP P X = N_plus P X := N_plus_1_eq hP X
  have hn : n_NP P X = N_minus P X := N_minus_1_eq hP X
  have hvz : v_zitter P X = J_mc P X X := J_1_eq P X
  have hds : ds_FockIvanenko P X = Phi_v P X X := Phi_1_eq hP X
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [G_FW_plus, G_FW_plus_inv, G_FW_minus, G_FW_minus_inv,
                P_FW_plus, P_FW_minus, S_FW_plus, S_FW_minus, V_Jordan, Sigma_Fock]
    rw [hl, hn]
    try rw [hvz]
    try rw [hds]
    dsimp only [Phi_v, J_mc, comm, anticomm]
    amari_peirce_nf hP

/-- **Universal `1 : 1 : 2` Tomita–Sakharov Partition of All Three Forces (`universal_1_1_2_tomita_sakharov_partition_of_all_three_forces`)**:
Proves that the 1st-order de Broglie osmotic force `u_osm`, the 2nd-order Bohm centrifugal force
`a_Bohm`, and the 2nd-order Sakharov gravity well `a_Well` all decompose in the exact `1 : 1 : 2`
ratio between Left (`1/4`), Right (`1/4`), and Twin-Vacuum (`1/2`) correlations. -/
lemma universal_1_1_2_tomita_sakharov_partition_of_all_three_forces
    (P X : B) (hP : P * P = P) :
    let vz := v_zitter P X
    let ds := ds_FockIvanenko P X
    let v  := V_Jordan P X
    let s  := Sigma_Fock P X;
    - ((ds * ds) * vz) = - (v * vz) ∧
    - (vz * (ds * ds)) = - (v * vz) ∧
    (2 • twinVacuumCorr ds vz : B) = - (2 • (v * vz)) ∧
    - ((ds * ds) * vz) - (vz * (ds * ds)) + 2 • twinVacuumCorr ds vz = u_osmotic P X ∧
    (s * s) * ds = (v * v) * ds ∧
    ds * (s * s) = (v * v) * ds ∧
    (- (2 • twinVacuumCorr s ds) : B) = 2 • ((v * v) * ds) ∧
    (s * s) * ds + ds * (s * s) - 2 • twinVacuumCorr s ds = a_Bohm_cent P X ∧
    v * ((vz * vz) * ds) = - ((v * v) * ds) ∧
    v * (ds * (vz * vz)) = - ((v * v) * ds) ∧
    (- (2 • (v * twinVacuumCorr vz ds)) : B) = - (2 • ((v * v) * ds)) ∧
    v * ((vz * vz) * ds) + v * (ds * (vz * vz)) - 2 • (v * twinVacuumCorr vz ds) = a_Sakharov_well P X := by
  have hl : l_NP P X = N_plus P X := N_plus_1_eq hP X
  have hn : n_NP P X = N_minus P X := N_minus_1_eq hP X
  have hvz : v_zitter P X = J_mc P X X := J_1_eq P X
  have hds : ds_FockIvanenko P X = Phi_v P X X := Phi_1_eq hP X
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [u_osmotic, a_Bohm_cent, a_Sakharov_well, twinVacuumCorr, V_Jordan, Sigma_Fock]
    try rw [hl]
    try rw [hn]
    try rw [hvz]
    try rw [hds]
    dsimp only [Phi_v, J_mc, comm, anticomm]
    amari_peirce_nf hP

/-- **Born–Nomizu Product Flip & Complete 5-Graded Spectrum of `V_XOR` (`born_nomizu_full_product_flip_and_finkelstein_complete_xor_spectrum`)**:
1. Born reciprocity `S_Eddington * ds_X = v_ZX`, `ds_X * ds_Y = -(v_ZX * v_ZY)`, `v_ZX * ds_Y + ds_X * v_ZY = 0`,
   Nomizu 1st Bianchi identity, and osmotic reduction `NomizuRiemann P X v_ZX ds_X = -u_osmotic P X`.
2. Complete 5-graded spectral resolution of `V_XOR = d_Kahler_l P_hor X (n_NP P_hor X)` under `H = P - Q`:
   `Poly24_pos1 H V_XOR = 0`, `Poly24_neg1 H V_XOR = 0`, `Poly24_pos2 H V_XOR = 24 • (P₁ X P₀ X P₂)`,
   `Poly24_neg2 H V_XOR = 24 • (P₂ X P₀ X P₁)`,
   `Poly24_0 H V_XOR = 24 • (P₁ X P₀ X P₁ + P₂ X P₀ X P₂ + P₀ X (P₁ + P₂) X P₀)`, and
   `Poly24_neg2 H V_XOR + Poly24_0 H V_XOR + Poly24_pos2 H V_XOR = 24 • V_XOR`. -/
lemma born_nomizu_full_product_flip_and_finkelstein_complete_xor_spectrum
    (P Q X Y Z : B)
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : Q * P = P * Q) :
    let sp    := S_Eddington P
    let vzX   := v_zitter P X
    let vzY   := v_zitter P Y
    let dsX   := ds_FockIvanenko P X
    let dsY   := ds_FockIvanenko P Y
    let dsZ   := ds_FockIvanenko P Z
    let P1    := P * (1 - Q)
    let P2    := (1 - P) * Q
    let H     := P - Q
    let P_hor := H * H
    let P0    := 1 - P_hor
    let V_XOR := d_Kahler_l P_hor X (n_NP P_hor X)
    sp * dsX = vzX ∧
    sp * vzX = dsX ∧
    dsX * dsY = - (vzX * vzY) ∧
    vzX * dsY + dsX * vzY = 0 ∧
    comm dsX dsY = - comm vzX vzY ∧
    NomizuRiemann P X Y dsZ + NomizuRiemann P Y Z dsX + NomizuRiemann P Z X dsY = 0 ∧
    NomizuRiemann P X vzX dsX = - u_osmotic P X ∧
    Poly24_pos1 H V_XOR = 0 ∧
    Poly24_neg1 H V_XOR = 0 ∧
    Poly24_pos2 H V_XOR = 24 • (P1 * X * P0 * X * P2) ∧
    Poly24_neg2 H V_XOR = 24 • (P2 * X * P0 * X * P1) ∧
    Poly24_0    H V_XOR = 24 • (P1 * X * P0 * X * P1 + P2 * X * P0 * X * P2 +
                                P0 * X * (P1 + P2) * X * P0) ∧
    Poly24_neg2 H V_XOR + Poly24_0 H V_XOR + Poly24_pos2 H V_XOR = 24 • V_XOR := by
  intro sp vzX vzY dsX dsY dsZ P1 P2 H P_hor P0 V_XOR
  have hbn := peirce_schrodinger_nomizu_narasimhan_ramanan_synthesis P X Y Z hP
  have h2bit := two_commuting_bits_xor_xnor_five_graded_24_tower P Q V_XOR hP hQ hPQ
  have hP_hor : P_hor * P_hor = P_hor := by
    dsimp only [P_hor, H]
    have proj_P  : ∀ W : B, P * (P * W) = P * W       := fun W => by rw [← mul_assoc, hP]
    have proj_Q  : ∀ W : B, Q * (Q * W) = Q * W       := fun W => by rw [← mul_assoc, hQ]
    have comm_QP : ∀ W : B, Q * (P * W) = P * (Q * W) := fun W => by rw [← mul_assoc, hPQ, mul_assoc]
    xor_idem_nf hP hQ hPQ proj_P proj_Q comm_QP
  have hP_hor' : ∀ W : B, P_hor * (P_hor * W) = P_hor * W := fun W => by rw [← mul_assoc, hP_hor]
  have hP0_idem : P0 * P0 = P0 := h2bit.2.2.1
  have hP0' : ∀ W : B, P0 * (P0 * W) = P0 * W := fun W => by rw [← mul_assoc, hP0_idem]
  have hP_hor_eq : P_hor = P1 + P2 := h2bit.2.2.2.2.2.2.2.1
  have h_VXOR_V : V_XOR = V_met P_hor X X := by
    dsimp only [V_XOR, d_Kahler_l]
    have hl : l_NP P_hor X = N_plus P_hor X := N_plus_1_eq hP_hor X
    have hn : n_NP P_hor X = N_minus P_hor X := N_minus_1_eq hP_hor X
    rw [hl, hn]
    exact (node6_quotiented_exterior_calculus_amari_alpha_and_bruhat_cure
      P_hor X X 0 X X X hP_hor (fun _ => by simp)).2.2.2.1
  have hV_step1 : V_met P_hor X X = P_hor * X * P0 * X * P_hor + P0 * X * (P1 + P2) * X * P0 := by
    dsimp only [V_met, Q_pos, Q_neg, N_plus, N_minus]
    change P_hor * X * P0 * (P0 * X * P_hor) + P0 * X * P_hor * (P_hor * X * P0) = _
    simp only [mul_assoc, hP0', hP_hor']
    rw [← hP_hor_eq]
  have h1 : P1 * P1 = P1 := h2bit.1
  have h2 : P2 * P2 = P2 := h2bit.2.1
  have h12 : P1 * P2 = 0 := h2bit.2.2.2.1
  have h21 : P2 * P1 = 0 := h2bit.2.2.2.2.1
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  have hP0_waist : P0 = 1 - P1 - P2 := by
    dsimp only [P0]; rw [hP_hor_eq]; abel
  have h_pos1_0 : P1 * V_XOR * P0 + P0 * V_XOR * P2 = 0 := by
    rw [h_VXOR_V, hV_step1, hP_hor_eq, hP0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_neg1_0 : P0 * V_XOR * P1 + P2 * V_XOR * P0 = 0 := by
    rw [h_VXOR_V, hV_step1, hP_hor_eq, hP0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_pos2_eq : P1 * V_XOR * P2 = P1 * X * P0 * X * P2 := by
    rw [h_VXOR_V, hV_step1, hP_hor_eq, hP0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_neg2_eq : P2 * V_XOR * P1 = P2 * X * P0 * X * P1 := by
    rw [h_VXOR_V, hV_step1, hP_hor_eq, hP0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_0_eq : P1 * V_XOR * P1 + P0 * V_XOR * P0 + P2 * V_XOR * P2 =
      P1 * X * P0 * X * P1 + P2 * X * P0 * X * P2 + P0 * X * (P1 + P2) * X * P0 := by
    rw [h_VXOR_V, hV_step1, hP_hor_eq, hP0_waist]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h_p1 : Poly24_pos1 H V_XOR = 0 := by
    rw [h2bit.2.2.2.2.2.2.2.2.2.2.2.2.1, h_pos1_0, smul_zero]
  have h_m1 : Poly24_neg1 H V_XOR = 0 := by
    rw [h2bit.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h_neg1_0, smul_zero]
  have h_p2 : Poly24_pos2 H V_XOR = 24 • (P1 * X * P0 * X * P2) := by
    rw [h2bit.2.2.2.2.2.2.2.2.2.2.1, h_pos2_eq]
  have h_m2 : Poly24_neg2 H V_XOR = 24 • (P2 * X * P0 * X * P1) := by
    rw [h2bit.2.2.2.2.2.2.2.2.2.2.2.1, h_neg2_eq]
  have h_0 : Poly24_0 H V_XOR =
      24 • (P1 * X * P0 * X * P1 + P2 * X * P0 * X * P2 + P0 * X * (P1 + P2) * X * P0) := by
    rw [h2bit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h_0_eq]
  have h_sum24 : Poly24_neg2 H V_XOR + Poly24_0 H V_XOR + Poly24_pos2 H V_XOR = 24 • V_XOR := by
    have h_tot := h2bit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [h_p1, h_m1] at h_tot
    simpa only [add_zero] using h_tot
  refine ⟨hbn.2.2.2.2.1, hbn.2.2.2.2.2.1, hbn.2.2.2.2.2.2.2.2.2.1,
          hbn.2.2.2.2.2.2.2.2.2.2.1, hbn.2.2.2.2.2.2.2.2.2.2.2.1,
          hbn.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          ?_, h_p1, h_m1, h_p2, h_m2, h_0, h_sum24⟩
  · dsimp only [NomizuRiemann, u_osmotic, dsX, vzX, ds_FockIvanenko, v_zitter, Phi_1, comm]
    peirce_base_nf hP

/-! ### Node `ℌ𝔗₅`: Two Chiral Faces of Reality & Decadic Polynomial Generating Ladders -/

/-- **Quantum Mechanics & Gravity as Two Chiral Faces (`quantum_and_gravity_are_two_faces_of_one_operator_reality`)**:
Inside `P`, Quantum `(J, Σ)` and Gravity `(Φ, V)` are identical (`P J = P Φ = N_+`, `P Σ = P V = Q_+`);
outside `1 - P`, they are exact opposites (`(1 - P) J = -(1 - P) Φ = -N_-`, `(1 - P) Σ = -(1 - P) V = -Q_-`);
and they are interlocked by `S_P = 2P - 1`, squaring, commutation, exterior differentiation, and
the Unruh horizon identity `V - 2 V P = -Σ`. -/
lemma quantum_and_gravity_are_two_faces_of_one_operator_reality
    (P X Y Z : B) (hP : P * P = P) :
    let sp := S_P P
    let j  := J_1 P X
    let ph := Phi_1 P X
    let np := N_plus_1 P X
    let nm := N_minus_1 P X
    let qp := Q_pos_1 P X
    let qm := Q_neg_1 P X
    let v  := V_1 P X
    let s  := Sigma_1 P X
    P * j = P * ph ∧ P * j = np ∧
    (1 - P) * j = - ((1 - P) * ph) ∧ (1 - P) * ph = nm ∧
    P * s = P * v ∧ P * s = qp ∧
    (1 - P) * s = - ((1 - P) * v) ∧ (1 - P) * v = qm ∧
    ph = np + nm ∧ j = np - nm ∧
    v  = qp + qm ∧ s = qp - qm ∧
    j  = sp * ph ∧ ph = sp * j ∧
    s  = sp * v  ∧ v  = sp * s ∧
    ph * ph = v ∧ j * j = - v ∧ s * s = v * v ∧
    Phi_1 P X * Phi_1 P Y = - (J_1 P X * J_1 P Y) ∧
    comm (Phi_1 P X) (Phi_1 P Y) = - comm (J_1 P X) (J_1 P Y) ∧
    d_plus_1 P X nm = v ∧ d_minus_1 P X np = v ∧
    d_plus_1 P X (d_minus_1 P X Z) + d_minus_1 P X (d_plus_1 P X Z) = comm v Z ∧
    - comm ph (comm ph j) + 2 • comm s ph = 0 ∧
    comm s (comm s ph) + v * comm j (comm j ph) = 0 ∧
    v - 2 • (v * P) = - s := by
  have hbn := peirce_schrodinger_nomizu_narasimhan_ramanan_synthesis P X Y Z hP
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          hbn.2.2.2.2.2.2.2.2.2.1, hbn.2.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · try dsimp only [Q_pos_1, Q_neg_1, d_plus_1, d_minus_1, chiralConj]
    try rw [N_plus_1_eq hP X]
    try rw [N_minus_1_eq hP X]
    try rw [J_1_eq P X]
    try rw [Phi_1_eq hP X]
    try rw [V_1_eq hP X]
    try rw [Sigma_1_eq hP X]
    try dsimp only [Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm]
    amari_peirce_nf hP

/-- **Telescoping Polynomial Identities & Unruh Degree-5 Equilibrium (`telescoping_polynomial_ladders_and_unruh_well`)**:
These are polynomial equalities; no inverse or convergence statement is included.
1. Even metric-curvature generating sum: `1 - J² + J⁴ = 1 + V + V²` and
   `(1 + J²)(1 - J² + J⁴) = 1 + J⁶ = 1 - V³`.
2. Odd dynamical flow generating sum: `J - J³ + J⁵ = (1 + V + V²) J` and
   `(1 + J²)(J - J³ + J⁵) = J + J⁷`.
3. Unruh–Spin identity `K_Unruh = -Σ` and degree-5 equilibrium:
   `[K_Unruh, [K_Unruh, Φ]] = 4[P, J⁵]`, `V[J, [J, Φ]] = -4[P, J⁵]`, and
   `[K_Unruh, [K_Unruh, Φ]] + V[J, [J, Φ]] = 0`. -/
lemma telescoping_polynomial_ladders_and_unruh_well
    (P X : B) (hP : P * P = P) :
    let j  := J_1 P X
    let ph := Phi_1 P X
    let v  := V_1 P X
    let s  := Sigma_1 P X
    let K  := K_Unruh P X
    let j2 := j * j
    let j3 := j2 * j
    let j4 := j2 * j2
    let j5 := j4 * j
    let j6 := j3 * j3
    let j7 := j6 * j
    1 - j2 + j4 = 1 + v + v * v ∧
    (1 + j2) * (1 - j2 + j4) = 1 + j6 ∧
    1 + j6 = 1 - v * v * v ∧
    j - j3 + j5 = (1 + v + v * v) * j ∧
    (1 + j2) * (j - j3 + j5) = j + j7 ∧
    K = - s ∧
    - comm ph (comm ph j) + 2 • comm s ph = 0 ∧
    comm K (comm K ph) = 4 • comm P j5 ∧
    v * comm j (comm j ph) = - (4 • comm P j5) ∧
    comm K (comm K ph) + v * comm j (comm j ph) = 0 := by
  intro j ph v s K j2 j3 j4 j5 j6 j7
  have h1 : 1 - j2 + j4 = 1 + v + v * v := by
    dsimp only [j2, j4, v, V_1, j]; noncomm_ring
  have h2 : (1 + j2) * (1 - j2 + j4) = 1 + j6 := by
    dsimp only [j2, j3, j4, j6]; noncomm_ring
  have h3 : 1 + j6 = 1 - v * v * v := by
    dsimp only [j2, j3, j6, v, V_1, j]; noncomm_ring
  have h4 : j - j3 + j5 = (1 + v + v * v) * j := by
    dsimp only [j2, j3, j4, j5, v, V_1, j]; noncomm_ring
  have h5 : (1 + j2) * (j - j3 + j5) = j + j7 := by
    dsimp only [j2, j3, j4, j5, j6, j7]; noncomm_ring
  have h_Pj : comm P j = ph := by dsimp only [ph, j, Phi_1, J_1]
  have h_Pj2 : comm P j2 = 0 := by
    dsimp only [j2, j]; rw [J_1_eq P X]; dsimp only [J_mc, comm]; amari_peirce_nf hP
  have h_Pj4 : comm P j4 = 0 := by
    dsimp only [j4]; rw [comm_mul_leibniz P j2 j2, h_Pj2, zero_mul, mul_zero, add_zero]
  have h_Pj5 : comm P j5 = j4 * ph := by
    dsimp only [j5]; rw [comm_mul_leibniz P j4 j, h_Pj4, h_Pj, zero_mul, zero_add]
  have h_j4_v2 : j4 = v * v := by dsimp only [j4, j2, v, V_1, j]; noncomm_ring
  have h_K_s : K = - s := by
    dsimp only [K, K_Unruh, v, s]; rw [V_1_eq hP X, Sigma_1_eq hP X]
    dsimp only [V_met, Sigma_sp, Q_pos, Q_neg]; amari_peirce_nf hP
  have h_SG4 := node4_rotating_ball_parabolic_entropy_well_and_dewitt_lock P X X hP
  rw [← J_1_eq P X, ← Phi_1_eq hP X, ← V_1_eq hP X, ← Sigma_1_eq hP X] at h_SG4
  refine ⟨h1, h2, h3, h4, h5, h_K_s, h_SG4.2.2.1, ?_, ?_, ?_⟩
  · rw [h_K_s]
    have h_neg_s : comm (-s) (comm (-s) ph) = comm s (comm s ph) := by
      unfold comm; noncomm_ring
    rw [h_neg_s, h_Pj5, h_j4_v2]; exact h_SG4.2.2.2.1
  · rw [h_Pj5, h_j4_v2]; exact h_SG4.2.2.2.2.1
  · rw [h_K_s]
    have h_neg_s : comm (-s) (comm (-s) ph) = comm s (comm s ph) := by
      unfold comm; noncomm_ring
    rw [h_neg_s]; exact h_SG4.2.2.2.2.2.1

end InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset
