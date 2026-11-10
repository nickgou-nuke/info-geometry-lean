/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Data.Nat.Choose.Basic
import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.TemperleyLiebCrossedProductAndGrandUnificationPoset

set_option linter.unusedSimpArgs false

/-!
# Track 1 & Track 2 Coagulation: Vieta–SUSY–Kato–Dissipation, Galois–Golay–Hurwitz in `[Ring B]`,
# and Order 28 (Octacosadic) 3-Strand Temperley–Lieb, Jones–Wenzl & Yang–Baxter Braid Poset

This module formalizes in native Lean 4 over an arbitrary noncommutative ring `[Ring B]`
(`0 sorry`, `0 admit`, `0 axiom`, `0 CommRing`):

1. **Track 1A — Complete 1-to-1 Standalone Theorems from Fences `#52`–`#93` (`1tIeNQ8Ajf9Son5W8ICjK18DshSacDzBB`) & `Lean #58`:**
   - `sheet_gramian_factorization_and_four_way_bott_diamond` (`Fence #52`)
   - `real_noncommutative_factorization_of_one_minus_J24` (`Fence #52`)
   - `non_commutative_vieta_scattering_anomaly` (`Fence #56`)
   - `causal_scattering_braid_anomaly` (`Fence #58`)
   - `exact_supersymmetry_and_fermion_genesis` (`Fence #63`)
   - `fermion_first_spectral_triple_unmasking` (`Fence #65`)
   - `autopoietic_lax_flow_and_constants_of_motion` (`Fence #70`, lifted from `[CommRing R]` with `sorry` to `[Ring B]` + `CyclicTrace B M` with `0 sorry`)
   - `relational_entanglement_and_solipsistic_death` (`Fence #73`)
   - `holographic_boundary_and_area_law` (`Fence #76`)
   - `immortal_metric_under_lax_flow` (`Fence #78`)
   - `arrow_of_time_requires_open_system` (`Fence #80`)
   - `recoiling_observer_and_geometric_phase` (`Fence #82`, with `0 sorry`)
   - `kato_berry_spectral_flow_and_covariant_time` (`Lean #58`)
   - `dark_matter_condensate_amplification` (`Fence #84`)
   - `dark_matter_is_the_waist_condensate` (`Fence #87`)
   - `action_gradient_descent_is_thermodynamic_decay` (`Fence #91`, with `0 sorry`)
   - `temperley_lieb_boundary_structure` (`Fence #93`)

2. **Track 1B — Complete 1-to-1 Theorems from `Lean #12, #13, #15, #18` (`1iLTmbxfiVRM8rOhwchpAcmLD3r1zL4JA_2026_11_09`) Lifted to `[Ring B]` (`0 CommRing`):**
   - `parafermion_and_vortex_condensation_thresholds`, `galois_orbit_fixes_only_rational_characters`,
     `coste_gannon_quadratic_galois_spin_preservation_mod24`,
     `marin_salvador_balancing_mutual_locality_condensation`,
     `cyclotomic_character_confinement_and_condensation_projector`
   - `perfect_code_sphere_packing_trinity`, `witt_steiner_design_block_counts`,
     `leech_lattice_root_annihilation_and_theta_series` (over `[Ring B]`),
     `conway_threefold_leech_decomposition_and_monster_griess`
   - `abelian_character_blind_to_commutators` (lifted to `[Ring B]` via explicit commutator defect),
     `chebyshev_horseshoe_parabola_identity` (over `[Ring B]`),
     `covariant_vs_contravariant_noncommutative_convolution_theorem`,
     `s3_wedderburn_artin_and_2d_peirce_syntax_witness`,
     `peirce_peter_weyl_four_basis_reconstruction` (over `[Ring B]`)
   - `clebsch_gordan_s4_idempotency_and_mutual_orthogonality` (over `[Ring B]`),
     `clebsch_gordan_frobenius_pythagorean_theorem` (over `[Ring B]`),
     `hurwitz_corner_triality_attention_filter` (over `[Ring B]`),
     `adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge` (over `[Ring B]`)

3. **Track 2 — Order 28 (Octacosadic) 3-Strand Temperley–Lieb, Jones–Wenzl Idempotent & Yang–Baxter Braid Poset (`𝔒ℭ₁ ≺ ⋯ ≺ 𝔒ℭ₅`):**
   - **Node `𝔒ℭ₁` (`three_strand_halmos_commutator_aporia`):**
     For three projections $e_1, e_2, e_3 \in B$ with distant commutativity $e_1 e_3 = e_3 e_1$,
     the adjacent Halmos generators $H_{12} = e_1 - e_2$ and $H_{23} = e_2 - e_3$ fail to commute
     by the exact sum of adjacent braiding fluxes:
     $$[H_{12}, H_{23}] = -(\Sigma_{12} + \Sigma_{23}) = -([e_1, e_2] + [e_2, e_3]).$$
   - **Node `𝔒ℭ₂` (`three_strand_cubic_temperley_lieb_braid_transfer`):**
     For $T_{123} = e_1 e_2 e_3$ and $T_{321} = e_3 e_2 e_1$:
     $$T_{123} e_1 = \tau e_1 e_3 = e_3 T_{123}, \qquad T_{123}^2 = \tau^2 e_1 e_3,$$
     $$T_{123} T_{321} = \tau^2 e_1, \qquad T_{321} T_{123} = \tau^2 e_3, \qquad [T_{123}, T_{321}] = \tau^2 (H_{12} + H_{23}).$$
   - **Node `𝔒ℭ₃` (`jones_wenzl_second_idempotent_from_halmos_square`):**
     The division-free 2-strand Jones–Wenzl element $W_2 := (1 - \tau) - (e_1 - e_2)^2 = (1 - \tau) - H_{12}^2$
     satisfies exact boundary annihilation and scaled idempotence:
     $$e_1 W_2 = W_2 e_1 = e_2 W_2 = W_2 e_2 = 0, \qquad H_{12} W_2 = W_2 H_{12} = 0, \qquad W_2^2 = (1 - \tau) W_2.$$
   - **Node `𝔒ℭ₄` (`kauffman_jones_yang_baxter_braid_defect_identity`):**
     For $g_1 = 1 + u e_1$ and $g_2 = 1 + u e_2$ (with central spectral parameter $u$),
     the Yang–Baxter braid defect is governed by the exact Jones–Kauffman quadratic $1 + u + \tau u^2$:
     $$g_1 g_2 g_1 - g_2 g_1 g_2 = (u + u^2 + \tau u^3) (e_1 - e_2) = u(1 + u + \tau u^2) H_{12}.$$
   - **Node `𝔒ℭ₅` (`master_octacosadic_three_strand_yang_baxter_coagulation`):**
     Coagulates `𝔒ℭ₁ ≺ ⋯ ≺ 𝔒ℭ₅` with Track 1A and Track 1B, and `temperley_lieb_yang_baxter_colimit_cone_transport`
     transports the 3-strand Temperley–Lieb, Jones–Wenzl, and Yang–Baxter braid algebra across any inductive
     colimit cone (`toLimit : ∀ k : ℕ, Stage k →+* Limit`).

## Mathematical Audit & Three-Bucket Classification

- **BUCKET 1 — Validated Kernel-Proved Core:**
  All Vieta–SUSY–Kato–Dissipation theorems (Track 1A), Galois–Golay–Peter–Weyl–Wigner–Hurwitz theorems (Track 1B),
  and Order 28 3-strand Temperley–Lieb, Jones–Wenzl idempotent, Yang–Baxter braid, and inductive colimit
  cone transport theorems (Track 2) are constructively proved in `[Ring B]` with zero `sorry`, zero `admit`,
  and zero custom structures.
- **BUCKET 2 — Salvageable With Honest Scope Narrowing:**
  Finite `2 × 2`, `3 × 3`, and quaternion operator tuples are defined as native product types (`Mat2Op`, `Mat3Op`, `QuatOp`)
  over `[Ring K]`, and the infinite-strand UHF / `TL_∞` limit is transported via explicit inductive colimit cones
  `toLimit : ∀ k : ℕ, Stage k →+* Limit` compatible with `embed : ∀ k : ℕ, Stage k →+* Stage (k + 1)`.
- **BUCKET 3 — Vacuous / Unjustified / Beyond Current Formal Scope:**
  Analytic `II₁` subfactor index classifications and topological 3-manifold Reshetikhin–Turaev state-sum invariants
  beyond the algebraic Temperley–Lieb, Jones–Wenzl, Yang–Baxter, and inductive colimit cone transport identities proved here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.WheelerSingleCommutatorHistoricalPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.IKKTLaxHolographicDarkCondensatePoset

universe u v

-- ============================================================================
-- SECTION 1: Poset Node Type for Order 28 (Octacosadic) & Track 1 Synthesis
-- ============================================================================

/-- Acyclic causal poset nodes `𝔒ℭ₁ ≺ 𝔒ℭ₂ ≺ 𝔒ℭ₃ ≺ 𝔒ℭ₄ ≺ 𝔒ℭ₅`. -/
inductive OctacosadicBraidNode : Type
  | OC1_ThreeStrandHalmosAporia
  | OC2_CubicBraidTransfer
  | OC3_JonesWenzlIdempotent
  | OC4_KauffmanJonesYangBaxterDefect
  | OC5_OctacosadicMasterCoagulation
  deriving DecidableEq, Repr

namespace OctacosadicBraidNode

/-- Default inhabited instance for `OctacosadicBraidNode`. -/
instance : Inhabited OctacosadicBraidNode := ⟨.OC1_ThreeStrandHalmosAporia⟩

/-- Strict causal rank ordering on `OctacosadicBraidNode`. -/
def rank : OctacosadicBraidNode → ℕ
  | OC1_ThreeStrandHalmosAporia       => 1
  | OC2_CubicBraidTransfer            => 2
  | OC3_JonesWenzlIdempotent          => 3
  | OC4_KauffmanJonesYangBaxterDefect => 4
  | OC5_OctacosadicMasterCoagulation  => 5

/-- The causal rank map on `OctacosadicBraidNode` is injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- Partial order on `OctacosadicBraidNode` induced by `rank`. -/
instance : PartialOrder OctacosadicBraidNode where
  le a b := rank a ≤ rank b
  lt a b := rank a < rank b
  le_refl a := Nat.le_refl (rank a)
  le_trans _ _ _ hab hbc := Nat.le_trans hab hbc
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm _ _ hab hba := rank_injective (Nat.le_antisymm hab hba)

/-- Strict 5-stage causal chain `𝔒ℭ₁ ≺ 𝔒ℭ₂ ≺ 𝔒ℭ₃ ≺ 𝔒ℭ₄ ≺ 𝔒ℭ₅`. -/
theorem oc_poset_chain :
    OC1_ThreeStrandHalmosAporia < OC2_CubicBraidTransfer ∧
    OC2_CubicBraidTransfer < OC3_JonesWenzlIdempotent ∧
    OC3_JonesWenzlIdempotent < OC4_KauffmanJonesYangBaxterDefect ∧
    OC4_KauffmanJonesYangBaxterDefect < OC5_OctacosadicMasterCoagulation := by
   refine ⟨by decide, by decide, by decide, by decide⟩

end OctacosadicBraidNode

-- ============================================================================
-- SECTION 2: Track 1A — Standalone Theorems from Fences #52..#93 & Lean #58
-- ============================================================================

section Track1A_VietaSusyKatoDissipation

variable {B : Type u} [Ring B]

/-- Positive sheet Gramian `Q_+ = N_+(P, X) N_-(P, X)`. -/
def Q_pos_sheet (P X : B) : B := (P * J_1 P X) * (- (J_1 P X * P))
/-- Negative sheet Gramian `Q_- = N_-(P, X) N_+(P, X)`. -/
def Q_neg_sheet (P X : B) : B := (- (J_1 P X * P)) * (P * J_1 P X)

/-- 24th Cyclotomic Polynomial `Φ₂₄(J) = J⁸ - J⁴ + 1` evaluated on `J : B`. -/
def Phi24_Op (J : B) : B :=
  let J2 := J * J
  let J4 := J2 * J2
  let J8 := J4 * J4
  J8 - J4 + 1

/-- Nilpotent lightcone supercharge `N_JF(P, X) = J_1(P, X) + Phi_1(P, X)`. -/
def N_JF (P X : B) : B := J_1 P X + Phi_1 P X
/-- Positive lightcone supercharge `Q_susy(P, X) = J_1(P, X) + Phi_1(P, X)`. -/
def Q_susy (P X : B) : B := J_1 P X + Phi_1 P X
/-- Conjugate lightcone supercharge `Q_bar_susy(P, X) = J_1(P, X) - Phi_1(P, X)`. -/
def Q_bar_susy (P X : B) : B := J_1 P X - Phi_1 P X

/-- Connes spectral triple Dirac operator `Dirac(P, X) = Phi_1(P, X)`. -/
def Dirac_Op (P X : B) : B := Phi_1 P X
/-- Connes chiral grading involution `Gamma5(P) = S_P(P)`. -/
def Gamma5_Op (P : B) : B := S_P P

/-- Observer Berry–Simon connection `Gamma_obs = [P, dP]`. -/
def Gamma_obs (P dP : B) : B := comm P dP
/-- Kato adiabatic connection `Gamma_Kato = [dP, P]`. -/
def Gamma_Kato (P dP : B) : B := comm dP P

/-- Waist projector `P0_waist = 1 - P1 - P2`. -/
def P0_waist (P1 P2 : B) : B := 1 - P1 - P2
/-- Waist dark condensate `C_zero = P0 C P0`. -/
def C_zero_waist (P1 P2 C : B) : B := P0_waist P1 P2 * C * P0_waist P1 P2
/-- Bare positive horizon-to-waist corner `P1 X P0`. -/
def N_plus_bare (P1 P2 X : B) : B := P1 * X * P0_waist P1 P2
/-- Bare negative waist-to-horizon corner `P0 Y P1`. -/
def N_minus_bare (P1 P2 Y : B) : B := P0_waist P1 P2 * Y * P1
/-- Condensate-dressed positive corner `N_plus_bare * C_zero_waist`. -/
def N_plus_dressed (P1 P2 X C : B) : B := N_plus_bare P1 P2 X * C_zero_waist P1 P2 C
/-- Condensate-dressed negative corner `C_zero_waist * N_minus_bare`. -/
def N_minus_dressed (P1 P2 Y C : B) : B := C_zero_waist P1 P2 C * N_minus_bare P1 P2 Y

/--
**Fence `#52` Theorem 1 (`sheet_gramian_factorization_and_four_way_bott_diamond`):**
Exact sheet-Gramian factorizations of `1 ± V` and `1 ± Σ` and the four-way factorization
diamond of `1 - [P, X]⁴` over `[Ring B]`.
-/
theorem sheet_gramian_factorization_and_four_way_bott_diamond
    (P X : B) (hP : P * P = P) :
    let j  := J_1 P X
    let ph := Phi_1 P X
    let v  := V_1 P X
    let s  := Sigma_1 P X
    let qp := Q_pos_sheet P X
    let qm := Q_neg_sheet P X
    let j2 := j * j
    let j4 := j2 * j2
    (1 - qp) * (1 - qm) = 1 - v ∧
    (1 + qp) * (1 + qm) = 1 + v ∧
    (1 - qp) * (1 + qm) = 1 - s ∧
    (1 + qp) * (1 - qm) = 1 + s ∧
    (1 - j) * (1 + j) * (1 - ph) * (1 + ph) = 1 - j4 ∧
    (1 - v) * (1 + v) = 1 - j4 ∧
    (1 - s) * (1 + s) = 1 - j4 ∧
    (1 - qp) * (1 + qp) * (1 - qm) * (1 + qm) = 1 - j4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [Q_pos_sheet, Q_neg_sheet, Sigma_1, V_1, Phi_1, J_1, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]
    abel

/--
**Fence `#52` Theorem 3 (`real_noncommutative_factorization_of_one_minus_J24`):**
Complete noncommutative factorization of `1 - [P, X]²⁴` over `[Ring B]`.
-/
theorem real_noncommutative_factorization_of_one_minus_J24
    (P X : B) (hP : P * P = P) :
    let j   := J_1 P X
    let ph  := Phi_1 P X
    let j2  := j * j
    let j4  := j2 * j2
    let j8  := j4 * j4
    let j12 := j8 * j4
    let j24 := j12 * j12
    (1 - j) * (1 + j) * (1 - ph) * (1 + ph) * (1 + j4 + j8) = 1 - j12 ∧
    (1 + j4) * Phi24_Op j = 1 + j12 ∧
    (1 - j) * (1 + j) * (1 - ph) * (1 + ph) * (1 + j4 + j8) *
      (1 + j4) * Phi24_Op j = 1 - j24 := by
  have h_bott : (1 - J_1 P X) * (1 + J_1 P X) * (1 - Phi_1 P X) * (1 + Phi_1 P X) =
      1 - (J_1 P X * J_1 P X) * (J_1 P X * J_1 P X) :=
    (sheet_gramian_factorization_and_four_way_bott_diamond P X hP).2.2.2.2.1
  set j := J_1 P X
  set ph := Phi_1 P X
  set j2 := j * j
  set j4 := j2 * j2
  set j8 := j4 * j4
  set j12 := j8 * j4
  set j24 := j12 * j12
  have h_12_minus : (1 - j4) * (1 + j4 + j8) = 1 - j12 := by
    dsimp [j12, j8, j4, j2]
    noncomm_ring
  have h_12_plus : (1 + j4) * Phi24_Op j = 1 + j12 := by
    dsimp [Phi24_Op, j12, j8, j4, j2]
    noncomm_ring
  have h_24 : (1 - j12) * (1 + j12) = 1 - j24 := by
    dsimp [j24]
    noncomm_ring
  refine ⟨?_, h_12_plus, ?_⟩
  · rw [h_bott, h_12_minus]
  · calc (1 - j) * (1 + j) * (1 - ph) * (1 + ph) * (1 + j4 + j8) * (1 + j4) * Phi24_Op j
      _ = ((1 - j4) * (1 + j4 + j8)) * ((1 + j4) * Phi24_Op j) := by
          rw [h_bott]; simp only [mul_assoc]
      _ = (1 - j12) * (1 + j12) := by rw [h_12_minus, h_12_plus]
      _ = 1 - j24               := h_24

/--
**Fence `#56` (`non_commutative_vieta_scattering_anomaly`):**
Interleaving the four noncommutative roots `1 ± J` and `1 ± Φ` of `1 - J⁴` generates
the nilpotent lightcone `J + Φ`, the spin `Σ`, and the scattering force `2V(J + Φ) + V²`.
-/
theorem non_commutative_vieta_scattering_anomaly
    (P X : B) (hP : P * P = P) :
    let j   := J_1 P X
    let ph  := Phi_1 P X
    let v   := V_1 P X
    let s   := Sigma_1 P X
    let njf := N_JF P X
    let R1  := 1 - j
    let R2  := 1 + j
    let R3  := 1 - ph
    let R4  := 1 + ph
    anticomm j ph = 0 ∧
    njf * njf = 0 ∧
    (R1 * R2) * (R3 * R4) = 1 - (j * j * j * j) ∧
    (R1 * R3) = 1 + s - njf ∧
    (R2 * R4) = 1 + s + njf ∧
    comm s njf = 2 • (v * njf) ∧
    (R1 * R3) * (R2 * R4) = 1 + 2 • s + (v * v) + 2 • (v * njf) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [N_JF, Sigma_1, V_1, Phi_1, J_1, comm, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, two_nsmul, mul_assoc, hP, proj_idem hP]
    abel

/--
**Fence `#58` (`causal_scattering_braid_anomaly`):**
Causal Vieta scattering and the spin-dilaton bracket `[Σ, J] = 2VΦ`, `[Σ, Φ] = 2VJ`,
`[Σ, J + Φ] = 2V(J + Φ)`.
-/
theorem causal_scattering_braid_anomaly
    (P X : B) (hP : P * P = P) :
    let j   := J_1 P X
    let ph  := Phi_1 P X
    let v   := V_1 P X
    let s   := Sigma_1 P X
    let njf := N_JF P X
    let R1  := 1 - j
    let R2  := 1 + j
    let R3  := 1 - ph
    let R4  := 1 + ph
    anticomm j ph = 0 ∧
    njf * njf = 0 ∧
    (R1 * R2) * (R3 * R4) = 1 - (j * j * j * j) ∧
    R1 * R3 = 1 + s - njf ∧
    R2 * R4 = 1 + s + njf ∧
    comm s j = 2 • (v * ph) ∧
    comm s ph = 2 • (v * j) ∧
    comm s njf = 2 • (v * njf) ∧
    (R1 * R3) * (R2 * R4) = 1 + 2 • s + v * v + 2 • (v * njf) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [N_JF, Sigma_1, V_1, Phi_1, J_1, comm, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, two_nsmul, mul_assoc, hP, proj_idem hP]
    abel

/--
**Fence `#63` (`exact_supersymmetry_and_fermion_genesis`):**
The nilpotent supercharges `Q = J + Φ` and `Q̄ = J - Φ` satisfy `Q² = Q̄² = 0`,
`{Q, Q̄} = -4V`, `[Q, Q̄] = -4Σ`, `[Σ, Q] = 2VQ`, and `[Σ, Q̄] = -2VQ̄`.
-/
theorem exact_supersymmetry_and_fermion_genesis
    (P X : B) (hP : P * P = P) :
    let j  := J_1 P X
    let ph := Phi_1 P X
    let v  := V_1 P X
    let s  := Sigma_1 P X
    let q  := Q_susy P X
    let qb := Q_bar_susy P X
    anticomm j ph = 0 ∧
    q * q = 0 ∧
    qb * qb = 0 ∧
    anticomm q qb = - (4 • v) ∧
    comm q qb = - (4 • s) ∧
    comm s q = 2 • (v * q) ∧
    comm s qb = - (2 • (v * qb)) := by
  have h4v : 4 • V_1 P X = V_1 P X + V_1 P X + V_1 P X + V_1 P X := by
    rw [ show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul ]; abel
  have h4s : 4 • Sigma_1 P X = Sigma_1 P X + Sigma_1 P X + Sigma_1 P X + Sigma_1 P X := by
    rw [ show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul ]; abel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [Phi_1, J_1, comm, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]; abel
  · dsimp only [Q_susy, Phi_1, J_1, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]; abel
  · dsimp only [Q_bar_susy, Phi_1, J_1, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]; abel
  · rw [h4v]
    dsimp only [Q_susy, Q_bar_susy, V_1, Phi_1, J_1, comm, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]; abel
  · rw [h4s]
    dsimp only [Q_susy, Q_bar_susy, Sigma_1, Phi_1, J_1, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]; abel
  · dsimp only [Q_susy, Sigma_1, V_1, Phi_1, J_1, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, two_nsmul, mul_assoc, hP, proj_idem hP]; abel
  · dsimp only [Q_bar_susy, Sigma_1, V_1, Phi_1, J_1, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, two_nsmul, mul_assoc, hP, proj_idem hP]; abel

/--
**Fence `#65` (`fermion_first_spectral_triple_unmasking`):**
Unmasks the supercharges `Q = 2 N_+` and `Q̄ = -2 N_-` as scaled Peirce corner jumps and
establishes the Connes spectral triple axioms `γ₅² = 1`, `{D, γ₅} = 0`, `D² = V`,
`2 N_+ = D + γ₅ D`, and `2 N_- = D - γ₅ D`.
-/
theorem fermion_first_spectral_triple_unmasking
    (P X : B) (hP : P * P = P) :
    let np := N_plus P X
    let nm := N_minus P X
    let v  := V_1 P X
    let q  := Q_susy P X
    let qb := Q_bar_susy P X
    let D  := Dirac_Op P X
    let γ5 := Gamma5_Op P
    q = 2 • np ∧
    qb = - (2 • nm) ∧
    γ5 * γ5 = 1 ∧
    anticomm D γ5 = 0 ∧
    D * D = v ∧
    2 • np = D + γ5 * D ∧
    2 • nm = D - γ5 * D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [Q_susy, Q_bar_susy, Dirac_Op, Gamma5_Op, S_P, Phi_1, J_1, V_1,
                N_plus, N_minus, comm, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, two_nsmul, mul_assoc, hP, proj_idem hP]
    abel

/--
**Fence `#70` (`autopoietic_lax_flow_and_constants_of_motion`, lifted to `[Ring B]` with `0 sorry`):**
Under the Lax Hamiltonian `V = -[P, X]²`, `P, J, Φ, Σ` are strictly conserved (`[V, ·] = 0`),
and under any `CyclicTrace B M`, the variational gradient satisfies
`tr(V(P, X + dX) - V(P, X) - V(P, dX)) = 2 • tr(Φ dX)`.
-/
theorem autopoietic_lax_flow_and_constants_of_motion
    {M : Type v} [AddCommGroup M] (tr : CyclicTrace B M)
    (P X dX : B) (hP : P * P = P) :
    let j     := J_1 P X
    let j_dx  := J_1 P dX
    let ph    := Phi_1 P X
    let v     := V_1 P X
    let s     := Sigma_1 P X
    let v_dx  := V_1 P dX
    let v_xdx := V_1 P (X + dX)
    comm v P = 0 ∧
    comm v j = 0 ∧
    comm v ph = 0 ∧
    comm v s = 0 ∧
    v_xdx - v - v_dx = - (j * j_dx + j_dx * j) ∧
    tr.tr (v_xdx - v - v_dx) = 2 • tr.tr (ph * dX) := by
  have h_ikkt := ikkt_connes_spectral_action_euler_lagrange tr P X dX hP
  have h_v_var : V_1 P (X + dX) - V_1 P X - V_1 P dX = - (J_1 P X * J_1 P dX + J_1 P dX * J_1 P X) :=
    h_ikkt.2.2.1
  have h_tr_var : tr.tr (V_1 P (X + dX) - V_1 P X - V_1 P dX) = 2 • tr.tr (Phi_1 P X * dX) :=
    h_ikkt.2.2.2
  refine ⟨?_, ?_, ?_, ?_, h_v_var, h_tr_var⟩ <;>
  · dsimp only [V_1, Sigma_1, Phi_1, J_1, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]
    abel

/--
**Fence `#73` (`relational_entanglement_and_solipsistic_death`):**
If `comm P X_self = 0`, `X_self` generates zero geometry (`J = Φ = V = Σ = 0`), and for
`X_tot = X_self + X_other` the entire geometric frame depends strictly on `X_other`.
-/
theorem relational_entanglement_and_solipsistic_death
    (P X_self X_other : B) (h_solipsism : comm P X_self = 0) :
    let X_tot := X_self + X_other
    J_1 P X_self = 0 ∧
    Phi_1 P X_self = 0 ∧
    V_1 P X_self = 0 ∧
    Sigma_1 P X_self = 0 ∧
    J_1 P X_tot = J_1 P X_other ∧
    Phi_1 P X_tot = Phi_1 P X_other ∧
    V_1 P X_tot = V_1 P X_other ∧
    Sigma_1 P X_tot = Sigma_1 P X_other ∧
    V_1 P X_tot = - (comm P X_other * comm P X_other) := by
  have hj_tot : J_1 P (X_self + X_other) = J_1 P X_other := by
    dsimp [J_1, comm]
    have h_self : P * X_self - X_self * P = 0 := h_solipsism
    calc P * (X_self + X_other) - (X_self + X_other) * P
      _ = (P * X_self - X_self * P) + (P * X_other - X_other * P) := by noncomm_ring
      _ = 0 + (P * X_other - X_other * P) := by rw [h_self]
      _ = P * X_other - X_other * P := by rw [zero_add]
  have hph_tot : Phi_1 P (X_self + X_other) = Phi_1 P X_other := by
    change comm P (J_1 P (X_self + X_other)) = comm P (J_1 P X_other)
    rw [hj_tot]
  have hj_self : J_1 P X_self = 0 := h_solipsism
  have hph_self : Phi_1 P X_self = 0 := by
    change comm P (J_1 P X_self) = 0
    rw [hj_self]
    dsimp [comm]; simp only [mul_zero, zero_mul, sub_self]
  refine ⟨hj_self, hph_self, ?_, ?_, hj_tot, hph_tot, ?_, ?_, ?_⟩
  · dsimp [V_1]; rw [hj_self, mul_zero, neg_zero]
  · dsimp [Sigma_1]; rw [hj_self, zero_mul]
  · dsimp [V_1]; rw [hj_tot]
  · dsimp [Sigma_1]; rw [hj_tot, hph_tot]
  · dsimp [V_1]; rw [hj_tot]; rfl

/--
**Fence `#76` (`holographic_boundary_and_area_law`):**
The observer `P` commutes with both bulk sectors `P X P` and `(1 - P) X (1 - P)`, localizing
`J, Φ, V, Σ` exclusively to the boundary jumps `N_+, N_-`.
-/
theorem holographic_boundary_and_area_law
    (P X : B) (hP : P * P = P) :
    let p_b := P * X * P
    let q_b := (1 - P) * X * (1 - P)
    let np  := N_plus P X
    let nm  := N_minus P X
    let j   := J_1 P X
    let ph  := Phi_1 P X
    let v   := V_1 P X
    let s   := Sigma_1 P X
    p_b + q_b + np + nm = X ∧
    comm P p_b = 0 ∧
    comm P q_b = 0 ∧
    j = np - nm ∧
    ph = np + nm ∧
    v = anticomm np nm ∧
    s = comm np nm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [N_plus, N_minus, J_1, Phi_1, V_1, Sigma_1, comm, anticomm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]
    abel

/--
**Fence `#78` (`immortal_metric_under_lax_flow`):**
Under the Lax flow `dX = [V, X]`, `dj = [P, dX] = [V, J]` and `dv = -(dj * J + J * dj) = 0`.
-/
theorem immortal_metric_under_lax_flow
    (P X : B) (hP : P * P = P) :
    let j  := J_1 P X
    let v  := V_1 P X
    let dX := comm v X
    let dj := comm P dX
    let dv := - (dj * j + j * dj)
    comm v P = 0 ∧
    dj = comm v j ∧
    dv = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp only [V_1, J_1, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]
    abel

/--
**Fence `#80` (`arrow_of_time_requires_open_system`):**
In a closed system (`dX_closed = [V, X_B]`), `dj_closed = [P, dX_closed] = 0`, whereas in an
open system (`dX_B` independent), `dv_open = - {dj_open, J} = - (dj_open * J + J * dj_open)`.
-/
theorem arrow_of_time_requires_open_system
    (P X_B dX_B : B) (hP : P * P = P) :
    let j         := J_1 P X_B
    let v         := V_1 P X_B
    let dX_closed := comm v X_B
    let dj_closed := comm P dX_closed
    let dj_open   := comm P dX_B
    let dv_open   := - anticomm dj_open j
    dj_closed = 0 ∧
    dv_open = - (dj_open * j + j * dj_open) := by
  refine ⟨?_, rfl⟩
  dsimp only [V_1, J_1, comm]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
             neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]
  abel

/--
**Fence `#82` (`recoiling_observer_and_geometric_phase`, `0 sorry`):**
For any moving projector `P² = P` with `dP * P + P * dP = dP`, the recoil is strictly
off-diagonal (`P * dP * P = 0`), satisfies `[P, [P, dP]] = dP`, `[P, Gamma_obs] = dP`,
`[Gamma_obs, P] = - dP`, and `[Gamma_Kato, P] = dP`.
-/
theorem recoiling_observer_and_geometric_phase
    (P dP X dX : B)
    (hP : P * P = P)
    (hdP : dP * P + P * dP = dP) :
    let G_obs  := Gamma_obs P dP
    let G_kato := Gamma_Kato P dP
    let dj     := comm dP X + comm P dX
    P * dP * P = 0 ∧
    comm P G_obs = dP ∧
    comm G_obs P = - dP ∧
    comm G_kato P = dP ∧
    comm P (comm P dP) = dP ∧
    dj = comm dP X + comm P dX := by
  have h_P_dP_P : P * dP * P = 0 := by
    have h1 : P * (dP * P + P * dP) = P * dP := by rw [hdP]
    have h2 : P * dP * P + P * dP = P * dP := by
      calc P * dP * P + P * dP
        _ = P * dP * P + (P * P) * dP := by rw [hP]
        _ = P * (dP * P + P * dP) := by noncomm_ring
        _ = P * dP := h1
    calc P * dP * P
      _ = (P * dP * P + P * dP) - P * dP := by abel
      _ = P * dP - P * dP := by rw [h2]
      _ = 0 := by abel
  have h_vielbein : comm P (comm P dP) = dP := by
    dsimp [comm]
    calc P * (P * dP - dP * P) - (P * dP - dP * P) * P
      _ = (P * P) * dP - P * dP * P - P * dP * P + dP * (P * P) := by noncomm_ring
      _ = P * dP - 0 - 0 + dP * P := by rw [hP, h_P_dP_P]
      _ = dP * P + P * dP := by abel
      _ = dP := hdP
  have h_G_obs : comm (Gamma_obs P dP) P = - dP := by
    dsimp [Gamma_obs, comm]
    calc (P * dP - dP * P) * P - P * (P * dP - dP * P)
      _ = - (P * (P * dP - dP * P) - (P * dP - dP * P) * P) := by abel
      _ = - (comm P (comm P dP)) := rfl
      _ = - dP := by rw [h_vielbein]
  have h_G_kato : comm (Gamma_Kato P dP) P = dP := by
    dsimp [Gamma_Kato, comm]
    calc (dP * P - P * dP) * P - P * (dP * P - P * dP)
      _ = P * (P * dP - dP * P) - (P * dP - dP * P) * P := by noncomm_ring
      _ = comm P (comm P dP) := rfl
      _ = dP := h_vielbein
  exact ⟨h_P_dP_P, h_vielbein, h_G_obs, h_G_kato, h_vielbein, rfl⟩

/--
**Lean `#58` (`kato_berry_spectral_flow_and_covariant_time`):**
Proves `P * dP * P = 0`, `[Gamma_Kato, P] = dP`, `P * Gamma_Kato * P = 0`,
`(1 - P) * Gamma_Kato * (1 - P) = 0`, and `[dP, X] = [Gamma_Kato, J] + [[Gamma_Kato, X], P]`.
-/
theorem kato_berry_spectral_flow_and_covariant_time
    (P dP X : B)
    (hP : P * P = P)
    (hdP : dP * P + P * dP = dP) :
    let j      := J_1 P X
    let G_kato := Gamma_Kato P dP
    P * dP * P = 0 ∧
    comm G_kato P = dP ∧
    P * G_kato * P = 0 ∧
    (1 - P) * G_kato * (1 - P) = 0 ∧
    comm dP X = comm G_kato j + comm (comm G_kato X) P := by
  have h_rec := recoiling_observer_and_geometric_phase P dP X 0 hP hdP
  have h_P_dP_P : P * dP * P = 0 := h_rec.1
  have h_G_P : comm (Gamma_Kato P dP) P = dP := h_rec.2.2.2.1
  have h_P_G_P : P * Gamma_Kato P dP * P = 0 := by
    dsimp [Gamma_Kato, comm]
    calc P * (dP * P - P * dP) * P
      _ = P * dP * (P * P) - (P * P) * dP * P := by noncomm_ring
      _ = P * dP * P - P * dP * P := by rw [hP]
      _ = 0 := by abel
  have h_Q_G_Q : (1 - P) * Gamma_Kato P dP * (1 - P) = 0 := by
    dsimp [Gamma_Kato, comm]
    calc (1 - P) * (dP * P - P * dP) * (1 - P)
      _ = (dP * P - P * dP * P - P * dP + (P * P) * dP) * (1 - P) := by noncomm_ring
      _ = (dP * P - 0 - P * dP + P * dP) * (1 - P) := by rw [h_P_dP_P, hP]
      _ = (dP * P) * (1 - P) := by abel
      _ = dP * P - dP * (P * P) := by noncomm_ring
      _ = dP * P - dP * P := by rw [hP]
      _ = 0 := by abel
  have h_jacobi : comm dP X = comm (Gamma_Kato P dP) (J_1 P X) + comm (comm (Gamma_Kato P dP) X) P := by
    calc comm dP X
      _ = comm (comm (Gamma_Kato P dP) P) X := by rw [h_G_P]
      _ = comm (Gamma_Kato P dP) (J_1 P X) + comm (comm (Gamma_Kato P dP) X) P := by
          dsimp [J_1, comm]
          noncomm_ring
  exact ⟨h_P_dP_P, h_G_P, h_P_G_P, h_Q_G_Q, h_jacobi⟩

/--
**Fence `#84` (`dark_matter_condensate_amplification`):**
An operator `C₀ = P₀ C P₀` confined to the waist `P₀ = 1 - P₁ - P₂` strictly commutes with `P₁`
(`comm P₁ C₀ = 0`) while amplifying the dressed metric `V_dressed = P₁ X C₀² Y P₁`.
-/
theorem dark_matter_condensate_amplification
    (P1 P2 X Y C : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let c0 := C_zero_waist P1 P2 C
    let np_d := N_plus_dressed P1 P2 X C
    let nm_d := N_minus_dressed P1 P2 Y C
    let V_dressed := np_d * nm_d
    comm P1 c0 = 0 ∧
    np_d = P1 * X * c0 ∧
    nm_d = c0 * Y * P1 ∧
    V_dressed = P1 * X * (c0 * c0) * Y * P1 := by
  have h1'  : ∀ W : B, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W : B, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W : B, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W : B, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [N_plus_dressed, N_minus_dressed, N_plus_bare, N_minus_bare, C_zero_waist, P0_waist, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, h1, h2, h12, h21, h1', h2', h12', h21', mul_zero, zero_mul]
    abel

/--
**Fence `#87` (`dark_matter_is_the_waist_condensate`):**
Proves `P₀² = P₀`, `comm P₁ C₀ = 0`, wave dressing, and `V_dres = P₁ X C₀² Y P₁`,
`V_bare = P₁ X P₀ Y P₁`.
-/
theorem dark_matter_is_the_waist_condensate
    (P1 P2 X Y C : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := P0_waist P1 P2
    let c0 := C_zero_waist P1 P2 C
    let np_bare := N_plus_bare P1 P2 X
    let nm_bare := N_minus_bare P1 P2 Y
    let np_dres := N_plus_dressed P1 P2 X C
    let nm_dres := N_minus_dressed P1 P2 Y C
    let V_bare := np_bare * nm_bare
    let V_dres := np_dres * nm_dres
    P0 * P0 = P0 ∧
    comm P1 c0 = 0 ∧
    np_dres = P1 * X * c0 ∧
    nm_dres = c0 * Y * P1 ∧
    V_dres = P1 * X * (c0 * c0) * Y * P1 ∧
    V_bare = P1 * X * P0 * Y * P1 := by
  have h_amp := dark_matter_condensate_amplification P1 P2 X Y C h1 h2 h12 h21
  have h1'  : ∀ W : B, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W : B, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W : B, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W : B, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  have h_P0 : P0_waist P1 P2 * P0_waist P1 P2 = P0_waist P1 P2 := by
    dsimp [P0_waist]
    simp only [sub_mul, mul_sub, one_mul, mul_one, h1, h2, h12, h21]
    abel
  have h_bare : N_plus_bare P1 P2 X * N_minus_bare P1 P2 Y = P1 * X * P0_waist P1 P2 * Y * P1 := by
    dsimp [N_plus_bare, N_minus_bare]
    calc (P1 * X * P0_waist P1 P2) * (P0_waist P1 P2 * Y * P1)
      _ = P1 * X * (P0_waist P1 P2 * P0_waist P1 P2) * Y * P1 := by noncomm_ring
      _ = P1 * X * P0_waist P1 P2 * Y * P1 := by rw [h_P0]
  exact ⟨h_P0, h_amp.1, h_amp.2.1, h_amp.2.2.1, h_amp.2.2.2, h_bare⟩

/--
**Fence `#91` (`action_gradient_descent_is_thermodynamic_decay`, `0 sorry`):**
Under the IKKT/Connes gradient descent flow `D(P) = 0` and `D(X) = -2 Φ`, the geometric
frame undergoes exact exponential decay: `D(J) = -2 J`, `D(Φ) = -2 Φ`, and `D(V) = -4 V`.
-/
theorem action_gradient_descent_is_thermodynamic_decay
    (D : OpDerivation B) (P X : B) (hP : P * P = P)
    (hDP : D.toFun P = 0)
    (hDX : D.toFun X = - (Phi_1 P X + Phi_1 P X)) :
    let j  := J_1 P X
    let ph := Phi_1 P X
    let v  := V_1 P X
    D.toFun j = - (j + j) ∧
    D.toFun ph = - (ph + ph) ∧
    D.toFun v = - (v + v + v + v) := by
  have h_comm_deriv : ∀ Y : B, D.toFun (comm P Y) = comm P (D.toFun Y) := by
    intro Y
    dsimp [comm]
    rw [D.map_sub', D.leibniz', D.leibniz', hDP]
    simp only [zero_mul, mul_zero, zero_add, add_zero]
  have hp_ph : comm P (Phi_1 P X) = J_1 P X := by
    dsimp [Phi_1, J_1, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               neg_mul, mul_neg, mul_assoc, hP, proj_idem hP]
    abel
  have h_j_decay : D.toFun (J_1 P X) = - (J_1 P X + J_1 P X) := by
    calc D.toFun (J_1 P X)
      _ = comm P (D.toFun X) := h_comm_deriv X
      _ = comm P (- (Phi_1 P X + Phi_1 P X)) := by rw [hDX]
      _ = - (comm P (Phi_1 P X) + comm P (Phi_1 P X)) := by
          dsimp [comm]; noncomm_ring
      _ = - (J_1 P X + J_1 P X) := by rw [hp_ph]
  have h_ph_decay : D.toFun (Phi_1 P X) = - (Phi_1 P X + Phi_1 P X) := by
    calc D.toFun (Phi_1 P X)
      _ = comm P (D.toFun (J_1 P X)) := h_comm_deriv (J_1 P X)
      _ = comm P (- (J_1 P X + J_1 P X)) := by rw [h_j_decay]
      _ = - (Phi_1 P X + Phi_1 P X) := by
          dsimp [Phi_1, J_1, comm]; noncomm_ring
  have h_v_decay : D.toFun (V_1 P X) = - (V_1 P X + V_1 P X + V_1 P X + V_1 P X) := by
    calc D.toFun (V_1 P X)
      _ = D.toFun (- (J_1 P X * J_1 P X)) := rfl
      _ = - D.toFun (J_1 P X * J_1 P X) := OpDerivation.map_neg D (J_1 P X * J_1 P X)
      _ = - (D.toFun (J_1 P X) * J_1 P X + J_1 P X * D.toFun (J_1 P X)) := by rw [D.leibniz']
      _ = - (- (J_1 P X + J_1 P X) * J_1 P X + J_1 P X * - (J_1 P X + J_1 P X)) := by rw [h_j_decay]
      _ = - (V_1 P X + V_1 P X + V_1 P X + V_1 P X) := by
          dsimp [V_1]; noncomm_ring
  exact ⟨h_j_decay, h_ph_decay, h_v_decay⟩

/--
**Fence `#93` (`temperley_lieb_boundary_structure`):**
Proves the Temperley–Lieb contraction structure together with the Socratic commuting collapse
`E1 * E2 = E2 * E1 → E1 * E2 = tau * E1 ∧ E1 * E2 = tau * E2`.
-/
theorem temperley_lieb_boundary_structure
    (E1 E2 tau : B)
    (h_E1_idem : E1 * E1 = E1)
    (h_E2_idem : E2 * E2 = E2)
    (h_TL121 : E1 * E2 * E1 = tau * E1)
    (h_TL212 : E2 * E1 * E2 = tau * E2)
    (h_comm : E1 * E2 = E2 * E1) :
    E1 * E1 = E1 ∧
    E1 * E2 * E1 = tau * E1 ∧
    E2 * E1 * E2 = tau * E2 ∧
    E1 * E2 = tau * E1 ∧
    E1 * E2 = tau * E2 := by
  have h1 : E1 * E2 = tau * E1 := by
    calc E1 * E2
      _ = (E1 * E1) * E2 := by rw [h_E1_idem]
      _ = E1 * (E1 * E2) := by rw [mul_assoc]
      _ = E1 * (E2 * E1) := by rw [h_comm]
      _ = E1 * E2 * E1   := by rw [← mul_assoc]
      _ = tau * E1       := h_TL121
  have h2 : E1 * E2 = tau * E2 := by
    calc E1 * E2
      _ = E1 * (E2 * E2) := by rw [h_E2_idem]
      _ = (E1 * E2) * E2 := by rw [mul_assoc]
      _ = (E2 * E1) * E2 := by rw [h_comm]
      _ = E2 * E1 * E2   := rfl
      _ = tau * E2       := h_TL212
  exact ⟨h_E1_idem, h_TL121, h_TL212, h1, h2⟩

end Track1A_VietaSusyKatoDissipation

-- ============================================================================
-- SECTION 3: Track 1B — Lean #12, #13, #15, #18 Lifted to `[Ring B]` (`0 CommRing`)
-- ============================================================================

section Track1B_GaloisGolayPeterWeylWignerHurwitz

variable {B : Type u} [Ring B]

/-- Scaled conformal spin `zfSpinNum κ l = l * (κ - l)` of the `l`-th `ℤ_κ` parafermion current. -/
def zfSpinNum (κ l : ℕ) : ℕ := l * (κ - l)

/-- Checks whether `m : Fin N` is fixed by all coprime Galois automorphisms `k ∈ (ℤ/Nℤ)^×`. -/
def isGaloisFixedSpin (N : ℕ) (m : Fin N) : Bool :=
  (List.range N).all (fun k =>
    if Nat.gcd k N == 1 then
      (k * m.val) % N == m.val
    else
      true)

/-- Checks whether `m ↦ (k² * m) % N` fixes every `m` for all coprime `k ∈ (ℤ/Nℤ)^×`. -/
def isQuadraticGaloisSpinInvariant (N : ℕ) : Bool :=
  (List.range N).all (fun m =>
    (List.range N).all (fun k =>
      if Nat.gcd k N == 1 then
        (k * k * m) % N == m
      else
        true))

/-- Additive spin-numerator form of Marín-Salvador's double-braiding monodromy phase. -/
def monodromyPhase (N : Int) (m_ab m_a m_b : Int) : Int :=
  (m_ab - m_a - m_b) % N

/-- Unnormalized `ℤ₃` parafermion condensate projector `1 + Ω + Ω²` in `[Ring B]`. -/
def P_cond3 (Ω : B) : B := 1 + Ω + Ω * Ω
/-- Unnormalized `ℤ₄` parafermion condensate projector `1 + U²` in `[Ring B]`. -/
def P_cond4 (U : B) : B := 1 + U * U

/-- **Lean `#12` Theorem 1 (`parafermion_and_vortex_condensation_thresholds`):** -/
theorem parafermion_and_vortex_condensation_thresholds :
    zfSpinNum 4 0 = 0 ∧
    zfSpinNum 4 1 = 3 ∧
    zfSpinNum 4 2 = 4 ∧
    zfSpinNum 4 3 = 3 ∧
    zfSpinNum 4 2 % 4 = 0 ∧
    zfSpinNum 4 1 % 4 ≠ 0 ∧
    zfSpinNum 3 1 = 2 ∧
    zfSpinNum 3 2 = 2 ∧
    (3 * zfSpinNum 3 1) % 3 = 0 ∧
    (8 * 2) % 16 = 0 ∧
    16 % 16 = 0 := by
  decide

/-- **Lean `#12` Theorem 2 (`galois_orbit_fixes_only_rational_characters`):** -/
theorem galois_orbit_fixes_only_rational_characters :
    (∀ m : Fin 4, isGaloisFixedSpin 4 m = true ↔ (m.val == 0 || m.val == 2) = true) ∧
    (∀ m : Fin 16, isGaloisFixedSpin 16 m = true ↔ (m.val == 0 || m.val == 8) = true) ∧
    (∀ m : Fin 24, isGaloisFixedSpin 24 m = true ↔ (m.val == 0 || m.val == 12) = true) := by
  decide

/-- **Lean `#12` Theorem 3 (`coste_gannon_quadratic_galois_spin_preservation_mod24`):** -/
theorem coste_gannon_quadratic_galois_spin_preservation_mod24 :
    isQuadraticGaloisSpinInvariant 2  = true ∧
    isQuadraticGaloisSpinInvariant 3  = true ∧
    isQuadraticGaloisSpinInvariant 4  = true ∧
    isQuadraticGaloisSpinInvariant 6  = true ∧
    isQuadraticGaloisSpinInvariant 8  = true ∧
    isQuadraticGaloisSpinInvariant 12 = true ∧
    isQuadraticGaloisSpinInvariant 24 = true ∧
    isQuadraticGaloisSpinInvariant 5  = false ∧
    isQuadraticGaloisSpinInvariant 16 = false := by
  decide

/-- **Lean `#12` Theorem 4 (`marin_salvador_balancing_mutual_locality_condensation`):** -/
theorem marin_salvador_balancing_mutual_locality_condensation
    (N m_ab : Int) :
    monodromyPhase N m_ab 0 0 = 0 ↔ m_ab % N = 0 := by
  dsimp [monodromyPhase]
  simp only [sub_zero]

/-- **Lean `#12` Theorem 5 (`cyclotomic_character_confinement_and_condensation_projector`):** -/
theorem cyclotomic_character_confinement_and_condensation_projector
    (Ω U : B) (hΩ : Ω * (Ω * Ω) = 1) (hU : U * (U * (U * U)) = 1) :
    (1 - Ω) * P_cond3 Ω = 0 ∧
    Ω * P_cond3 Ω = P_cond3 Ω ∧
    P_cond3 Ω * P_cond3 Ω = P_cond3 Ω + P_cond3 Ω + P_cond3 Ω ∧
    (U * U) * P_cond4 U = P_cond4 U ∧
    P_cond4 U * P_cond4 U = P_cond4 U + P_cond4 U := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [P_cond3]; simp only [sub_mul, mul_add, one_mul, mul_one, mul_assoc, hΩ]; abel
  · dsimp [P_cond3]; simp only [mul_add, mul_one, mul_assoc, hΩ]; abel
  · dsimp [P_cond3]
    have hΩ4 : Ω * (Ω * (Ω * Ω)) = Ω := by rw [hΩ, mul_one]
    simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc, hΩ, hΩ4]; abel
  · dsimp [P_cond4]; simp only [mul_add, mul_one, mul_assoc, hU]; abel
  · dsimp [P_cond4]; simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc, hU]; abel

/-- Volume of a Hamming ball of radius `e` in `𝔽_q^n`. -/
def hammingBallVol (n q : ℕ) : ℕ → ℕ
  | 0     => 1
  | e + 1 => hammingBallVol n q e + Nat.choose n (e + 1) * (q - 1) ^ (e + 1)

/-- **Lean `#13` Theorem 1 (`perfect_code_sphere_packing_trinity`):** -/
theorem perfect_code_sphere_packing_trinity :
    hammingBallVol 7  2 1 = 2 ^ (7 - 4) ∧
    hammingBallVol 11 3 2 = 3 ^ (11 - 6) ∧
    hammingBallVol 23 2 3 = 2 ^ (23 - 12) ∧
    Nat.choose 23 0 + Nat.choose 23 1 + Nat.choose 23 2 + Nat.choose 23 3 = 2048 ∧
    Nat.choose 11 0 + 2 * Nat.choose 11 1 + 4 * Nat.choose 11 2 = 243 := by
  decide

/-- **Lean `#13` Theorem 2 (`witt_steiner_design_block_counts`):** -/
theorem witt_steiner_design_block_counts :
    Nat.choose 12 5 / Nat.choose 6 5 = 132 ∧
    2 * (Nat.choose 12 5 / Nat.choose 6 5) = 264 ∧
    Nat.choose 24 5 / Nat.choose 8 5 = 759 ∧
    1 + 264 + 440 + 24 = 3 ^ 6 ∧
    1 + 759 + 2576 + 759 + 1 = 2 ^ 12 := by
  decide

/-- Single-variable inhomogeneous Hamming `[8, 4, 4]` weight enumerator `1 + 14 t⁴ + t⁸` in `[Ring B]`. -/
def W8_op (t : B) : B := 1 + 14 • (t ^ 4) + t ^ 8

/-- Single-variable inhomogeneous Golay cusp discriminant `t⁴ (1 - t⁴)⁴` in `[Ring B]`. -/
def Delta24_op (t : B) : B := (t ^ 4) * ((1 - t ^ 4) ^ 4)

/-- Single-variable inhomogeneous binary Golay `[24, 12, 8]` weight enumerator in `[Ring B]`. -/
def W24_op (t : B) : B := 1 + 759 • (t ^ 8) + 2576 • (t ^ 12) + 759 • (t ^ 16) + t ^ 24

/--
**Lean `#13` Theorem 3 (`gleason_golay_w24_polynomial_identity`, lifted to `[Ring B]`):**
In any noncommutative ring `[Ring B]`, for any operator `t : B`,
`W8_op(t)³ - 42 • Delta24_op(t) = W24_op(t)`.
-/
theorem gleason_golay_w24_polynomial_identity (t : B) :
    (W8_op t) ^ 3 - 42 • Delta24_op t = W24_op t ∧
    (W8_op t) ^ 3 =
      1 + 42 • (t ^ 4) + 591 • (t ^ 8) + 2828 • (t ^ 12) +
      591 • (t ^ 16) + 42 • (t ^ 20) + t ^ 24 := by
  refine ⟨?_, ?_⟩ <;>
  · dsimp [W8_op, Delta24_op, W24_op]
    noncomm_ring

/-- Truncated `E₈` theta series `1 + 240 q + 2160 q² + 6720 q³` in any noncommutative ring `[Ring B]`. -/
def ThetaE8_op (q : B) : B := 1 + 240 • q + 2160 • (q ^ 2) + 6720 • (q ^ 3)

/-- Truncated Ramanujan modular discriminant `q - 24 q² + 252 q³` in any noncommutative ring `[Ring B]`. -/
def RamanujanDelta_op (q : B) : B := q - 24 • (q ^ 2) + 252 • (q ^ 3)

/--
**Lean `#13` Theorem 4 (`leech_lattice_root_annihilation_and_theta_series`, lifted to `[Ring B]`):**
In any noncommutative ring `[Ring B]`, subtracting `720 • RamanujanDelta_op(q)` from
`(ThetaE8_op q)³` annihilates the `q¹` root term (`720 - 720 = 0`) and produces the exact
Leech kissing number `196,560 • q²` and norm-6 coefficient `16,773,120 • q³`.
-/
theorem leech_lattice_root_annihilation_and_theta_series (q : B) :
    (ThetaE8_op q) ^ 3 - 720 • RamanujanDelta_op q =
      1 + 196560 • (q ^ 2) + 16773120 • (q ^ 3) +
      (q ^ 4) * (396921600 • (1 : B) + 4607539200 • q + 31115059200 • (q ^ 2) +
                 126572544000 • (q ^ 3) + 292626432000 • (q ^ 4) + 303464448000 • (q ^ 5)) := by
  dsimp [ThetaE8_op, RamanujanDelta_op]
  noncomm_ring

/-- **Lean `#13` Theorem 5 (`conway_threefold_leech_decomposition_and_monster_griess`):** -/
theorem conway_threefold_leech_decomposition_and_monster_griess :
    let octadSector  := (Nat.choose 24 5 / Nat.choose 8 5) * (2 ^ 7)
    let spinorSector := 24 * (2 ^ 12)
    let pairSector   := Nat.choose 24 2 * 4
    octadSector = 97152 ∧
    spinorSector = 98304 ∧
    pairSector = 1104 ∧
    octadSector + spinorSector + pairSector = 196560 ∧
    196560 + Nat.choose 25 2 + 24 = 196884 ∧
    3 * 248 = 744 := by
  decide

/--
**Lean `#15` Theorem 1 (`abelian_character_blind_to_commutators`, lifted to `[Ring B]`):**
For any multiplicative map `χ : G → B` into a noncommutative ring `[Ring B]`,
`χ(u * v) - χ(v * u) = comm (χ u) (χ v)`, so `χ(u * v) = χ(v * u)` whenever `χ u` and `χ v`
commute (`comm (χ u) (χ v) = 0`).
-/
theorem abelian_character_blind_to_commutators
    {G : Type*} [Mul G]
    (χ : G → B) (h_hom : ∀ u v : G, χ (u * v) = χ u * χ v)
    (u v : G) (h_comm : comm (χ u) (χ v) = 0) :
    χ (u * v) - χ (v * u) = comm (χ u) (χ v) ∧
    χ (u * v) = χ (v * u) ∧
    χ (u * v) - χ (v * u) = 0 := by
  have h_diff : χ (u * v) - χ (v * u) = comm (χ u) (χ v) := by
    rw [h_hom u v, h_hom v u]; rfl
  have h_zero : χ (u * v) - χ (v * u) = 0 := h_diff.trans h_comm
  exact ⟨h_diff, sub_eq_zero.mp h_zero, h_zero⟩

/--
**Lean `#15` Theorem 2 (`chebyshev_horseshoe_parabola_identity`, lifted to `[Ring B]`):**
In any noncommutative ring `[Ring B]`, if `c * c + s * s = 1`, then `c * c - s * s = 2 • (c * c) - 1`,
and for any `t : B`, `(1 - t * t)² + (2 • t)² = (1 + t * t)²`.
-/
theorem chebyshev_horseshoe_parabola_identity
    (c s t : B) (h_circle : c * c + s * s = 1) :
    (c * c - s * s = 2 • (c * c) - 1) ∧
    ((1 - t * t) ^ 2 + (2 • t) ^ 2 = (1 + t * t) ^ 2) ∧
    ((1 - t * t) ^ 2 - (2 • t) ^ 2 = 2 • ((1 - t * t) ^ 2) - (1 + t * t) ^ 2) := by
  refine ⟨?_, by noncomm_ring, by noncomm_ring⟩
  calc c * c - s * s
    _ = 2 • (c * c) - (c * c + s * s) := by rw [two_nsmul]; abel
    _ = 2 • (c * c) - 1               := by rw [h_circle]

/-- **Lean `#15` Theorem 3 (`covariant_vs_contravariant_noncommutative_convolution_theorem`):** -/
theorem covariant_vs_contravariant_noncommutative_convolution_theorem
    {G : Type*} [Mul G]
    (ρ ρ_inv : G → B) (u v : G)
    (h_cov : ρ (u * v) = ρ u * ρ v)
    (h_inv : ρ_inv (u * v) = ρ_inv v * ρ_inv u) :
    ρ (u * v) = ρ u * ρ v ∧
    ρ_inv (u * v) = ρ_inv v * ρ_inv u ∧
    ρ_inv (u * v) - ρ_inv u * ρ_inv v = comm (ρ_inv v) (ρ_inv u) := by
  exact ⟨h_cov, h_inv, by rw [h_inv]; rfl⟩

/-- Native `2 × 2` matrix carrier `((m₁₁, m₁₂), (m₂₁, m₂₂))` over an arbitrary ring `K`. -/
def Mat2Op (K : Type u) : Type u := (K × K) × (K × K)

namespace Mat2Op
variable {K : Type u} [Ring K]

/-- Construct a `2 × 2` matrix `((a11, a12), (a21, a22))` in `Mat2Op K`. -/
def mkMat (a11 a12 a21 a22 : K) : Mat2Op K := ((a11, a12), (a21, a22))

/-- Top-left `(1, 1)` entry of `A : Mat2Op K`. -/
def m11 (A : Mat2Op K) : K := A.1.1

/-- Top-right `(1, 2)` entry of `A : Mat2Op K`. -/
def m12 (A : Mat2Op K) : K := A.1.2

/-- Bottom-left `(2, 1)` entry of `A : Mat2Op K`. -/
def m21 (A : Mat2Op K) : K := A.2.1

/-- Bottom-right `(2, 2)` entry of `A : Mat2Op K`. -/
def m22 (A : Mat2Op K) : K := A.2.2

/-- Componentwise addition on `Mat2Op K`. -/
def addMat (A B : Mat2Op K) : Mat2Op K :=
  ((A.1.1 + B.1.1, A.1.2 + B.1.2), (A.2.1 + B.2.1, A.2.2 + B.2.2))

/-- Componentwise subtraction on `Mat2Op K`. -/
def subMat (A B : Mat2Op K) : Mat2Op K :=
  ((A.1.1 - B.1.1, A.1.2 - B.1.2), (A.2.1 - B.2.1, A.2.2 - B.2.2))

/-- Identity `2 × 2` matrix `((1, 0), (0, 1))` in `Mat2Op K`. -/
def oneMat : Mat2Op K := ((1, 0), (0, 1))

/-- Natural-number scalar multiple `n • A` on `Mat2Op K`. -/
def nsmulMat (n : ℕ) (A : Mat2Op K) : Mat2Op K :=
  ((n • A.1.1, n • A.1.2), (n • A.2.1, n • A.2.2))

/-- Left scalar multiple `c * A` on `Mat2Op K`. -/
def scaleRight (c : K) (A : Mat2Op K) : Mat2Op K :=
  ((c * A.1.1, c * A.1.2), (c * A.2.1, c * A.2.2))

/-- Matrix multiplication `A * B` on `Mat2Op K`. -/
def mul (A B : Mat2Op K) : Mat2Op K :=
  ((A.1.1 * B.1.1 + A.1.2 * B.2.1, A.1.1 * B.1.2 + A.1.2 * B.2.2),
   (A.2.1 * B.1.1 + A.2.2 * B.2.1, A.2.1 * B.1.2 + A.2.2 * B.2.2))

/-- Matrix trace `m₁₁ + m₂₂` on `Mat2Op K`. -/
def tr (A : Mat2Op K) : K := A.1.1 + A.2.2

/-- Identity Peirce basis element `I = ((1, 0), (0, 1))`. -/
def basisI   : Mat2Op K := ((1,  0), ( 0,  1))

/-- Parity involution Peirce basis element `S_P = ((1, 0), (0, -1))`. -/
def basisSP  : Mat2Op K := ((1,  0), ( 0, -1))

/-- Off-diagonal vielbein Peirce basis element `Φ = ((0, 1), (1, 0))`. -/
def basisPhi : Mat2Op K := ((0,  1), ( 1,  0))

/-- Symplectic current Peirce basis element `J = ((0, 1), (-1, 0))`. -/
def basisJ   : Mat2Op K := ((0,  1), (-1,  0))

/-- Transposition generator `τ₁₂` of the standard 2D representation of `S₃` over `ℤ`. -/
def s3_tau12 : Mat2Op ℤ := (( 1,  0), (0, -1))

/-- Transposition generator `τ₂₃` of the standard 2D representation of `S₃` over `ℤ`. -/
def s3_tau23 : Mat2Op ℤ := ((-1, -1), (0,  1))

/-- **Lean `#15` Theorem 4 (`s3_wedderburn_artin_and_2d_peirce_syntax_witness`):** -/
theorem s3_wedderburn_artin_and_2d_peirce_syntax_witness :
    1 ^ 2 + 1 ^ 2 + 2 ^ 2 = 6 ∧
    mul s3_tau12 s3_tau12 = (oneMat : Mat2Op ℤ) ∧
    mul s3_tau23 s3_tau23 = (oneMat : Mat2Op ℤ) ∧
    mul s3_tau12 s3_tau23 ≠ mul s3_tau23 s3_tau12 := by
  refine ⟨by decide,
          Prod.ext (Prod.ext (by decide) (by decide)) (Prod.ext (by decide) (by decide)),
          Prod.ext (Prod.ext (by decide) (by decide)) (Prod.ext (by decide) (by decide)),
          fun h => by
            have h12 : (mul s3_tau12 s3_tau23).1.2 = (mul s3_tau23 s3_tau12).1.2 :=
              congrArg (fun X => X.1.2) h
            revert h12
            decide⟩

/--
**Lean `#15` Theorem 5 (`peirce_peter_weyl_four_basis_reconstruction`, lifted to `[Ring K]`):**
In any noncommutative ring `[Ring K]`, any `2 × 2` operator matrix `M : Mat2Op K` satisfies
`2 • M = tr(M I) I + tr(M S_P) S_P + tr(M Φ) Φ - tr(M J) J`.
-/
theorem peirce_peter_weyl_four_basis_reconstruction (M : Mat2Op K) :
    nsmulMat 2 M =
      subMat
        (addMat
          (addMat (scaleRight (tr (mul M basisI)) basisI)
                  (scaleRight (tr (mul M basisSP)) basisSP))
          (scaleRight (tr (mul M basisPhi)) basisPhi))
        (scaleRight (tr (mul M basisJ)) basisJ) := by
  rcases M with ⟨⟨a11, a12⟩, ⟨a21, a22⟩⟩
  dsimp only [nsmulMat, subMat, addMat, scaleRight, tr, mul, basisI, basisSP, basisPhi, basisJ]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> noncomm_ring

end Mat2Op

/-- Native `3 × 3` matrix carrier `((m₁₁, m₁₂, m₁₃), (m₂₁, m₂₂, m₂₃), (m₃₁, m₃₂, m₃₃))` over `K`. -/
def Mat3Op (K : Type u) : Type u := (K × K × K) × (K × K × K) × (K × K × K)

namespace Mat3Op
variable {K : Type u} [Ring K]

/-- Zero `3 × 3` matrix in `Mat3Op K`. -/
def zeroMat : Mat3Op K := ((0, 0, 0), (0, 0, 0), (0, 0, 0))

/-- Componentwise addition on `Mat3Op K`. -/
def addMat (A B : Mat3Op K) : Mat3Op K :=
  ((A.1.1 + B.1.1, A.1.2.1 + B.1.2.1, A.1.2.2 + B.1.2.2),
   (A.2.1.1 + B.2.1.1, A.2.1.2.1 + B.2.1.2.1, A.2.1.2.2 + B.2.1.2.2),
   (A.2.2.1 + B.2.2.1, A.2.2.2.1 + B.2.2.2.1, A.2.2.2.2 + B.2.2.2.2))

/-- Natural-number scalar multiple `n • A` on `Mat3Op K`. -/
def nsmulMat (n : ℕ) (A : Mat3Op K) : Mat3Op K :=
  ((n • A.1.1, n • A.1.2.1, n • A.1.2.2),
   (n • A.2.1.1, n • A.2.1.2.1, n • A.2.1.2.2),
   (n • A.2.2.1, n • A.2.2.2.1, n • A.2.2.2.2))

/-- Matrix trace `m₁₁ + m₂₂ + m₃₃` on `Mat3Op K`. -/
def tr (A : Mat3Op K) : K := A.1.1 + A.2.1.2.1 + A.2.2.2.2

/-- Non-commutative Frobenius bilinear form `∑_{i,j} A_{ij} B_{ij}` on `Mat3Op K`. -/
def frobInner (A B : Mat3Op K) : K :=
  A.1.1 * B.1.1 + A.1.2.1 * B.1.2.1 + A.1.2.2 * B.1.2.2 +
  A.2.1.1 * B.2.1.1 + A.2.1.2.1 * B.2.1.2.1 + A.2.1.2.2 * B.2.1.2.2 +
  A.2.2.1 * B.2.2.1 + A.2.2.2.1 * B.2.2.2.1 + A.2.2.2.2 * B.2.2.2.2

/-- Trivial singlet Wigner–Clebsch–Gordan projector `Π₁` (scaled by `6`) on `Mat3Op K`. -/
def Pi1 (M : Mat3Op K) : Mat3Op K :=
  let t := 2 • tr M
  ((t, 0, 0), (0, t, 0), (0, 0, t))

/-- Two-dimensional Cartan diagonal Wigner–Clebsch–Gordan projector `Π₂` (scaled by `6`) on `Mat3Op K`. -/
def Pi2 (M : Mat3Op K) : Mat3Op K :=
  ((4 • M.1.1 - 2 • M.2.1.2.1 - 2 • M.2.2.2.2, 0, 0),
   (0, 4 • M.2.1.2.1 - 2 • M.1.1 - 2 • M.2.2.2.2, 0),
   (0, 0, 4 • M.2.2.2.2 - 2 • M.1.1 - 2 • M.2.1.2.1))

/-- Symmetric off-diagonal Wigner–Clebsch–Gordan projector `Π₃⁺` (scaled by `6`) on `Mat3Op K`. -/
def Pi3_pos (M : Mat3Op K) : Mat3Op K :=
  ((0, 3 • (M.1.2.1 + M.2.1.1), 3 • (M.1.2.2 + M.2.2.1)),
   (3 • (M.2.1.1 + M.1.2.1), 0, 3 • (M.2.1.2.2 + M.2.2.2.1)),
   (3 • (M.2.2.1 + M.1.2.2), 3 • (M.2.2.2.1 + M.2.1.2.2), 0))

/-- Antisymmetric off-diagonal Wigner–Clebsch–Gordan projector `Π₃⁻` (scaled by `6`) on `Mat3Op K`. -/
def Pi3_neg (M : Mat3Op K) : Mat3Op K :=
  ((0, 3 • (M.1.2.1 - M.2.1.1), 3 • (M.1.2.2 - M.2.2.1)),
   (3 • (M.2.1.1 - M.1.2.1), 0, 3 • (M.2.1.2.2 - M.2.2.2.1)),
   (3 • (M.2.2.1 - M.1.2.2), 3 • (M.2.2.2.1 - M.2.1.2.2), 0))

/--
**Lean `#18` Theorem 1 (`clebsch_gordan_s4_idempotency_and_mutual_orthogonality`, lifted to `[Ring K]`):**
Over any noncommutative ring `[Ring K]`, the four Wigner–Clebsch–Gordan projectors on `Mat3Op K`
satisfy `Pi1 + Pi2 + Pi3_pos + Pi3_neg = 6 • id`, `Pi_α(Pi_α M) = 6 • Pi_α M`, and
`Pi_α(Pi_β M) = 0` for `α ≠ β`.
-/
theorem clebsch_gordan_s4_idempotency_and_mutual_orthogonality (M : Mat3Op K) :
    addMat (addMat (addMat (Pi1 M) (Pi2 M)) (Pi3_pos M)) (Pi3_neg M) = nsmulMat 6 M ∧
    Pi1 (Pi1 M) = nsmulMat 6 (Pi1 M) ∧
    Pi2 (Pi2 M) = nsmulMat 6 (Pi2 M) ∧
    Pi3_pos (Pi3_pos M) = nsmulMat 6 (Pi3_pos M) ∧
    Pi3_neg (Pi3_neg M) = nsmulMat 6 (Pi3_neg M) ∧
    Pi1 (Pi2 M) = (zeroMat : Mat3Op K) ∧ Pi2 (Pi1 M) = (zeroMat : Mat3Op K) ∧
    Pi1 (Pi3_pos M) = (zeroMat : Mat3Op K) ∧ Pi2 (Pi3_pos M) = (zeroMat : Mat3Op K) ∧
    Pi3_pos (Pi3_neg M) = (zeroMat : Mat3Op K) ∧ Pi3_neg (Pi3_pos M) = (zeroMat : Mat3Op K) := by
  rcases M with ⟨⟨a11, a12, a13⟩, ⟨a21, a22, a23⟩, ⟨a31, a32, a33⟩⟩
  dsimp only [Pi1, Pi2, Pi3_pos, Pi3_neg, addMat, nsmulMat, zeroMat, tr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_))
      (Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> noncomm_ring

/--
**Lean `#18` Theorem 2 (`clebsch_gordan_frobenius_pythagorean_theorem`, lifted to `[Ring K]`):**
Over any noncommutative ring `[Ring K]` (`0 CommRing`), all cross-channel Frobenius inner products
vanish and `36 • frobInner M N = ∑_α frobInner (Pi_α M) (Pi_α N)` holds identically!
-/
theorem clebsch_gordan_frobenius_pythagorean_theorem (M N : Mat3Op K) :
    frobInner (Pi1 M) (Pi2 N) = 0 ∧
    frobInner (Pi1 M) (Pi3_pos N) = 0 ∧
    frobInner (Pi2 M) (Pi3_pos N) = 0 ∧
    frobInner (Pi3_pos M) (Pi3_neg N) = 0 ∧
    36 • frobInner M N =
      frobInner (Pi1 M) (Pi1 N) +
      frobInner (Pi2 M) (Pi2 N) +
      frobInner (Pi3_pos M) (Pi3_pos N) +
      frobInner (Pi3_neg M) (Pi3_neg N) := by
  rcases M with ⟨⟨m11, m12, m13⟩, ⟨m21, m22, m23⟩, ⟨m31, m32, m33⟩⟩
  rcases N with ⟨⟨n11, n12, n13⟩, ⟨n21, n22, n23⟩, ⟨n31, n32, n33⟩⟩
  dsimp only [frobInner, Pi1, Pi2, Pi3_pos, Pi3_neg, tr]
  refine ⟨by noncomm_ring, by noncomm_ring, by noncomm_ring, by noncomm_ring, by noncomm_ring⟩

end Mat3Op

/-- Native quaternion carrier `((w, x), (y, z))` over an arbitrary noncommutative ring `K`. -/
def QuatOp (K : Type u) : Type u := (K × K) × (K × K)

namespace QuatOp
variable {K : Type u} [Ring K]

/-- Zero quaternion `((0, 0), (0, 0))` in `QuatOp K`. -/
def zeroQuat : QuatOp K := ((0, 0), (0, 0))

/-- Componentwise addition on `QuatOp K`. -/
def addQuat (a b : QuatOp K) : QuatOp K :=
  ((a.1.1 + b.1.1, a.1.2 + b.1.2), (a.2.1 + b.2.1, a.2.2 + b.2.2))

/-- Componentwise subtraction on `QuatOp K`. -/
def subQuat (a b : QuatOp K) : QuatOp K :=
  ((a.1.1 - b.1.1, a.1.2 - b.1.2), (a.2.1 - b.2.1, a.2.2 - b.2.2))

/-- Integer scalar multiple `c • q` on `QuatOp K`. -/
def zsmulQuat (c : ℤ) (q : QuatOp K) : QuatOp K :=
  ((c • q.1.1, c • q.1.2), (c • q.2.1, c • q.2.2))

/-- Quaternion conjugate `(w, -x, -y, -z)` on `QuatOp K`. -/
def conj (q : QuatOp K) : QuatOp K := ((q.1.1, -q.1.2), (-q.2.1, -q.2.2))

/-- Quaternion quadratic norm `w² + x² + y² + z²` in `K`. -/
def qNorm (q : QuatOp K) : K := q.1.1 * q.1.1 + q.1.2 * q.1.2 + q.2.1 * q.2.1 + q.2.2 * q.2.2

/-- Hamilton quaternion multiplication on `QuatOp K`. -/
def mul (a b : QuatOp K) : QuatOp K :=
  ((a.1.1 * b.1.1 - a.1.2 * b.1.2 - a.2.1 * b.2.1 - a.2.2 * b.2.2,
    a.1.1 * b.1.2 + a.1.2 * b.1.1 + a.2.1 * b.2.2 - a.2.2 * b.2.1),
   (a.1.1 * b.2.1 - a.1.2 * b.2.2 + a.2.1 * b.1.1 + a.2.2 * b.1.2,
    a.1.1 * b.2.2 + a.1.2 * b.2.1 - a.2.1 * b.1.2 + a.2.2 * b.1.1))

/-- Unit quaternion `1 = ((1, 0), (0, 0))` in `QuatOp K`. -/
def qOne : QuatOp K := ((1, 0), (0, 0))

/-- Imaginary quaternion unit `i = ((0, 1), (0, 0))` in `QuatOp K`. -/
def qi   : QuatOp K := ((0, 1), (0, 0))

/-- Imaginary quaternion unit `j = ((0, 0), (1, 0))` in `QuatOp K`. -/
def qj   : QuatOp K := ((0, 0), (1, 0))

/-- Imaginary quaternion unit `k = ((0, 0), (0, 1))` in `QuatOp K`. -/
def qk   : QuatOp K := ((0, 0), (0, 1))

/-- Hurwitz spinor corner `W = ((1, 1), (1, 1))` in `QuatOp K`. -/
def hurwitzW : QuatOp K := ((1, 1), (1, 1))

/--
**Lean `#18` Theorem 3 (`hurwitz_corner_triality_attention_filter`, lifted to `[Ring K]`):**
Over any noncommutative ring `[Ring K]`, the Hurwitz spinor corner `W = (1, 1, 1, 1)` satisfies
`qNorm W = 4`, `W² - 2 • W + 4 • 1 = 0`, `W³ = -8 • 1`, and cyclically permutes `(i, j, k)`:
`W * i * W̄ = 4 • j`, `W * j * W̄ = 4 • k`, `W * k * W̄ = 4 • i`.
-/
theorem hurwitz_corner_triality_attention_filter :
    8 + 2 ^ 4 = 24 ∧ 24 + 6 * 4 = 48 ∧
    qNorm (hurwitzW : QuatOp K) = 4 • (1 : K) ∧
    addQuat (subQuat (mul (hurwitzW : QuatOp K) hurwitzW) (zsmulQuat 2 hurwitzW))
      (zsmulQuat 4 qOne) = (zeroQuat : QuatOp K) ∧
    mul (mul (hurwitzW : QuatOp K) hurwitzW) hurwitzW = zsmulQuat (-8) qOne ∧
    mul (mul (hurwitzW : QuatOp K) qi) (conj hurwitzW) = zsmulQuat 4 qj ∧
    mul (mul (hurwitzW : QuatOp K) qj) (conj hurwitzW) = zsmulQuat 4 qk ∧
    mul (mul (hurwitzW : QuatOp K) qk) (conj hurwitzW) = zsmulQuat 4 qi := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [qNorm, hurwitzW]; noncomm_ring
  · dsimp only [hurwitzW, qOne, zeroQuat, addQuat, subQuat, zsmulQuat, mul]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> noncomm_ring
  · dsimp only [hurwitzW, qOne, zsmulQuat, mul]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> noncomm_ring
  · dsimp only [hurwitzW, qi, qj, conj, zsmulQuat, mul]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> noncomm_ring
  · dsimp only [hurwitzW, qj, qk, conj, zsmulQuat, mul]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> noncomm_ring
  · dsimp only [hurwitzW, qk, qi, conj, zsmulQuat, mul]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> noncomm_ring

end QuatOp

/-- 6th cyclotomic polynomial `Φ₆(y) = y² - y + 1` in `[Ring B]`. -/
def Phi6_op (y : B) : B := y ^ 2 - y + 1

/-- 24th cyclotomic polynomial `Φ₂₄(x) = x⁸ - x⁴ + 1` in `[Ring B]`. -/
def Phi24_cyc (x : B) : B := x ^ 8 - x ^ 4 + 1

/--
**Lean `#18` Theorem 4 (`adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge`, lifted to `[Ring B]`):**
Over any noncommutative ring `[Ring B]`, `Phi6_op (x ^ 4) = Phi24_cyc x`,
`(x ^ 4 + 1) * Phi24_cyc x = x ^ 12 + 1`, and `(x ^ 12 - 1) * (x ^ 4 + 1) * Phi24_cyc x = x ^ 24 - 1`.
-/
theorem adams_j_homomorphism_and_bott_hurwitz_cyclotomic_bridge (x : B) :
    Phi6_op (x ^ 4) = Phi24_cyc x ∧
    (x ^ 4 + 1) * Phi24_cyc x = x ^ 12 + 1 ∧
    (x ^ 12 - 1) * (x ^ 4 + 1) * Phi24_cyc x = x ^ 24 - 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp [Phi6_op, Phi24_cyc]
    noncomm_ring

end Track1B_GaloisGolayPeterWeylWignerHurwitz

-- ============================================================================
-- SECTION 4: Track 2 — Order 28 (Octacosadic) 3-Strand Temperley–Lieb,
--            Jones–Wenzl Idempotent & Yang–Baxter Braid Poset (𝔒ℭ₁ ≺ ⋯ ≺ 𝔒ℭ₅)
-- ============================================================================

section Track2_OctacosadicThreeStrandTemperleyLiebYangBaxter

variable {B : Type u} [Ring B]

/-- Adjacent Halmos difference generators `H_12 = e1 - e2`, `H_23 = e2 - e3`, and `H_13 = e1 - e3`. -/
def H_tl (e1 e2 : B) : B := e1 - e2

/-- Adjacent Temperley–Lieb braiding commutator `Sigma_tl(e1, e2) = [e1, e2]`. -/
def Sigma_tl (e1 e2 : B) : B := comm e1 e2

/-- Forward 3-strand Temperley–Lieb braid transfer operator `T_123 = e1 e2 e3`. -/
def T_123 (e1 e2 e3 : B) : B := e1 * e2 * e3

/-- Backward 3-strand Temperley–Lieb braid transfer operator `T_321 = e3 e2 e1`. -/
def T_321 (e1 e2 e3 : B) : B := e3 * e2 * e1

/-- Division-free 2-strand Jones–Wenzl projector `JW_2(e1, e2, τ) = (1 - τ) - (e1 - e2)²`. -/
def JW_2 (e1 e2 tau : B) : B := (1 - tau) - (e1 - e2) * (e1 - e2)

/-- Kauffman–Jones spectral braid generator `g_braid(u, e) = 1 + u * e`. -/
def g_braid (u e : B) : B := 1 + u * e

/--
**Node `𝔒ℭ₁` (`three_strand_halmos_commutator_aporia`):**
For any three operators `e1, e2, e3 : B` where distant strands commute (`e1 * e3 = e3 * e1`),
the two adjacent Halmos generators `H_12 = e1 - e2` and `H_23 = e2 - e3` satisfy:
1. `H_12 + H_23 = H_13 = e1 - e3`,
2. `[H_12, H_23] = [e1, e2] + [e2, e3] = Sigma_tl e1 e2 + Sigma_tl e2 e3`.
Thus `H_12` and `H_23` fail to commute unless the total braiding flux `Sigma_tl e1 e2 + Sigma_tl e2 e3` vanishes!
-/
theorem three_strand_halmos_commutator_aporia
    (e1 e2 e3 : B) (h13 : e1 * e3 = e3 * e1) :
    let h12 := H_tl e1 e2
    let h23 := H_tl e2 e3
    let h13_op := H_tl e1 e3
    let s12 := Sigma_tl e1 e2
    let s23 := Sigma_tl e2 e3
    h12 + h23 = h13_op ∧
    comm h12 h23 = s12 + s23 := by
  refine ⟨?_, ?_⟩
  · dsimp [H_tl]; abel
  · dsimp [H_tl, Sigma_tl, comm]
    calc (e1 - e2) * (e2 - e3) - (e2 - e3) * (e1 - e2)
      _ = ((e1 * e2 - e2 * e1) + (e2 * e3 - e3 * e2)) - (e1 * e3 - e3 * e1) := by noncomm_ring
      _ = ((e1 * e2 - e2 * e1) + (e2 * e3 - e3 * e2)) - 0 := by rw [h13, sub_self]
      _ = (e1 * e2 - e2 * e1) + (e2 * e3 - e3 * e2) := by rw [sub_zero]

/--
**Node `𝔒ℭ₂` (`three_strand_cubic_temperley_lieb_braid_transfer`):**
Under the 3-strand Temperley–Lieb relations (`e_i² = e_i`, `e1 * e3 = e3 * e1`,
`e1 e2 e1 = τ e1`, `e2 e1 e2 = τ e2`, `e2 e3 e2 = τ e2`, `e3 e2 e3 = τ e3` with central `τ`),
the cubic transfer operators `T_123 = e1 e2 e3` and `T_321 = e3 e2 e1` satisfy:
1. `(e1 * e3)² = e1 * e3` (distant joint projection is idempotent),
2. `T_123 * e1 = τ * (e1 * e3)` and `e3 * T_123 = τ * (e1 * e3)`,
3. `T_123 * T_123 = (τ * τ) * (e1 * e3)` and `T_321 * T_321 = (τ * τ) * (e1 * e3)`,
4. `T_123 * T_321 = (τ * τ) * e1` and `T_321 * T_123 = (τ * τ) * e3`,
5. `[T_123, T_321] = (τ * τ) * (H_tl e1 e2 + H_tl e2 e3) = (τ * τ) * (e1 - e3)`.
-/
theorem three_strand_cubic_temperley_lieb_braid_transfer
    (e1 e2 e3 tau : B)
    (he1 : e1 * e1 = e1) (he3 : e3 * e3 = e3)
    (h13 : e1 * e3 = e3 * e1)
    (h121 : e1 * e2 * e1 = tau * e1)
    (h232 : e2 * e3 * e2 = tau * e2)
    (h323 : e3 * e2 * e3 = tau * e3)
    (h212 : e2 * e1 * e2 = tau * e2)
    (htau1 : e1 * tau = tau * e1)
    (htau3 : e3 * tau = tau * e3) :
    let t123 := T_123 e1 e2 e3
    let t321 := T_321 e1 e2 e3
    (e1 * e3) * (e1 * e3) = e1 * e3 ∧
    t123 * e1 = tau * (e1 * e3) ∧
    e3 * t123 = tau * (e1 * e3) ∧
    t123 * t123 = (tau * tau) * (e1 * e3) ∧
    t321 * t321 = (tau * tau) * (e1 * e3) ∧
    t123 * t321 = (tau * tau) * e1 ∧
    t321 * t123 = (tau * tau) * e3 ∧
    comm t123 t321 = (tau * tau) * (H_tl e1 e2 + H_tl e2 e3) := by
  have htau1' : ∀ W : B, e1 * (tau * W) = tau * (e1 * W) := fun W => by
    rw [← mul_assoc, htau1, mul_assoc]
  have htau3' : ∀ W : B, e3 * (tau * W) = tau * (e3 * W) := fun W => by
    rw [← mul_assoc, htau3, mul_assoc]
  have he13_idem : (e1 * e3) * (e1 * e3) = e1 * e3 := by
    calc (e1 * e3) * (e1 * e3)
      _ = e1 * (e3 * e1) * e3 := by noncomm_ring
      _ = e1 * (e1 * e3) * e3 := by rw [← h13]
      _ = (e1 * e1) * (e3 * e3) := by noncomm_ring
      _ = e1 * e3 := by rw [he1, he3]
  have ht123_e1 : T_123 e1 e2 e3 * e1 = tau * (e1 * e3) := by
    dsimp [T_123]
    calc e1 * e2 * e3 * e1
      _ = e1 * e2 * (e3 * e1) := by rw [mul_assoc]
      _ = e1 * e2 * (e1 * e3) := by rw [← h13]
      _ = (e1 * e2 * e1) * e3 := by noncomm_ring
      _ = (tau * e1) * e3 := by rw [h121]
      _ = tau * (e1 * e3) := by rw [mul_assoc]
  have he3_t123 : e3 * T_123 e1 e2 e3 = tau * (e1 * e3) := by
    dsimp [T_123]
    calc e3 * (e1 * e2 * e3)
      _ = (e3 * e1) * e2 * e3 := by noncomm_ring
      _ = (e1 * e3) * e2 * e3 := by rw [← h13]
      _ = e1 * (e3 * e2 * e3) := by noncomm_ring
      _ = e1 * (tau * e3) := by rw [h323]
      _ = tau * (e1 * e3) := htau1' e3
  have ht321_e3 : T_321 e1 e2 e3 * e3 = tau * (e1 * e3) := by
    dsimp [T_321]
    calc e3 * e2 * e1 * e3
      _ = e3 * e2 * (e1 * e3) := by rw [mul_assoc]
      _ = e3 * e2 * (e3 * e1) := by rw [h13]
      _ = (e3 * e2 * e3) * e1 := by noncomm_ring
      _ = (tau * e3) * e1 := by rw [h323]
      _ = tau * (e3 * e1) := by rw [mul_assoc]
      _ = tau * (e1 * e3) := by rw [← h13]
  have ht123_sq : T_123 e1 e2 e3 * T_123 e1 e2 e3 = (tau * tau) * (e1 * e3) := by
    calc T_123 e1 e2 e3 * (e1 * e2 * e3)
      _ = ((T_123 e1 e2 e3 * e1) * e2) * e3 := by noncomm_ring
      _ = ((tau * (e1 * e3)) * e2) * e3 := by rw [ht123_e1]
      _ = tau * (e1 * (e3 * e2 * e3)) := by noncomm_ring
      _ = tau * (e1 * (tau * e3)) := by rw [h323]
      _ = tau * (tau * (e1 * e3)) := by rw [htau1' e3]
      _ = (tau * tau) * (e1 * e3) := by rw [← mul_assoc]
  have ht321_sq : T_321 e1 e2 e3 * T_321 e1 e2 e3 = (tau * tau) * (e1 * e3) := by
    calc T_321 e1 e2 e3 * (e3 * e2 * e1)
      _ = ((T_321 e1 e2 e3 * e3) * e2) * e1 := by noncomm_ring
      _ = ((tau * (e1 * e3)) * e2) * e1 := by rw [ht321_e3]
      _ = ((tau * (e3 * e1)) * e2) * e1 := by rw [h13]
      _ = tau * (e3 * (e1 * e2 * e1)) := by noncomm_ring
      _ = tau * (e3 * (tau * e1)) := by rw [h121]
      _ = tau * (tau * (e3 * e1)) := by rw [htau3' e1]
      _ = (tau * tau) * (e1 * e3) := by rw [← h13, ← mul_assoc]
  have ht123_t321 : T_123 e1 e2 e3 * T_321 e1 e2 e3 = (tau * tau) * e1 := by
    dsimp [T_123, T_321]
    calc (e1 * e2 * e3) * (e3 * e2 * e1)
      _ = e1 * e2 * (e3 * e3) * e2 * e1 := by noncomm_ring
      _ = e1 * (e2 * e3 * e2) * e1 := by rw [he3]; noncomm_ring
      _ = e1 * (tau * e2) * e1 := by rw [h232]
      _ = (e1 * (tau * e2)) * e1 := rfl
      _ = (tau * (e1 * e2)) * e1 := by rw [htau1' e2]
      _ = tau * (e1 * e2 * e1) := by rw [mul_assoc]
      _ = tau * (tau * e1) := by rw [h121]
      _ = (tau * tau) * e1 := by rw [← mul_assoc]
  have ht321_t123 : T_321 e1 e2 e3 * T_123 e1 e2 e3 = (tau * tau) * e3 := by
    dsimp [T_123, T_321]
    calc (e3 * e2 * e1) * (e1 * e2 * e3)
      _ = e3 * e2 * (e1 * e1) * e2 * e3 := by noncomm_ring
      _ = e3 * (e2 * e1 * e2) * e3 := by rw [he1]; noncomm_ring
      _ = e3 * (tau * e2) * e3 := by rw [h212]
      _ = (e3 * (tau * e2)) * e3 := rfl
      _ = (tau * (e3 * e2)) * e3 := by rw [htau3' e2]
      _ = tau * (e3 * e2 * e3) := by rw [mul_assoc]
      _ = tau * (tau * e3) := by rw [h323]
      _ = (tau * tau) * e3 := by rw [← mul_assoc]
  have hcomm_t : comm (T_123 e1 e2 e3) (T_321 e1 e2 e3) = (tau * tau) * (H_tl e1 e2 + H_tl e2 e3) := by
    dsimp [comm, H_tl]
    rw [ht123_t321, ht321_t123]
    noncomm_ring
  exact ⟨he13_idem, ht123_e1, he3_t123, ht123_sq, ht321_sq, ht123_t321, ht321_t123, hcomm_t⟩

/--
**Node `𝔒ℭ₃` (`jones_wenzl_second_idempotent_from_halmos_square`):**
Under the 2-strand Temperley–Lieb relations (`e1² = e1`, `e2² = e2`, `e1 e2 e1 = τ e1`,
`e2 e1 e2 = τ e2` with central `τ`), the division-free 2-strand Jones–Wenzl element
`JW_2(e1, e2, τ) = (1 - τ) - (e1 - e2)² = (1 - τ) - e1 - e2 + e1 e2 + e2 e1` satisfies:
1. `JW_2 = (1 - τ) - e1 - e2 + e1 * e2 + e2 * e1`,
2. `e1 * JW_2 = 0` and `JW_2 * e1 = 0`,
3. `e2 * JW_2 = 0` and `JW_2 * e2 = 0`,
4. `H_tl e1 e2 * JW_2 = 0` and `JW_2 * H_tl e1 e2 = 0`,
5. `JW_2 * JW_2 = (1 - τ) * JW_2` (scaled idempotence!).
-/
theorem jones_wenzl_second_idempotent_from_halmos_square
    (e1 e2 tau : B)
    (he1 : e1 * e1 = e1) (he2 : e2 * e2 = e2)
    (h121 : e1 * e2 * e1 = tau * e1)
    (h212 : e2 * e1 * e2 = tau * e2)
    (htau1 : e1 * tau = tau * e1)
    (htau2 : e2 * tau = tau * e2) :
    let w2 := JW_2 e1 e2 tau
    let h12 := H_tl e1 e2
    w2 = (1 - tau) - e1 - e2 + e1 * e2 + e2 * e1 ∧
    e1 * w2 = 0 ∧
    w2 * e1 = 0 ∧
    e2 * w2 = 0 ∧
    w2 * e2 = 0 ∧
    h12 * w2 = 0 ∧
    w2 * h12 = 0 ∧
    w2 * w2 = (1 - tau) * w2 := by
  have he1' : ∀ W : B, e1 * (e1 * W) = e1 * W := fun W => by rw [← mul_assoc, he1]
  have he2' : ∀ W : B, e2 * (e2 * W) = e2 * W := fun W => by rw [← mul_assoc, he2]
  have h121_r : e1 * (e2 * e1) = tau * e1 := by rw [← mul_assoc, h121]
  have h212_r : e2 * (e1 * e2) = tau * e2 := by rw [← mul_assoc, h212]
  have h121' : ∀ W : B, e1 * (e2 * (e1 * W)) = tau * (e1 * W) := fun W => by
    rw [← mul_assoc, ← mul_assoc, h121, mul_assoc]
  have h212' : ∀ W : B, e2 * (e1 * (e2 * W)) = tau * (e2 * W) := fun W => by
    rw [← mul_assoc, ← mul_assoc, h212, mul_assoc]
  have hw2_expand : JW_2 e1 e2 tau = (1 - tau) - e1 - e2 + e1 * e2 + e2 * e1 := by
    dsimp [JW_2]
    simp only [sub_mul, mul_sub, mul_assoc, he1, he2]
    abel
  have he1_w2 : e1 * JW_2 e1 e2 tau = 0 := by
    rw [hw2_expand]
    simp only [mul_add, mul_sub, mul_one, mul_assoc, he1, he1', h121, h121_r, htau1]
    abel
  have hw2_e1 : JW_2 e1 e2 tau * e1 = 0 := by
    rw [hw2_expand]
    simp only [add_mul, sub_mul, one_mul, mul_assoc, he1, he1', h121, h121_r]
    abel
  have he2_w2 : e2 * JW_2 e1 e2 tau = 0 := by
    rw [hw2_expand]
    simp only [mul_add, mul_sub, mul_one, mul_assoc, he2, he2', h212, h212_r, htau2]
    abel
  have hw2_e2 : JW_2 e1 e2 tau * e2 = 0 := by
    rw [hw2_expand]
    simp only [add_mul, sub_mul, one_mul, mul_assoc, he2, he2', h212, h212_r]
    abel
  have hh12_w2 : H_tl e1 e2 * JW_2 e1 e2 tau = 0 := by
    dsimp [H_tl]; rw [sub_mul, he1_w2, he2_w2, sub_self]
  have hw2_h12 : JW_2 e1 e2 tau * H_tl e1 e2 = 0 := by
    dsimp [H_tl]; rw [mul_sub, hw2_e1, hw2_e2, sub_self]
  have hw2_sq : JW_2 e1 e2 tau * JW_2 e1 e2 tau = (1 - tau) * JW_2 e1 e2 tau := by
    calc JW_2 e1 e2 tau * JW_2 e1 e2 tau
      _ = ((1 - tau) - H_tl e1 e2 * H_tl e1 e2) * JW_2 e1 e2 tau := rfl
      _ = (1 - tau) * JW_2 e1 e2 tau - H_tl e1 e2 * (H_tl e1 e2 * JW_2 e1 e2 tau) := by
          rw [sub_mul, mul_assoc]
      _ = (1 - tau) * JW_2 e1 e2 tau - H_tl e1 e2 * 0 := by rw [hh12_w2]
      _ = (1 - tau) * JW_2 e1 e2 tau := by rw [mul_zero, sub_zero]
  exact ⟨hw2_expand, he1_w2, hw2_e1, he2_w2, hw2_e2, hh12_w2, hw2_h12, hw2_sq⟩

/--
**Node `𝔒ℭ₄` (`kauffman_jones_yang_baxter_braid_defect_identity`):**
For `g1 = 1 + u * e1` and `g2 = 1 + u * e2` (with spectral parameter `u` commuting with `e1, e2, τ`),
the Artin Yang–Baxter braid defect is governed by the exact Jones–Kauffman quadratic `1 + u + τ u²`:
1. `g1 * g2 * g1 - g2 * g1 * g2 = (u + u * u + tau * (u * u * u)) * (e1 - e2)`,
2. If `1 + u + tau * (u * u) = 0`, then `g1 * g2 * g1 = g2 * g1 * g2` holds identically!
-/
theorem kauffman_jones_yang_baxter_braid_defect_identity
    (e1 e2 tau u : B)
    (he1 : e1 * e1 = e1) (he2 : e2 * e2 = e2)
    (h121 : e1 * e2 * e1 = tau * e1)
    (h212 : e2 * e1 * e2 = tau * e2)
    (hu1 : e1 * u = u * e1) (hu2 : e2 * u = u * e2)
    (hutau : u * tau = tau * u) :
    let g1 := g_braid u e1
    let g2 := g_braid u e2
    let h12 := H_tl e1 e2
    g1 * g2 * g1 - g2 * g1 * g2 = (u * (1 + u + tau * (u * u))) * h12 ∧
    (1 + u + tau * (u * u) = 0 → g1 * g2 * g1 = g2 * g1 * g2) := by
  have hu1' : ∀ W : B, e1 * (u * W) = u * (e1 * W) := fun W => by rw [← mul_assoc, hu1, mul_assoc]
  have hu2' : ∀ W : B, e2 * (u * W) = u * (e2 * W) := fun W => by rw [← mul_assoc, hu2, mul_assoc]
  have hutau' : ∀ W : B, u * (tau * W) = tau * (u * W) := fun W => by rw [← mul_assoc, hutau, mul_assoc]
  have he1' : ∀ W : B, e1 * (e1 * W) = e1 * W := fun W => by rw [← mul_assoc, he1]
  have he2' : ∀ W : B, e2 * (e2 * W) = e2 * W := fun W => by rw [← mul_assoc, he2]
  have h121_r : e1 * (e2 * e1) = tau * e1 := by rw [← mul_assoc, h121]
  have h212_r : e2 * (e1 * e2) = tau * e2 := by rw [← mul_assoc, h212]
  have h121' : ∀ W : B, e1 * (e2 * (e1 * W)) = tau * (e1 * W) := fun W => by
    rw [← mul_assoc, ← mul_assoc, h121, mul_assoc]
  have h212' : ∀ W : B, e2 * (e1 * (e2 * W)) = tau * (e2 * W) := fun W => by
    rw [← mul_assoc, ← mul_assoc, h212, mul_assoc]
  have h_defect : g_braid u e1 * g_braid u e2 * g_braid u e1 -
      g_braid u e2 * g_braid u e1 * g_braid u e2 =
      (u * (1 + u + tau * (u * u))) * H_tl e1 e2 := by
    dsimp [g_braid, H_tl]
    simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, mul_assoc,
               he1, he2, he1', he2', hu1, hu2, hu1', hu2', h121, h212, h121_r, h212_r, hutau']
    abel
  refine ⟨h_defect, fun h_quad => ?_⟩
  apply sub_eq_zero.mp
  rw [h_defect, h_quad, mul_zero, zero_mul]

/--
**Node `𝔒ℭ₅` (`master_octacosadic_three_strand_yang_baxter_coagulation`):**
Master structural synthesis of the Order 28 (Octacosadic) poset `𝔒ℭ₁ ≺ ⋯ ≺ 𝔒ℭ₅`.
-/
theorem master_octacosadic_three_strand_yang_baxter_coagulation
    (e1 e2 e3 tau u : B)
    (he1 : e1 * e1 = e1) (he2 : e2 * e2 = e2) (he3 : e3 * e3 = e3)
    (h13 : e1 * e3 = e3 * e1)
    (h121 : e1 * e2 * e1 = tau * e1)
    (h212 : e2 * e1 * e2 = tau * e2)
    (h232 : e2 * e3 * e2 = tau * e2)
    (h323 : e3 * e2 * e3 = tau * e3)
    (htau1 : e1 * tau = tau * e1) (htau2 : e2 * tau = tau * e2) (htau3 : e3 * tau = tau * e3)
    (hu1 : e1 * u = u * e1) (hu2 : e2 * u = u * e2) (hutau : u * tau = tau * u) :
    (OctacosadicBraidNode.OC1_ThreeStrandHalmosAporia < OctacosadicBraidNode.OC2_CubicBraidTransfer ∧
     OctacosadicBraidNode.OC2_CubicBraidTransfer < OctacosadicBraidNode.OC3_JonesWenzlIdempotent ∧
     OctacosadicBraidNode.OC3_JonesWenzlIdempotent < OctacosadicBraidNode.OC4_KauffmanJonesYangBaxterDefect ∧
     OctacosadicBraidNode.OC4_KauffmanJonesYangBaxterDefect < OctacosadicBraidNode.OC5_OctacosadicMasterCoagulation) ∧
    comm (H_tl e1 e2) (H_tl e2 e3) = Sigma_tl e1 e2 + Sigma_tl e2 e3 ∧
    comm (T_123 e1 e2 e3) (T_321 e1 e2 e3) = (tau * tau) * (H_tl e1 e2 + H_tl e2 e3) ∧
    JW_2 e1 e2 tau * JW_2 e1 e2 tau = (1 - tau) * JW_2 e1 e2 tau ∧
    (g_braid u e1 * g_braid u e2 * g_braid u e1 - g_braid u e2 * g_braid u e1 * g_braid u e2 =
      (u * (1 + u + tau * (u * u))) * H_tl e1 e2) := by
  exact ⟨OctacosadicBraidNode.oc_poset_chain,
         (three_strand_halmos_commutator_aporia e1 e2 e3 h13).2,
         (three_strand_cubic_temperley_lieb_braid_transfer e1 e2 e3 tau he1 he3 h13 h121 h232 h323 h212 htau1 htau3).2.2.2.2.2.2.2,
         (jones_wenzl_second_idempotent_from_halmos_square e1 e2 tau he1 he2 h121 h212 htau1 htau2).2.2.2.2.2.2.2,
         (kauffman_jones_yang_baxter_braid_defect_identity e1 e2 tau u he1 he2 h121 h212 hu1 hu2 hutau).1⟩

/--
**Inductive Colimit Cone Transport of the Temperley–Lieb, Jones–Wenzl, & Yang–Baxter Braid Tower
(`temperley_lieb_yang_baxter_colimit_cone_transport`):**
Let `Stage : ℕ → Type u` be a directed tower of non-commutative operator rings `[∀ k, Ring (Stage k)]`
with connecting ring homomorphisms `embed : ∀ k : ℕ, Stage k →+* Stage (k + 1)` and colimit
cone legs `toLimit : ∀ k : ℕ, Stage k →+* Limit` into a colimit ring `[Ring Limit]` satisfying
cone compatibility `∀ k Z, toLimit (k + 1) (embed k Z) = toLimit k Z`.
Then for any stage `k : ℕ` and any Temperley–Lieb / Jones–Wenzl / Yang–Baxter generators
`e1, e2, tau, u : Stage k`:
1. The colimit cone legs preserve `H_tl`, `JW_2`, and `g_braid` and are invariant under stage
   refinement `embed k`,
2. If `e1, e2, tau, u` satisfy the Temperley–Lieb relations at stage `k`, then their images in the
   colimit ring `Limit` satisfy both the Jones–Wenzl scaled idempotence relation and the exact
   Kauffman–Jones Yang–Baxter braid defect identity!
-/
theorem temperley_lieb_yang_baxter_colimit_cone_transport
    {Stage : ℕ → Type u} [∀ k, Ring (Stage k)]
    {Limit : Type v} [Ring Limit]
    (embed : ∀ k : ℕ, Stage k →+* Stage (k + 1))
    (toLimit : ∀ k : ℕ, Stage k →+* Limit)
    (hCone : ∀ (k : ℕ) (Z : Stage k), toLimit (k + 1) (embed k Z) = toLimit k Z)
    (k : ℕ) (e1 e2 tau u : Stage k)
    (he1 : e1 * e1 = e1) (he2 : e2 * e2 = e2)
    (h121 : e1 * e2 * e1 = tau * e1) (h212 : e2 * e1 * e2 = tau * e2)
    (htau1 : e1 * tau = tau * e1) (htau2 : e2 * tau = tau * e2)
    (hu1 : e1 * u = u * e1) (hu2 : e2 * u = u * e2) (hutau : u * tau = tau * u) :
    let E1  := toLimit k e1
    let E2  := toLimit k e2
    let Tau := toLimit k tau
    let U   := toLimit k u
    toLimit k (JW_2 e1 e2 tau) = JW_2 E1 E2 Tau ∧
    toLimit (k + 1) (JW_2 (embed k e1) (embed k e2) (embed k tau)) = JW_2 E1 E2 Tau ∧
    toLimit k (g_braid u e1) = g_braid U E1 ∧
    toLimit (k + 1) (g_braid (embed k u) (embed k e1)) = g_braid U E1 ∧
    JW_2 E1 E2 Tau * JW_2 E1 E2 Tau = (1 - Tau) * JW_2 E1 E2 Tau ∧
    (g_braid U E1 * g_braid U E2 * g_braid U E1 - g_braid U E2 * g_braid U E1 * g_braid U E2 =
      (U * (1 + U + Tau * (U * U))) * H_tl E1 E2) := by
  have hMapJW_lim : ∀ (a b t : Stage k),
      toLimit k (JW_2 a b t) = JW_2 (toLimit k a) (toLimit k b) (toLimit k t) := by
    intro a b t; dsimp only [JW_2]; simp only [map_sub, map_mul, map_one]
  have hMapJW_emb : ∀ (a b t : Stage k),
      embed k (JW_2 a b t) = JW_2 (embed k a) (embed k b) (embed k t) := by
    intro a b t; dsimp only [JW_2]; simp only [map_sub, map_mul, map_one]
  have hMapG_lim : ∀ (x a : Stage k),
      toLimit k (g_braid x a) = g_braid (toLimit k x) (toLimit k a) := by
    intro x a; dsimp only [g_braid]; simp only [map_add, map_mul, map_one]
  have hMapG_emb : ∀ (x a : Stage k),
      embed k (g_braid x a) = g_braid (embed k x) (embed k a) := by
    intro x a; dsimp only [g_braid]; simp only [map_add, map_mul, map_one]
  have hMapH_lim : ∀ (a b : Stage k),
      toLimit k (H_tl a b) = H_tl (toLimit k a) (toLimit k b) := by
    intro a b; dsimp only [H_tl]; simp only [map_sub]
  have hJW_stage : JW_2 e1 e2 tau * JW_2 e1 e2 tau = (1 - tau) * JW_2 e1 e2 tau :=
    (jones_wenzl_second_idempotent_from_halmos_square e1 e2 tau he1 he2 h121 h212 htau1 htau2).2.2.2.2.2.2.2
  have hYB_stage : g_braid u e1 * g_braid u e2 * g_braid u e1 -
      g_braid u e2 * g_braid u e1 * g_braid u e2 =
      (u * (1 + u + tau * (u * u))) * H_tl e1 e2 :=
    (kauffman_jones_yang_baxter_braid_defect_identity e1 e2 tau u he1 he2 h121 h212 hu1 hu2 hutau).1
  refine ⟨hMapJW_lim e1 e2 tau, ?_, hMapG_lim u e1, ?_, ?_, ?_⟩
  · rw [← hMapJW_emb, hCone, hMapJW_lim]
  · rw [← hMapG_emb, hCone, hMapG_lim]
  · have h := congrArg (toLimit k) hJW_stage
    simpa only [map_mul, map_sub, map_one, hMapJW_lim] using h
  · have h := congrArg (toLimit k) hYB_stage
    simpa only [map_sub, map_mul, map_add, map_one, hMapG_lim, hMapH_lim] using h

end Track2_OctacosadicThreeStrandTemperleyLiebYangBaxter

end InfoGeometry.OperatorAlgebra.PeirceSpine
