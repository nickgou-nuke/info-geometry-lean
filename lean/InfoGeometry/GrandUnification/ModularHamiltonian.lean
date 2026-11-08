/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.GrandUnification.ModularPhaseSeparation
import InfoGeometry.GrandUnification.MachianCosmology
import InfoGeometry.GrandUnification.DirectSumDecomposition
import InfoGeometry.GrandUnification.MoebiusWittenIndex
import InfoGeometry.GrandUnification.HorizonCapacitance
import InfoGeometry.Canonical.HolographicCapacitorMoebiusTraceBridge
import InfoGeometry.Canonical.ConnesRadonNikodymLogBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NoncommRing

/-!
===============================================================================
HIVE CONSTITUTIONAL HEADER
===============================================================================
Module: InfoGeometry.GrandUnification.ModularHamiltonian
Role: Constructive, non-vacuous Lean 4 formalization of the Modular Hamiltonian
  $K = -\log \Delta$ as the logarithmic horizon defect and generator of modular
  time flow across the $(5,5)$ holographic capacitor (`HorizonCapacitance`,
  `MoebiusWittenIndex`, `ModularPhaseSeparation`, `MachianCosmology`).

-------------------------------------------------------------------------------
THREE-BUCKET EPISTEMIC AUDIT MAP
-------------------------------------------------------------------------------
- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.GrandUnification.ModularPhaseSeparation`:
    `IsKreinSymmetry`, `IsOddOperator`, `supertrace`, `ModularCommutant`,
    `odd_operator_zero_of_grading_one`, `odd_operator_zero_of_grading_neg_one`,
    `modular_phase_separation`.
  * `InfoGeometry.GrandUnification.MachianCosmology`,
    `InfoGeometry.GrandUnification.DirectSumDecomposition`,
    `InfoGeometry.GrandUnification.MoebiusWittenIndex`:
    `Ego`, `Anima`, `ego_inf_anima_eq_bot`, `ego_sup_anima_eq_top`,
    `witten_index`, `moebius_zero_index_enforcement`, `total_dimension_ten`.
  * `InfoGeometry.GrandUnification.HorizonCapacitance`:
    `HorizonDefectBlock`, `horizon_capacitance`, `horizon_capacitance_add_range_finrank`.
- BUCKET 2 (Deconfabulation of the Raw `ModularHamiltonian.lean` Draft):
  * Eliminated the vacuous `structure ModularDynamics ... : Prop` wrapper and
    the placeholder `theorem time_requires_horizon ... : True := trivial`.
  * Replaced `True := trivial` with the exact linear-algebraic theorem
    `time_requires_horizon`: for any operator $K \in \mathrm{End}_R(M)$ whose
    modes are anchored to the horizon defect ($\mathcal{T} K = K$, equivalently
    $\mathrm{range}(K) \le \mathrm{HorizonDefectBlock}(\mathcal{T})$), vanishing
    horizon capacitance (`horizon_capacitance 𝒯 = 0`) forces
    $\mathrm{HorizonDefectBlock}(\mathcal{T}) = \bot$, $\mathrm{range}(K) = \bot$,
    and $K = 0$ identically; contrapositively, $K \ne 0 \implies \mathrm{horizon\_capacitance}(\mathcal{T}) > 0$.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `modularLogEigenvalue_properties` ($\mathfrak{MH}_1$):
    $K(1) = 0$, $K(\delta^{-1}) = -K(\delta)$, $K(\delta_1 \delta_2) = K(\delta_1) + K(\delta_2)$,
    and $\exp(-K(\delta)) = \delta$ for $\delta > 0$.
  * `modular_conjugation_iff_isOddOperator` &
    `modular_hamiltonian_twin_sheet_time_reversal` ($\mathfrak{MH}_2$):
    $J_\Delta^2 = 1 \implies (J_\Delta K J_\Delta = -K \iff \mathrm{IsOddOperator}\,J_\Delta\,K)$,
    mapping $\mathrm{Ego}(J_\Delta) \leftrightarrow \mathrm{Anima}(J_\Delta)$ and reversing the sign
    of $K$ across the twin chiral sheets $\mathrm{Ego}(\Gamma)$ and $\mathrm{Anima}(\Gamma)$.
  * `holographic_capacitance_split_five_five_quantization` ($\mathfrak{MH}_3$):
    $\mathrm{HorizonDefectBlock}(\Gamma) = \mathrm{Ego}(\Gamma)$, and for the $(5,5)$ split
    vacuum ($\dim \mathrm{Ego}(\Gamma) = 5$, $\dim \mathrm{Anima}(\Gamma) = 5$),
    $\mathrm{horizon\_capacitance}(\Gamma) = 5$, $\mathrm{witten\_index}(\Gamma) = 0$, and
    $\dim_R M = 10$.
  * `time_requires_horizon`, `nonzero_time_forces_positive_horizon_capacitance`, &
    `modular_time_anomaly_forces_noncommuting_twist` ($\mathfrak{MH}_4$).
  * `mh5_master_modular_hamiltonian_horizon_capacitance_synthesis` ($\mathfrak{MH}_5$).
===============================================================================
-/

namespace InfoGeometry.GrandUnification.Dynamics

open LinearMap
open FiniteDimensional
open InfoGeometry.GrandUnification.ModularPhaseSeparation
open InfoGeometry.GrandUnification.MachianCosmology
open InfoGeometry.GrandUnification.DirectSumDecomposition
open InfoGeometry.GrandUnification.MoebiusWittenIndex
open InfoGeometry.GrandUnification.HorizonCapacitance
open InfoGeometry.Canonical.HolographicCapacitorMoebiusTraceBridge

/-!
## Section 1: The 5-Stage Causal Poset ($\mathfrak{MH}_1 \prec \mathfrak{MH}_2 \prec \mathfrak{MH}_3 \prec \mathfrak{MH}_4 \prec \mathfrak{MH}_5$)
-/

/-- The 5 stages of the Modular Hamiltonian & Horizon Capacitance causal poset. -/
inductive ModularHamiltonianStage : Type
  | mh1_logarithmic_modular_defect
  | mh2_tomita_conjugation_twin_sheet_reversal
  | mh3_holographic_five_bit_capacitance_quantization
  | mh4_time_requires_horizon_defect
  | mh5_master_thermodynamic_dynamic_closure
  deriving DecidableEq, Repr

namespace ModularHamiltonianStage

/-- Strict integer rank $\mathfrak{MH}_1 < \mathfrak{MH}_2 < \mathfrak{MH}_3 < \mathfrak{MH}_4 < \mathfrak{MH}_5$. -/
def rank : ModularHamiltonianStage → ℕ
  | .mh1_logarithmic_modular_defect => 1
  | .mh2_tomita_conjugation_twin_sheet_reversal => 2
  | .mh3_holographic_five_bit_capacitance_quantization => 3
  | .mh4_time_requires_horizon_defect => 4
  | .mh5_master_thermodynamic_dynamic_closure => 5

/-- Covering edges of the 5-stage Hasse chain $\mathfrak{MH}_1 \prec \dots \prec \mathfrak{MH}_5$. -/
def coverEdge : ModularHamiltonianStage → ModularHamiltonianStage → Prop
  | .mh1_logarithmic_modular_defect, .mh2_tomita_conjugation_twin_sheet_reversal => True
  | .mh2_tomita_conjugation_twin_sheet_reversal, .mh3_holographic_five_bit_capacitance_quantization => True
  | .mh3_holographic_five_bit_capacitance_quantization, .mh4_time_requires_horizon_defect => True
  | .mh4_time_requires_horizon_defect, .mh5_master_thermodynamic_dynamic_closure => True
  | _, _ => False

/-- Decidability of `coverEdge`. -/
instance instDecidableRelCoverEdge : DecidableRel coverEdge := fun a b => by
  cases a <;> cases b <;> unfold coverEdge <;> infer_instance

/-- The rank function is injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge increments `rank` by $1$. -/
theorem coverEdge_rank_step {a b : ModularHamiltonianStage} (h : coverEdge a b) :
    rank b = rank a + 1 := by
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge is strictly monotone in `rank`. -/
theorem coverEdge_strictMono {a b : ModularHamiltonianStage} (h : coverEdge a b) :
    rank a < rank b := by
  have hstep := coverEdge_rank_step h
  omega

/-- No stage covers itself. -/
theorem coverEdge_acyclic (a : ModularHamiltonianStage) : ¬ coverEdge a a := by
  intro h
  have hlt := coverEdge_strictMono h
  omega

/-- Complete 4-edge covering chain $\mathfrak{MH}_1 \prec \mathfrak{MH}_2 \prec \mathfrak{MH}_3 \prec \mathfrak{MH}_4 \prec \mathfrak{MH}_5$. -/
theorem poset_covering_chain :
    coverEdge .mh1_logarithmic_modular_defect .mh2_tomita_conjugation_twin_sheet_reversal ∧
    coverEdge .mh2_tomita_conjugation_twin_sheet_reversal .mh3_holographic_five_bit_capacitance_quantization ∧
    coverEdge .mh3_holographic_five_bit_capacitance_quantization .mh4_time_requires_horizon_defect ∧
    coverEdge .mh4_time_requires_horizon_defect .mh5_master_thermodynamic_dynamic_closure := by
  decide

end ModularHamiltonianStage

/-!
## Section 2 ($\mathfrak{MH}_1$): The Logarithmic Modular Defect $K = -\log \Delta$
-/

/-- Spectral eigenvalue $K(\delta) = -\log \delta$ of the Modular Hamiltonian $K = -\log \Delta$
on a modular eigenmode with eigenvalue $\delta > 0$. -/
noncomputable def modularLogEigenvalue (δ : ℝ) : ℝ :=
  -Real.log δ

/-- **Stage $\mathfrak{MH}_1$ Theorem (Logarithmic Modular Hamiltonian Laws):**
1. At unit modular weight $\delta = 1$ (no modular defect), $K(1) = -\log 1 = 0$;
2. Under Klein-bottle / Tomita–Takesaki sheet inversion $\delta \mapsto \delta^{-1}$,
   $K(\delta^{-1}) = -K(\delta)$ (Modular Time reverses sign across the twin sheets);
3. For any positive modular weights $\delta_1, \delta_2 > 0$,
   $K(\delta_1 \delta_2) = K(\delta_1) + K(\delta_2)$;
4. For any $\delta > 0$, $\exp(-K(\delta)) = \delta$ ($\Delta = e^{-K}$). -/
theorem modularLogEigenvalue_properties (δ δ₁ δ₂ : ℝ)
    (hδ : 0 < δ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    modularLogEigenvalue 1 = 0 ∧
    modularLogEigenvalue δ⁻¹ = -modularLogEigenvalue δ ∧
    modularLogEigenvalue (δ₁ * δ₂) =
      modularLogEigenvalue δ₁ + modularLogEigenvalue δ₂ ∧
    Real.exp (-modularLogEigenvalue δ) = δ := by
  have h1 : modularLogEigenvalue 1 = 0 := by
    unfold modularLogEigenvalue
    rw [Real.log_one, neg_zero]
  have hinv : modularLogEigenvalue δ⁻¹ = -modularLogEigenvalue δ := by
    unfold modularLogEigenvalue
    rw [Real.log_inv, neg_neg]
  have hmul :
      modularLogEigenvalue (δ₁ * δ₂) =
        modularLogEigenvalue δ₁ + modularLogEigenvalue δ₂ := by
    unfold modularLogEigenvalue
    rw [Real.log_mul (ne_of_gt hδ₁) (ne_of_gt hδ₂)]
    ring
  have hexp : Real.exp (-modularLogEigenvalue δ) = δ := by
    unfold modularLogEigenvalue
    rw [neg_neg, Real.exp_log hδ]
  exact ⟨h1, hinv, hmul, hexp⟩

/-!
## Section 3 ($\mathfrak{MH}_2$): Tomita–Takesaki Modular Conjugation ($J_\Delta K J_\Delta = -K$) & Twin-Sheet Time Reversal
-/

section ModularConjugation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Equivalence of Tomita–Takesaki Modular Conjugation and `IsOddOperator`:**
For any modular conjugation involution $J_\Delta \in \mathrm{End}_R(M)$ with $J_\Delta^2 = 1$,
the Tomita–Takesaki law $J_\Delta K J_\Delta = -K$ is equivalent to $J_\Delta K = -(K J_\Delta)$
(`IsOddOperator J_Δ K`). -/
theorem modular_conjugation_iff_isOddOperator
    (J_Δ K : Module.End R M) (hJ : J_Δ * J_Δ = 1) :
    J_Δ * K * J_Δ = -K ↔ IsOddOperator J_Δ K := by
  unfold IsOddOperator
  constructor
  · intro hconj
    calc
      J_Δ * K = (J_Δ * K) * 1 := (mul_one (J_Δ * K)).symm
      _ = (J_Δ * K) * (J_Δ * J_Δ) := by rw [hJ]
      _ = (J_Δ * K * J_Δ) * J_Δ := by noncomm_ring
      _ = (-K) * J_Δ := by rw [hconj]
      _ = -(K * J_Δ) := neg_mul K J_Δ
  · intro hodd
    calc
      J_Δ * K * J_Δ = (-(K * J_Δ)) * J_Δ := by rw [hodd]
      _ = -((K * J_Δ) * J_Δ) := neg_mul (K * J_Δ) J_Δ
      _ = -(K * (J_Δ * J_Δ)) := by rw [mul_assoc]
      _ = -(K * 1) := by rw [hJ]
      _ = -K := by rw [mul_one]

/-- **Stage $\mathfrak{MH}_2$ Theorem (Twin-Sheet Reversal of Modular Time):**
Let $J_\Delta, K \in \mathrm{End}_R(M)$ satisfy $J_\Delta^2 = 1$ and $J_\Delta K J_\Delta = -K$.
1. $K$ swaps the $+1$ (`Ego J_Δ`) and $-1$ (`Anima J_Δ`) eigenspaces of $J_\Delta$:
   $x \in \mathrm{Ego}(J_\Delta) \implies K x \in \mathrm{Anima}(J_\Delta)$ and
   $y \in \mathrm{Anima}(J_\Delta) \implies K y \in \mathrm{Ego}(J_\Delta)$;
2. For any chiral grading $\Gamma$ anticommuting with $J_\Delta$ ($J_\Delta \Gamma = -\Gamma J_\Delta$),
   $J_\Delta$ maps `Ego Γ` into `Anima Γ` and reverses the action of $K$ on every state $v \in M$:
   $K (J_\Delta v) = - J_\Delta (K v)$. -/
theorem modular_hamiltonian_twin_sheet_time_reversal
    (J_Δ Γ K : Module.End R M)
    (hJ : J_Δ * J_Δ = 1)
    (hconj : J_Δ * K * J_Δ = -K)
    (hJΓ : J_Δ * Γ = -(Γ * J_Δ)) :
    (∀ x ∈ Ego J_Δ, K x ∈ Anima J_Δ) ∧
    (∀ y ∈ Anima J_Δ, K y ∈ Ego J_Δ) ∧
    (∀ v ∈ Ego Γ, J_Δ v ∈ Anima Γ) ∧
    (∀ v : M, K (J_Δ v) = - J_Δ (K v)) := by
  have hodd : J_Δ * K = -(K * J_Δ) :=
    (modular_conjugation_iff_isOddOperator J_Δ K hJ).mp hconj
  have hJK_apply : ∀ v : M, J_Δ (K v) = - K (J_Δ v) := by
    intro v
    have h1 : (J_Δ * K) v = (-(K * J_Δ)) v := congrArg (fun T : Module.End R M => T v) hodd
    rw [Module.End.mul_apply, LinearMap.neg_apply, Module.End.mul_apply] at h1
    exact h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    change (J_Δ + 1) (K x) = 0
    have hx_eq : J_Δ x = x := sub_eq_zero.mp hx
    calc
      (J_Δ + 1) (K x) = J_Δ (K x) + K x := by rw [LinearMap.add_apply, Module.End.one_apply]
      _ = - K (J_Δ x) + K x := by rw [hJK_apply x]
      _ = - K x + K x := by rw [hx_eq]
      _ = 0 := neg_add_cancel (K x)
  · intro y hy
    change (J_Δ - 1) (K y) = 0
    have hy_eq : J_Δ y = -y := add_eq_zero_iff_eq_neg.mp hy
    calc
      (J_Δ - 1) (K y) = J_Δ (K y) - K y := by rw [LinearMap.sub_apply, Module.End.one_apply]
      _ = - K (J_Δ y) - K y := by rw [hJK_apply y]
      _ = - K (-y) - K y := by rw [hy_eq]
      _ = K y - K y := by rw [map_neg, neg_neg]
      _ = 0 := sub_self (K y)
  · intro v hv
    change (Γ + 1) (J_Δ v) = 0
    have hv_eq : Γ v = v := sub_eq_zero.mp hv
    have hΓJ : Γ (J_Δ v) = - J_Δ (Γ v) := by
      have h1 : (J_Δ * Γ) v = (-(Γ * J_Δ)) v := congrArg (fun T : Module.End R M => T v) hJΓ
      have h2 : J_Δ (Γ v) = - Γ (J_Δ v) := by
        rw [Module.End.mul_apply, LinearMap.neg_apply, Module.End.mul_apply] at h1
        exact h1
      calc
        Γ (J_Δ v) = -(-Γ (J_Δ v)) := (neg_neg _).symm
        _ = - J_Δ (Γ v) := by rw [← h2]
    calc
      (Γ + 1) (J_Δ v) = Γ (J_Δ v) + J_Δ v := by rw [LinearMap.add_apply, Module.End.one_apply]
      _ = - J_Δ (Γ v) + J_Δ v := by rw [hΓJ]
      _ = - J_Δ v + J_Δ v := by rw [hv_eq]
      _ = 0 := neg_add_cancel (J_Δ v)
  · intro v
    have h2 := hJK_apply v
    calc
      K (J_Δ v) = -(-K (J_Δ v)) := (neg_neg _).symm
      _ = - J_Δ (K v) := by rw [← h2]

/-- **Modular Time Anomaly Forces Non-Commuting Twist:**
Over a free finite-rank module `M`, if $J_\Delta^2 = 1$, $J_\Delta K J_\Delta = -K$, and
`supertrace J_Δ (K * 𝒯 - 𝒯 * K) ≠ 0`, then $J_\Delta \ne 1$, $J_\Delta \ne -1$, and
$\mathcal{T} \notin \mathrm{ModularCommutant}\,K$ ($\mathcal{T} K \ne K \mathcal{T}$). -/
theorem modular_time_anomaly_forces_noncommuting_twist
    [Invertible (2 : R)] [Module.Free R M] [Module.Finite R M]
    (J_Δ K 𝒯 : Module.End R M)
    (hJ : J_Δ * J_Δ = 1)
    (hconj : J_Δ * K * J_Δ = -K)
    (hanom : supertrace J_Δ (K * 𝒯 - 𝒯 * K) ≠ 0) :
    J_Δ ≠ 1 ∧ J_Δ ≠ -1 ∧ (𝒯 ∈ ModularCommutant K → False) := by
  have hodd : IsOddOperator J_Δ K :=
    (modular_conjugation_iff_isOddOperator J_Δ K hJ).mp hconj
  exact modular_phase_separation J_Δ K 𝒯 hodd hanom

end ModularConjugation

/-!
## Section 4 ($\mathfrak{MH}_3$): The $(5,5)$ Holographic Capacitance Quantization (`holographic_capacitance_quantization`)
-/

section HolographicCapacitance

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- The Horizon Defect Block `HorizonDefectBlock Γ = ker(Γ - id)` is definitionally identical
to the $+1$ chiral eigenspace `Ego Γ = ker(Γ - 1)`. -/
theorem horizonDefectBlock_eq_ego (Γ : Module.End R M) :
    HorizonDefectBlock Γ = Ego Γ ∧
    horizon_capacitance Γ = (Module.finrank R (Ego Γ) : ℤ) := by
  have hsub : HorizonDefectBlock Γ = Ego Γ := by
    ext x
    exact Iff.intro id id
  have hcap : horizon_capacitance Γ = (Module.finrank R (Ego Γ) : ℤ) := by
    unfold horizon_capacitance
    rw [hsub]
  exact ⟨hsub, hcap⟩

/-- **Stage $\mathfrak{MH}_3$ Theorem (`holographic_capacitance_split_five_five_quantization`):**
For any $(5,5)$ Krein/Möbius horizon ($\Gamma^2 = 1$, $\dim_R \mathrm{Ego}(\Gamma) = 5$,
$\dim_R \mathrm{Anima}(\Gamma) = 5$):
1. `HorizonDefectBlock Γ = Ego Γ`;
2. **Exact 5-Bit Horizon Capacitance Quantization:** `horizon_capacitance Γ = 5`;
3. **Zero Global Witten Index:** `witten_index Γ = 0`;
4. **10D Bulk Recovery:** `Module.finrank R M = 10`;
5. **Complementary Defect Range Rank:** `(Module.finrank R (LinearMap.range (Γ - LinearMap.id)) : ℤ) = 5`. -/
theorem holographic_capacitance_split_five_five_quantization
    [Invertible (2 : R)] [FiniteDimensional R M]
    (Γ : Module.End R M)
    (h_krein : IsKreinSymmetry Γ)
    (h_left : Module.finrank R (Ego Γ) = 5)
    (h_right : Module.finrank R (Anima Γ) = 5) :
    HorizonDefectBlock Γ = Ego Γ ∧
    horizon_capacitance Γ = 5 ∧
    witten_index Γ = 0 ∧
    Module.finrank R M = 10 ∧
    (Module.finrank R (LinearMap.range (Γ - LinearMap.id)) : ℤ) = 5 := by
  obtain ⟨hblock, _⟩ := horizonDefectBlock_eq_ego Γ
  have h_sym : Module.finrank R (HorizonDefectBlock Γ) = 5 := by
    rw [hblock, h_left]
  have hcap : horizon_capacitance Γ = 5 :=
    holographic_capacitance_quantization Γ h_sym
  have hwit : witten_index Γ = 0 :=
    moebius_zero_index_enforcement Γ h_left h_right
  have hdim10 : Module.finrank R M = 10 :=
    total_dimension_ten Γ h_krein h_left h_right
  have hrn := horizon_capacitance_add_range_finrank Γ
  have hrange : (Module.finrank R (LinearMap.range (Γ - LinearMap.id)) : ℤ) = 5 := by
    rw [hcap, hdim10] at hrn
    omega
  exact ⟨hblock, hcap, hwit, hdim10, hrange⟩

end HolographicCapacitance

/-!
## Section 5 ($\mathfrak{MH}_4$): Constructive Proof of `time_requires_horizon`
-/

section TimeRequiresHorizon

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]

omit [FiniteDimensional R M] in
/-- If the Modular Hamiltonian $K$ is anchored to the fixed-point modes of the Möbius twist
$\mathcal{T}$ ($\mathcal{T} K = K$), then its range lies inside `HorizonDefectBlock 𝒯`. -/
theorem range_le_horizonDefectBlock_of_mul_eq_right
    (𝒯 K : Module.End R M) (hTK : 𝒯 * K = K) :
    LinearMap.range K ≤ HorizonDefectBlock 𝒯 := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  change ((𝒯 - LinearMap.id : Module.End R M)) (K x) = 0
  have h_eval : (𝒯 * K) x = K x := congrArg (fun T : Module.End R M => T x) hTK
  calc
    ((𝒯 - LinearMap.id : Module.End R M)) (K x) = 𝒯 (K x) - K x := by
      rw [LinearMap.sub_apply, LinearMap.id_apply]
    _ = (𝒯 * K) x - K x := by rw [Module.End.mul_apply]
    _ = K x - K x := by rw [h_eval]
    _ = 0 := sub_self (K x)

/-- Vanishing horizon capacitance (`horizon_capacitance 𝒯 = 0`) forces the Horizon Defect Block
`HorizonDefectBlock 𝒯` to be the trivial subspace `⊥`. -/
theorem horizonDefectBlock_eq_bot_of_capacitance_zero
    (𝒯 : Module.End R M) (h_cap : horizon_capacitance 𝒯 = 0) :
    HorizonDefectBlock 𝒯 = ⊥ ∧
    Module.finrank R (HorizonDefectBlock 𝒯) = 0 := by
  unfold horizon_capacitance at h_cap
  have hfin : Module.finrank R (HorizonDefectBlock 𝒯) = 0 :=
    Int.ofNat_eq_zero.mp h_cap
  exact ⟨Submodule.finrank_eq_zero.mp hfin, hfin⟩

/-- **Stage $\mathfrak{MH}_4$ Theorem (`time_requires_horizon` — Deconfabulated Constructive Proof):**
If the Modular Hamiltonian $K \in \mathrm{End}_R(M)$ is supported on the Horizon Defect Block
($\mathcal{T} K = K$) and the Horizon Capacitance vanishes (`horizon_capacitance 𝒯 = 0`), then:
1. `HorizonDefectBlock 𝒯 = ⊥`;
2. `LinearMap.range K = ⊥`;
3. **`K = 0` identically** (Modular Time cannot flow without a horizon defect);
4. For any grading/conjugation $J_\Delta$, `supertrace J_Δ K = 0`. -/
theorem time_requires_horizon
    (𝒯 J_Δ K : Module.End R M)
    (h_support : 𝒯 * K = K)
    (h_trivial_horizon : horizon_capacitance 𝒯 = 0) :
    HorizonDefectBlock 𝒯 = ⊥ ∧
    LinearMap.range K = ⊥ ∧
    K = 0 ∧
    supertrace J_Δ K = 0 := by
  have hbot : HorizonDefectBlock 𝒯 = ⊥ :=
    (horizonDefectBlock_eq_bot_of_capacitance_zero 𝒯 h_trivial_horizon).1
  have hle : LinearMap.range K ≤ HorizonDefectBlock 𝒯 :=
    range_le_horizonDefectBlock_of_mul_eq_right 𝒯 K h_support
  rw [hbot] at hle
  have hrange : LinearMap.range K = ⊥ := le_bot_iff.mp hle
  have hK : K = 0 := LinearMap.range_eq_bot.mp hrange
  have hstr : supertrace J_Δ K = 0 := by
    unfold supertrace
    rw [hK, mul_zero, map_zero]
  exact ⟨hbot, hrange, hK, hstr⟩

/-- **Operator-Trace Horizon Existence Theorem (`time_requires_horizon_trace_capacitance`):**
Over any characteristic-zero field `R`, if the Modular Hamiltonian $K \in \mathrm{End}_R(M)$
is supported on the Horizon Defect Block ($\mathcal{T} K = K$) and the operator-trace
capacitance on $Q_0$ vanishes (`horizonTraceCapacitance 𝒯 = 0`), then:
1. `horizon_capacitance 𝒯 = 0`;
2. `HorizonDefectBlock 𝒯 = ⊥`;
3. `LinearMap.range K = ⊥`;
4. **`K = 0` identically** and `supertrace J_Δ K = 0`. -/
theorem time_requires_horizon_trace_capacitance
    [CharZero R]
    (𝒯 J_Δ K : Module.End R M)
    (h_support : 𝒯 * K = K)
    (h_trace_zero : horizonTraceCapacitance 𝒯 = 0) :
    horizon_capacitance 𝒯 = 0 ∧
    HorizonDefectBlock 𝒯 = ⊥ ∧
    LinearMap.range K = ⊥ ∧
    K = 0 ∧
    supertrace J_Δ K = 0 := by
  have h_eq_cap := (horizonDefectRestriction_eq_id_and_trace_eq_capacitance 𝒯).2.2.1
  rw [h_trace_zero] at h_eq_cap
  have h_cap_zero : horizon_capacitance 𝒯 = 0 :=
    Int.cast_eq_zero.mp h_eq_cap.symm
  have h_triv := time_requires_horizon 𝒯 J_Δ K h_support h_cap_zero
  exact ⟨h_cap_zero, h_triv⟩

/-- **Contrapositive Horizon Existence Theorem (`nonzero_time_forces_positive_horizon_capacitance`):**
Whenever a non-zero Modular Hamiltonian $K \ne 0$ is anchored to the horizon ($\mathcal{T} K = K$),
the Horizon Capacitance is strictly positive (`0 < horizon_capacitance 𝒯`). -/
theorem nonzero_time_forces_positive_horizon_capacitance
    (𝒯 K : Module.End R M)
    (h_support : 𝒯 * K = K)
    (hK_ne : K ≠ 0) :
    0 < horizon_capacitance 𝒯 ∧ horizon_capacitance 𝒯 ≠ 0 := by
  have hcap_ne : horizon_capacitance 𝒯 ≠ 0 := by
    intro hzero
    have hK0 := (time_requires_horizon 𝒯 1 K h_support hzero).2.2.1
    exact hK_ne hK0
  have hnonneg : 0 ≤ horizon_capacitance 𝒯 := by
    unfold horizon_capacitance
    exact Int.natCast_nonneg _
  exact ⟨lt_of_le_of_ne hnonneg hcap_ne.symm, hcap_ne⟩

end TimeRequiresHorizon

/-!
## Section 6 ($\mathfrak{MH}_5$): Master Thermodynamic–Dynamic Closure Synthesis
-/

/-- **Stage $\mathfrak{MH}_5$ Master Theorem (`mh5_master_modular_hamiltonian_horizon_capacitance_synthesis`):**
Unifies the 5-stage covering poset ($\mathfrak{MH}_1 \prec \dots \prec \mathfrak{MH}_5$) with:
1. ($\mathfrak{MH}_1$) Logarithmic Modular Hamiltonian $K(\delta) = -\log\delta$ with
   $K(1) = 0$ and sheet-inversion negation $K(\delta^{-1}) = -K(\delta)$;
2. ($\mathfrak{MH}_2$) Tomita–Takesaki conjugation $J_\Delta K J_\Delta = -K \iff \mathrm{IsOddOperator}\,J_\Delta\,K$
   and twin-sheet time reversal $K(J_\Delta v) = -J_\Delta(K v)$;
3. ($\mathfrak{MH}_3$) Exact 5-bit horizon capacitance quantization `horizon_capacitance Γ = 5`,
   `witten_index Γ = 0`, and $\dim_R M = 10$ for the $(5,5)$ split vacuum;
4. ($\mathfrak{MH}_4$) Constructive `time_requires_horizon` ($\mathcal{T} K = K \wedge \mathrm{horizon\_capacitance}(\mathcal{T}) = 0 \implies K = 0$)
   and its contrapositive ($K \ne 0 \implies 0 < \mathrm{horizon\_capacitance}(\mathcal{T})$). -/
theorem mh5_master_modular_hamiltonian_horizon_capacitance_synthesis
    {R M : Type*} [Field R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
    [FiniteDimensional R M]
    (δ : ℝ) (hδ : 0 < δ)
    (Γ J_Δ 𝒯 K K_triv : Module.End R M)
    (h_krein : IsKreinSymmetry Γ)
    (h_left : Module.finrank R (Ego Γ) = 5)
    (h_right : Module.finrank R (Anima Γ) = 5)
    (hJ : J_Δ * J_Δ = 1)
    (hconj : J_Δ * K * J_Δ = -K)
    (h_triv_support : 𝒯 * K_triv = K_triv)
    (h_triv_cap : horizon_capacitance 𝒯 = 0) :
    (ModularHamiltonianStage.coverEdge
        .mh1_logarithmic_modular_defect .mh2_tomita_conjugation_twin_sheet_reversal ∧
     ModularHamiltonianStage.coverEdge
        .mh2_tomita_conjugation_twin_sheet_reversal .mh3_holographic_five_bit_capacitance_quantization ∧
     ModularHamiltonianStage.coverEdge
        .mh3_holographic_five_bit_capacitance_quantization .mh4_time_requires_horizon_defect ∧
     ModularHamiltonianStage.coverEdge
        .mh4_time_requires_horizon_defect .mh5_master_thermodynamic_dynamic_closure) ∧
    (modularLogEigenvalue 1 = 0 ∧
     modularLogEigenvalue δ⁻¹ = -modularLogEigenvalue δ ∧
     Real.exp (-modularLogEigenvalue δ) = δ) ∧
    (IsOddOperator J_Δ K ∧ ∀ v : M, K (J_Δ v) = - J_Δ (K v)) ∧
    (horizon_capacitance Γ = 5 ∧ witten_index Γ = 0 ∧ Module.finrank R M = 10) ∧
    (K_triv = 0 ∧ supertrace J_Δ K_triv = 0) := by
  have hposet := ModularHamiltonianStage.poset_covering_chain
  have hlog := modularLogEigenvalue_properties δ δ δ hδ hδ hδ
  have hodd := (modular_conjugation_iff_isOddOperator J_Δ K hJ).mp hconj
  have hrev : ∀ v : M, K (J_Δ v) = - J_Δ (K v) := by
    intro v
    have h1 : (J_Δ * K) v = (-(K * J_Δ)) v := congrArg (fun T : Module.End R M => T v) hodd
    have h2 : J_Δ (K v) = - K (J_Δ v) := by
      rw [Module.End.mul_apply, LinearMap.neg_apply, Module.End.mul_apply] at h1
      exact h1
    calc
      K (J_Δ v) = -(-K (J_Δ v)) := (neg_neg _).symm
      _ = - J_Δ (K v) := by rw [← h2]
  have hcap5 := holographic_capacitance_split_five_five_quantization Γ h_krein h_left h_right
  have htriv := time_requires_horizon 𝒯 J_Δ K_triv h_triv_support h_triv_cap
  exact ⟨hposet,
    ⟨hlog.1, hlog.2.1, hlog.2.2.2⟩,
    ⟨hodd, hrev⟩,
    ⟨hcap5.2.1, hcap5.2.2.1, hcap5.2.2.2.1⟩,
    ⟨htriv.2.2.1, htriv.2.2.2⟩⟩

end InfoGeometry.GrandUnification.Dynamics
