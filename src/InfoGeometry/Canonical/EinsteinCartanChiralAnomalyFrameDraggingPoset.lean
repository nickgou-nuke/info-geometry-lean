/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge
import InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset
import InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty

/-!
# Operator Einstein–Cartan Gravity: Chiral Einstein Anomaly, Spin Frame Dragging, Soldered Cartan–Ehresmann Split & Fisher–Riemann Cramér–Rao Poset (`𝔈₁ ≺ ⋯ ≺ 𝔈₈`)

This module formalizes in native Mathlib (`Lean 4`) the 8-stage Acyclic Causal Poset
(`EinsteinCartanAnomalyStage : 𝔈₁ ≺ 𝔈₂ ≺ 𝔈₃ ≺ 𝔈₄ ≺ 𝔈₅ ≺ 𝔈₆ ≺ 𝔈₇ ≺ 𝔈₈`) governing the
non-commutative operator lift of Einstein–Cartan gravity:

1. **Stage `𝔈₁` (`archetype_E1_chiral_cut_and_maurer_cartan_solder_forms`)**:
   Chiral parity involution `S_P = invS P = 2P - 1`, symmetric Maurer–Cartan solder form
   `Φ = genPhi P A C = N_+ + N_-`, skew Maurer–Cartan 1-form `J = genJ P A C = [P, a] = N_+ - N_-`,
   and chiral duality `S_P * Φ = J`, `S_P * J = Φ`.
2. **Stage `𝔈₂` (`archetype_E2_operator_fisher_metric_and_spin_dipole_curvature`)**:
   Operator Fisher metric `V = genV P A C = {N_+, N_-} = Φ² = -J²`, spin-dipole curvature
   `Σ = genSig P A C = [N_+, N_-] = J * Φ = -Φ * J`, Grassmannian idempotency defect
   `(P + Φ)² - (P + Φ) = V`, and Maurer–Cartan curvature `F_MC = [P, Φ] + Φ² = J + V`.
3. **Stage `𝔈₃` (`archetype_E3_para_kahler_lock_and_levi_civita_aporia`)**:
   Para-Kähler creation lock `V = S_P * Σ = Σ * S_P` and `Σ = S_P * V = V * S_P`, establishing
   `Σ = 0 ↔ V = 0`, together with the **Levi-Civita Socratic Aporia**: forcing the tetrads to
   commute (`[Φ, J] = 0`) forces `(2 : ℤ) • V = 0` (and `V = 0`, `Σ = 0` in any 2-torsion-free ring).
4. **Stage `𝔈₄` (`chiralEinsteinAnomaly`, `archetype_E4_chiral_einstein_anomaly_cocycle`)**:
   The **Chiral Einstein Anomaly** `chiralEinsteinAnomaly P A C := S_P * [Φ, J] = -((2 : ℤ) • V)`,
   proving that twice the symmetric Fisher metric `V` is the chiral anomaly of the non-commuting
   vielbeins `[Φ, J] = -((2 : ℤ) • Σ)`.
5. **Stage `𝔈₅` (`dressedSpinTorsion`, `archetype_E5_spin_frame_dragging_and_dressed_torsion`)**:
   Exact spin-vielbein anticommutation `{Σ, Φ} = {Σ, J} = 0`, **Spin Frame Dragging**
   `[Σ, Φ] = (2 : ℤ) • (V * J)` and `[Σ, J] = (2 : ℤ) • (V * Φ)`, and dressed covariant torsion
   `𝒯_Σ(Φ) := [P + Σ, Φ] = (1 + (2 : ℤ) • V) * J`.
6. **Stage `𝔈₆` (`solderedConnPhi`, `solderedConnJ`, `jordanAssociator`,
   `archetype_E6_soldered_cartan_ehresmann_and_jordan_associator`)**:
   Soldered Cartan–Ehresmann commutator `[Σ + Φ, Σ + J] = -((2 : ℤ) • Σ) + (2 : ℤ) • (V * (Φ - J))`
   and the Universal Grade-3 Jordan Associator
   `𝒜(N_-, N_+, N_+) = {{N_-, N_+}, N_+} - {N_-, {N_+, N_+}} = [Σ, N_+] = (2 : ℤ) • (V * N_+)`.
7. **Stage `𝔈₇` (`archetype_E7_general_einstein_cartan_split_and_bianchi`)**:
   General Einstein–Cartan gauge split `[Ω₁ + Φ₁, Ω₂ + Φ₂] = ℛ₁₂ + 𝒯₁₂` into even Riemann–Cartan
   curvature (`[S_P, ℛ₁₂] = 0`) and odd Élie Cartan torsion (`{S_P, 𝒯₁₂} = 0`), with the exact
   non-Abelian Bianchi–Cartan identity `∑_cyc [𝒜₁, ℛ₂₃ + 𝒯₂₃] = 0`.
8. **Stage `𝔈₈` (`archetype_E8_centrifugal_dragging_and_fisher_cramer_rao`,
   `einstein_cartan_chiral_anomaly_frame_dragging_master_synthesis`,
   `einstein_cartan_frame_dragging_matrix_witness`)**:
   4th-order centrifugal frame dragging `[Σ, [Σ, Φ]] = (4 : ℤ) • (V² * Φ)`, Fisher–Riemann
   sectional curvature `-[Φ, [Φ, J]] = -((4 : ℤ) • (V * J)) = -((2 : ℤ) • [Σ, Φ])`, and the
   Hilbert-space Operator Cramér–Rao gravitational bound
   `g(X,X) g(Y,Y) ≥ g(X,Y)² + (1/4) Ω(X,Y)² ≥ (1/4) Ω(X,Y)²`.

## i. Overview

Formalizes the 8-stage `EinsteinCartanAnomalyStage` poset (`𝔈₁ ≺ ⋯ ≺ 𝔈₈`) for non-commutative
operator Einstein–Cartan gravity, chiral Einstein anomaly, spin frame dragging, and the
Fisher–Riemann Cramér–Rao bound.

## ii. Key results

- `archetype_E1_chiral_cut_and_maurer_cartan_solder_forms` through
  `archetype_E8_centrifugal_dragging_and_fisher_cramer_rao`
- `einstein_cartan_chiral_anomaly_frame_dragging_master_synthesis`

## iii. Table of contents

- Section 0: The 8-Stage Acyclic Causal Poset (`𝔈₁ ≺ ⋯ ≺ 𝔈₈`)
- Sections 1–8: Stages `𝔈₁` through `𝔈₈`

## iv. References

- É. Cartan, *Sur une généralisation de la notion de courbure de Riemann et les espaces à torsion* (1922).

#### BUCKET 1: CLOSED FINITE THEOREMS
- `EinsteinCartanAnomalyStage.causalEdge_acyclic`, `einstein_cartan_frame_dragging_matrix_witness`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `archetype_E1_chiral_cut_and_maurer_cartan_solder_forms` through
  `einstein_cartan_chiral_anomaly_frame_dragging_master_synthesis`.

#### BUCKET 3: OPEN CLOSURE DEBT
- Continuum 4-manifold spin-connection integration beyond algebraic Peirce–Cartan operators.
-/

noncomputable section

namespace InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Canonical.ChiralCondensateGMORBanksCasherNJLPoset
open InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset
open InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty
open InfoGeometry.QuantumGeometry.Projective
open scoped Matrix InnerProductSpace

/-! ===========================================================================
    Section 0: The 8-Stage Acyclic Causal Poset (𝔈₁ ≺ 𝔈₂ ≺ ⋯ ≺ 𝔈₈)
    =========================================================================== -/

/-- The 8-stage epistemic compilation poset (`𝔈₁ ≺ ⋯ ≺ 𝔈₈`) of Operator Einstein–Cartan Gravity,
the Chiral Einstein Anomaly, Spin Frame Dragging, and the Fisher–Riemann Cramér–Rao Bound. -/
inductive EinsteinCartanAnomalyStage : Type
  | E1_ChiralCutAndMaurerCartanSolderForms
  | E2_OperatorFisherMetricAndSpinDipoleCurvature
  | E3_ParaKahlerLockAndLeviCivitaAporia
  | E4_ChiralEinsteinAnomalyCocycle
  | E5_SpinFrameDraggingAndDressedTorsion
  | E6_SolderedCartanEhresmannAndJordanAssociator
  | E7_GeneralEinsteinCartanSplitAndBianchi
  | E8_CentrifugalDraggingAndFisherCramerRaoBound
  deriving DecidableEq, Repr, Inhabited

namespace EinsteinCartanAnomalyStage

/-- Strictly monotone integer rank `0..7` for `EinsteinCartanAnomalyStage`. -/
def rank : EinsteinCartanAnomalyStage → ℕ
  | .E1_ChiralCutAndMaurerCartanSolderForms        => 0
  | .E2_OperatorFisherMetricAndSpinDipoleCurvature => 1
  | .E3_ParaKahlerLockAndLeviCivitaAporia          => 2
  | .E4_ChiralEinsteinAnomalyCocycle               => 3
  | .E5_SpinFrameDraggingAndDressedTorsion         => 4
  | .E6_SolderedCartanEhresmannAndJordanAssociator => 5
  | .E7_GeneralEinsteinCartanSplitAndBianchi       => 6
  | .E8_CentrifugalDraggingAndFisherCramerRaoBound => 7

/-- `rank` is injective on `EinsteinCartanAnomalyStage`. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrderEinsteinCartanAnomalyStage :
    LinearOrder EinsteinCartanAnomalyStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal dependency edge `a ≺ b` in the `𝔈₁..𝔈₈` poset, including both the linear
spine and the diamond fork `𝔈₃ ≺ 𝔈₄, 𝔈₅` and join `𝔈₄, 𝔈₅ ≺ 𝔈₆`. -/
def causalEdge : EinsteinCartanAnomalyStage → EinsteinCartanAnomalyStage → Prop
  | .E1_ChiralCutAndMaurerCartanSolderForms,
    .E2_OperatorFisherMetricAndSpinDipoleCurvature => True
  | .E2_OperatorFisherMetricAndSpinDipoleCurvature,
    .E3_ParaKahlerLockAndLeviCivitaAporia => True
  | .E3_ParaKahlerLockAndLeviCivitaAporia,
    .E4_ChiralEinsteinAnomalyCocycle => True
  | .E3_ParaKahlerLockAndLeviCivitaAporia,
    .E5_SpinFrameDraggingAndDressedTorsion => True
  | .E4_ChiralEinsteinAnomalyCocycle,
    .E5_SpinFrameDraggingAndDressedTorsion => True
  | .E4_ChiralEinsteinAnomalyCocycle,
    .E6_SolderedCartanEhresmannAndJordanAssociator => True
  | .E5_SpinFrameDraggingAndDressedTorsion,
    .E6_SolderedCartanEhresmannAndJordanAssociator => True
  | .E6_SolderedCartanEhresmannAndJordanAssociator,
    .E7_GeneralEinsteinCartanSplitAndBianchi => True
  | .E7_GeneralEinsteinCartanSplitAndBianchi,
    .E8_CentrifugalDraggingAndFisherCramerRaoBound => True
  | _, _ => False

/-- Every direct causal edge strictly increases `rank`. -/
theorem causalEdge_strict_rank_mono {a b : EinsteinCartanAnomalyStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

/-- `causalEdge` is irreflexive. -/
theorem causalEdge_irrefl (a : EinsteinCartanAnomalyStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

/-- Every transitive causal path strictly increases `rank`. -/
theorem transGen_causalEdge_strict_rank_mono {a b : EinsteinCartanAnomalyStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hbc)

/-- Strict acyclicity of the 8-stage `EinsteinCartanAnomalyStage` causal poset. -/
theorem causalEdge_acyclic (a : EinsteinCartanAnomalyStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

/-- Complete 8-stage causal spine and diamond fork/join witness. -/
theorem causalEdge_chain_and_diamond :
    causalEdge .E1_ChiralCutAndMaurerCartanSolderForms
      .E2_OperatorFisherMetricAndSpinDipoleCurvature ∧
    causalEdge .E2_OperatorFisherMetricAndSpinDipoleCurvature
      .E3_ParaKahlerLockAndLeviCivitaAporia ∧
    causalEdge .E3_ParaKahlerLockAndLeviCivitaAporia
      .E4_ChiralEinsteinAnomalyCocycle ∧
    causalEdge .E3_ParaKahlerLockAndLeviCivitaAporia
      .E5_SpinFrameDraggingAndDressedTorsion ∧
    causalEdge .E4_ChiralEinsteinAnomalyCocycle
      .E6_SolderedCartanEhresmannAndJordanAssociator ∧
    causalEdge .E5_SpinFrameDraggingAndDressedTorsion
      .E6_SolderedCartanEhresmannAndJordanAssociator ∧
    causalEdge .E6_SolderedCartanEhresmannAndJordanAssociator
      .E7_GeneralEinsteinCartanSplitAndBianchi ∧
    causalEdge .E7_GeneralEinsteinCartanSplitAndBianchi
      .E8_CentrifugalDraggingAndFisherCramerRaoBound := by
  repeat' constructor

end EinsteinCartanAnomalyStage

/-! ===========================================================================
    Section 1: Stage 𝔈₁ — Chiral Cut & Maurer–Cartan Solder Forms
    =========================================================================== -/

section StageE1

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔈₁` (`archetype_E1_chiral_cut_and_maurer_cartan_solder_forms`)**:
Over any associative ring `[Ring B]` with idempotent `P * P = P`, chiral involution
`S_P = invS P = 2P - 1`, symmetric vielbein (solder form) `Φ = genPhi P A C = N_+ + N_-`,
and skew Maurer–Cartan 1-form `J = genJ P A C = N_+ - N_-`:
1. `invS P * invS P = 1`,
2. `conePlus P A * conePlus P A = 0` and `coneMinus P C * coneMinus P C = 0`,
3. `invS P * genPhi P A C = genJ P A C` and `genPhi P A C * invS P = -genJ P A C`,
4. `invS P * genJ P A C = genPhi P A C` and `genJ P A C * invS P = -genPhi P A C`,
5. `anticomm (invS P) (genPhi P A C) = 0` and `anticomm (invS P) (genJ P A C) = 0`,
6. `comm P (genPhi P A C) = genJ P A C` and `comm P (genJ P A C) = genPhi P A C`. -/
theorem archetype_E1_chiral_cut_and_maurer_cartan_solder_forms (A C : B) :
    invS P * invS P = 1 ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    invS P * genPhi P A C = genJ P A C ∧
    genPhi P A C * invS P = -genJ P A C ∧
    invS P * genJ P A C = genPhi P A C ∧
    genJ P A C * invS P = -genPhi P A C ∧
    OperatorAlgebra.PeirceSpine.anticomm (invS P) (genPhi P A C) = 0 ∧
    OperatorAlgebra.PeirceSpine.anticomm (invS P) (genJ P A C) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm P (genPhi P A C) = genJ P A C ∧
    OperatorAlgebra.PeirceSpine.comm P (genJ P A C) = genPhi P A C := by
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP⟩

end StageE1

/-! ===========================================================================
    Section 2: Stage 𝔈₂ — Operator Fisher Metric V & Spin-Dipole Curvature Σ
    =========================================================================== -/

section StageE2

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔈₂` (`archetype_E2_operator_fisher_metric_and_spin_dipole_curvature`)**:
For the symmetric Fisher metric `V = genV P A C = {N_+, N_-}` and antisymmetric spin-dipole
connection `Σ = genSig P A C = [N_+, N_-]`:
1. `genPhi P A C * genPhi P A C = genV P A C` and `genJ P A C * genJ P A C = -genV P A C`,
2. `genJ P A C * genPhi P A C = genSig P A C` and `genPhi P A C * genJ P A C = -genSig P A C`,
3. `genSig P A C * genSig P A C = genV P A C * genV P A C`,
4. `(P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C`
   (the deformed projector fails idempotency by the exact Fisher metric `V`),
5. `peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C`
   (`F_MC(P, A, C) = [P, Φ] + Φ² = J + V`),
6. `comm P (genSig P A C) + genSig P A C * genSig P A C = genV P A C * genV P A C`
   (`F_0(Σ) = V²`). -/
theorem archetype_E2_operator_fisher_metric_and_spin_dipole_curvature (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    genJ P A C * genPhi P A C = genSig P A C ∧
    genPhi P A C * genJ P A C = -genSig P A C ∧
    genSig P A C * genSig P A C = genV P A C * genV P A C ∧
    (P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C ∧
    peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C ∧
    OperatorAlgebra.PeirceSpine.comm P (genSig P A C) +
      genSig P A C * genSig P A C = genV P A C * genV P A C := by
  unfold peirceMaurerCartanCurvature peirceGradingDeriv
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

end StageE2

/-! ===========================================================================
    Section 3: Stage 𝔈₃ — Para-Kähler Creation Lock & The Levi-Civita Aporia
    =========================================================================== -/

section StageE3

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔈₃` (`archetype_E3_para_kahler_lock_and_levi_civita_aporia`)**:
1. **Para-Kähler Creation Lock**:
   `invS P * genSig P A C = genV P A C`, `genSig P A C * invS P = genV P A C`,
   `invS P * genV P A C = genSig P A C`, and `genV P A C * invS P = genSig P A C`.
2. **Equivalence of Non-Zero Spin Curvature and Non-Zero Fisher Metric**:
   `genSig P A C = 0 ↔ genV P A C = 0`.
3. **The Levi-Civita Aporia (Torsion-Free Commutativity Annihilates the Metric)**:
   - If `genSig P A C = 0`, then `genV P A C = 0`, `genPhi P A C * genPhi P A C = 0`, and
     `genJ P A C * genJ P A C = 0`.
   - If the dual tetrads commute (`comm (genPhi P A C) (genJ P A C) = 0`), then
     `(2 : ℤ) • genSig P A C = 0` and `(2 : ℤ) • genV P A C = 0`. -/
theorem archetype_E3_para_kahler_lock_and_levi_civita_aporia (A C : B) :
    invS P * genSig P A C = genV P A C ∧
    genSig P A C * invS P = genV P A C ∧
    invS P * genV P A C = genSig P A C ∧
    genV P A C * invS P = genSig P A C ∧
    (genSig P A C = 0 ↔ genV P A C = 0) ∧
    (genSig P A C = 0 →
      genV P A C = 0 ∧
      genPhi P A C * genPhi P A C = 0 ∧
      genJ P A C * genJ P A C = 0) ∧
    (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) = 0 →
      (2 : ℤ) • genSig P A C = 0 ∧ (2 : ℤ) • genV P A C = 0) := by
  have hSV : invS P * genSig P A C = genV P A C := by peirce_nf hP
  have hVS : genSig P A C * invS P = genV P A C := by peirce_nf hP
  have hSSig : invS P * genV P A C = genSig P A C := by peirce_nf hP
  have hSigS : genV P A C * invS P = genSig P A C := by peirce_nf hP
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
  have hJSq : genJ P A C * genJ P A C = -genV P A C := by peirce_nf hP
  have hComm :
      OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) =
        -((2 : ℤ) • genSig P A C) := by peirce_nf hP
  have hAnom :
      invS P * OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) =
        -((2 : ℤ) • genV P A C) := by peirce_nf hP
  refine ⟨hSV, hVS, hSSig, hSigS, ?_, ?_, ?_⟩
  · constructor
    · intro hSig0
      rw [← hSV, hSig0, mul_zero]
    · intro hV0
      rw [← hSSig, hV0, mul_zero]
  · intro hSig0
    have hV0 : genV P A C = 0 := by rw [← hSV, hSig0, mul_zero]
    refine ⟨hV0, ?_, ?_⟩
    · rw [hPhiSq, hV0]
    · rw [hJSq, hV0, neg_zero]
  · intro hComm0
    have h2Sig : (2 : ℤ) • genSig P A C = 0 := by
      have hNeg : -((2 : ℤ) • genSig P A C) = 0 := by rw [← hComm, hComm0]
      exact neg_eq_zero.mp hNeg
    have h2V : (2 : ℤ) • genV P A C = 0 := by
      have hNeg : -((2 : ℤ) • genV P A C) = 0 := by
        rw [← hAnom, hComm0, mul_zero]
      exact neg_eq_zero.mp hNeg
    exact ⟨h2Sig, h2V⟩

/-- In a `ℤ`-torsion-free ring (`[NoZeroSMulDivisors ℤ B]`), commuting vielbeins
`comm (genPhi P A C) (genJ P A C) = 0` force `genV P A C = 0` and `genSig P A C = 0`. -/
theorem levi_civita_commuting_frames_force_zero_metric
    [NoZeroSMulDivisors ℤ B] (A C : B)
    (hComm0 : OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) = 0) :
    genV P A C = 0 ∧ genSig P A C = 0 := by
  have h2 := (archetype_E3_para_kahler_lock_and_levi_civita_aporia hP A C).2.2.2.2.2.2 hComm0
  have h2ne : (2 : ℤ) ≠ 0 := by decide
  exact ⟨(smul_eq_zero.mp h2.2).resolve_left h2ne,
         (smul_eq_zero.mp h2.1).resolve_left h2ne⟩

end StageE3

/-! ===========================================================================
    Section 4: Stage 𝔈₄ — The Chiral Einstein Anomaly Cocycle S_P[Φ, J] = -2V
    =========================================================================== -/

section StageE4

variable {B : Type*} [Ring B]

/-- The **Chiral Einstein Anomaly** `S_P [Φ, J] = invS P * comm (genPhi P A C) (genJ P A C)`. -/
def chiralEinsteinAnomaly (P A C : B) : B :=
  invS P * OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)

variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔈₄` (`archetype_E4_chiral_einstein_anomaly_cocycle`)**:
1. The commutator of the dual vielbeins generates minus twice the spin-dipole connection:
   `comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C)`,
2. Projecting `[Φ, J]` against the chiral involution `S_P` produces minus twice the Operator
   Fisher Metric `V`:
   `chiralEinsteinAnomaly P A C = -((2 : ℤ) • genV P A C)` and
   `comm (genPhi P A C) (genJ P A C) * invS P = -((2 : ℤ) • genV P A C)`,
3. The Chiral Einstein Anomaly is strictly even (`comm (invS P) (chiralEinsteinAnomaly P A C) = 0`)
   and centralizes the tangent bundle (`comm (chiralEinsteinAnomaly P A C) (genPhi P A C) = 0`
   and `comm (chiralEinsteinAnomaly P A C) (genJ P A C) = 0`). -/
theorem archetype_E4_chiral_einstein_anomaly_cocycle (A C : B) :
    OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) =
      -((2 : ℤ) • genSig P A C) ∧
    chiralEinsteinAnomaly P A C = -((2 : ℤ) • genV P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) * invS P =
      -((2 : ℤ) • genV P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (invS P) (chiralEinsteinAnomaly P A C) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (chiralEinsteinAnomaly P A C) (genPhi P A C) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (chiralEinsteinAnomaly P A C) (genJ P A C) = 0 := by
  unfold chiralEinsteinAnomaly
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

end StageE4

/-! ===========================================================================
    Section 5: Stage 𝔈₅ — Spin Frame Dragging & Dressed Covariant Torsion
    =========================================================================== -/

section StageE5

variable {B : Type*} [Ring B]

/-- The dressed Einstein–Cartan spin-torsion `𝒯_Σ(Φ) := [P + Σ, Φ]`. -/
def dressedSpinTorsion (P A C : B) : B :=
  OperatorAlgebra.PeirceSpine.comm (P + genSig P A C) (genPhi P A C)

variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔈₅` (`archetype_E5_spin_frame_dragging_and_dressed_torsion`)**:
1. **Spin–Vielbein Anticommutation**:
   `anticomm (genSig P A C) (genPhi P A C) = 0` and `anticomm (genSig P A C) (genJ P A C) = 0`.
2. **Exact Chiral Spin Frame Dragging**:
   `comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)` (`[Σ, Φ] = 2V J`)
   and `comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C)` (`[Σ, J] = 2V Φ`).
3. **Corner-Level Frame Dragging**:
   `comm (genSig P A C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A)` and
   `comm (genSig P A C) (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C))`.
4. **Dressed Covariant Torsion**:
   `dressedSpinTorsion P A C = genJ P A C + (2 : ℤ) • (genV P A C * genJ P A C)` and
   `dressedSpinTorsion P A C = (1 + (2 : ℤ) • genV P A C) * genJ P A C` (`𝒯_Σ(Φ) = (1 + 2V) J`). -/
theorem archetype_E5_spin_frame_dragging_and_dressed_torsion (A C : B) :
    OperatorAlgebra.PeirceSpine.anticomm (genSig P A C) (genPhi P A C) = 0 ∧
    OperatorAlgebra.PeirceSpine.anticomm (genSig P A C) (genJ P A C) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genJ P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genJ P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C) (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C) (coneMinus P C) =
      -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    dressedSpinTorsion P A C =
      genJ P A C + (2 : ℤ) • (genV P A C * genJ P A C) ∧
    dressedSpinTorsion P A C =
      (1 + (2 : ℤ) • genV P A C) * genJ P A C := by
  unfold dressedSpinTorsion
  exact ⟨gemSpinPhi_anticomm hP A C,
         gemSpinJ_anticomm hP A C,
         gemFirstOrderLenseThirring hP A C,
         gemDualPrecession hP A C,
         gemCornerPrecession_plus hP A C,
         gemCornerPrecession_minus hP A C,
         by peirce_nf hP,
         gemDressedTorsion_eq hP A C⟩

end StageE5

/-! ===========================================================================
    Section 6: Stage 𝔈₆ — Soldered Cartan–Ehresmann Split & Grade-3 Jordan Associator
    =========================================================================== -/

section StageE6

variable {B : Type*} [Ring B]

/-- The soldered Cartan–Ehresmann connection `𝒜_Φ := Σ + Φ` along the symmetric vielbein `Φ`. -/
def solderedConnPhi (P A C : B) : B :=
  genSig P A C + genPhi P A C

/-- The soldered Cartan–Ehresmann connection `𝒜_J := Σ + J` along the dual 1-form `J`. -/
def solderedConnJ (P A C : B) : B :=
  genSig P A C + genJ P A C

/-- The universal Grade-3 Jordan associator `𝒜(X, Y, Z) := {{X, Y}, Z} - {X, {Y, Z}}`. -/
def jordanAssociator (X Y Z : B) : B :=
  OperatorAlgebra.PeirceSpine.anticomm (OperatorAlgebra.PeirceSpine.anticomm X Y) Z -
    OperatorAlgebra.PeirceSpine.anticomm X (OperatorAlgebra.PeirceSpine.anticomm Y Z)

/-- Universal identity relating the Jordan associator to the nested Lie commutator `[[Z, X], Y]`. -/
theorem jordanAssociator_eq_double_comm (X Y Z : B) :
    jordanAssociator X Y Z =
      OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm Z X) Y := by
  dsimp [jordanAssociator, OperatorAlgebra.PeirceSpine.anticomm,
    OperatorAlgebra.PeirceSpine.comm]
  noncomm_ring

variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔈₆` (`archetype_E6_soldered_cartan_ehresmann_and_jordan_associator`)**:
1. **Soldered Cartan–Ehresmann Commutator Split**:
   `comm (solderedConnPhi P A C) (solderedConnJ P A C) = -((2 : ℤ) • genSig P A C) + (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C))`
   (`[Σ + Φ, Σ + J] = -2Σ + 2V(Φ - J)`),
2. **Exact Even/Odd Parity Isolation**:
   `evenGrade P (comm (solderedConnPhi P A C) (solderedConnJ P A C)) = -((2 : ℤ) • genSig P A C)`
   (even Riemann–Cartan core in `𝔨`) and
   `oddGrade P (comm (solderedConnPhi P A C) (solderedConnJ P A C)) = (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C))`
   (odd spin-dragging torsion in `𝔭`),
3. **Grade-3 Jordan Associator Origin of Spin Frame Dragging**:
   `jordanAssociator (coneMinus P C) (conePlus P A) (conePlus P A) = comm (genSig P A C) (conePlus P A)`
   and `= (2 : ℤ) • (genV P A C * conePlus P A)`, while
   `jordanAssociator (conePlus P A) (coneMinus P C) (coneMinus P C) = (2 : ℤ) • (genV P A C * coneMinus P C)`,
   so their sum is `(2 : ℤ) • (genV P A C * genPhi P A C) = comm (genSig P A C) (genJ P A C)`
   and their difference is `(2 : ℤ) • (genV P A C * genJ P A C) = comm (genSig P A C) (genPhi P A C)`. -/
theorem archetype_E6_soldered_cartan_ehresmann_and_jordan_associator (A C : B) :
    OperatorAlgebra.PeirceSpine.comm (solderedConnPhi P A C) (solderedConnJ P A C) =
      -((2 : ℤ) • genSig P A C) +
        (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C)) ∧
    evenGrade P
        (OperatorAlgebra.PeirceSpine.comm (solderedConnPhi P A C) (solderedConnJ P A C)) =
      -((2 : ℤ) • genSig P A C) ∧
    oddGrade P
        (OperatorAlgebra.PeirceSpine.comm (solderedConnPhi P A C) (solderedConnJ P A C)) =
      (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C)) ∧
    jordanAssociator (coneMinus P C) (conePlus P A) (conePlus P A) =
      OperatorAlgebra.PeirceSpine.comm (genSig P A C) (conePlus P A) ∧
    jordanAssociator (coneMinus P C) (conePlus P A) (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    jordanAssociator (conePlus P A) (coneMinus P C) (coneMinus P C) =
      (2 : ℤ) • (genV P A C * coneMinus P C) ∧
    jordanAssociator (coneMinus P C) (conePlus P A) (conePlus P A) -
      jordanAssociator (conePlus P A) (coneMinus P C) (coneMinus P C) =
      OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C) := by
  unfold solderedConnPhi solderedConnJ jordanAssociator
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

end StageE6

/-! ===========================================================================
    Section 7: Stage 𝔈₇ — General Einstein–Cartan Gauge Split & Bianchi Identity
    =========================================================================== -/

section StageE7

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔈₇` (`archetype_E7_general_einstein_cartan_split_and_bianchi`)**:
For arbitrary gauge seeds `X₁, X₂, X₃` (generating even spin connections `Ω_i = evenGrade P X_i ∈ 𝔨`)
and frame seeds `Y₁, Y₂, Y₃` (generating odd tetrads `Φ_i = oddGrade P Y_i ∈ 𝔭`) with split
Cartan connections `𝒜_i = cartanSplitConnection P X_i Y_i = Ω_i + Φ_i`:
1. **Cartan Structure Decomposition**:
   `[𝒜₁, 𝒜₂] = riemannCartanCurvature P X₁ Y₁ X₂ Y₂ + elieCartanTorsion P X₁ Y₁ X₂ Y₂`,
2. **Chiral Parity of Riemann–Cartan Curvature (`∈ 𝔨`)**:
   `comm (invS P) (riemannCartanCurvature P X₁ Y₁ X₂ Y₂) = 0`,
3. **Chiral Parity of Élie Cartan Torsion (`∈ 𝔭`)**:
   `anticomm (invS P) (elieCartanTorsion P X₁ Y₁ X₂ Y₂) = 0`,
4. **Exact Non-Abelian Bianchi–Cartan Identity**:
   `[𝒜₁, ℛ₂₃ + 𝒯₂₃] + [𝒜₂, ℛ₃₁ + 𝒯₃₁] + [𝒜₃, ℛ₁₂ + 𝒯₁₂] = 0`. -/
theorem archetype_E7_general_einstein_cartan_split_and_bianchi
    (X₁ Y₁ X₂ Y₂ X₃ Y₃ : B) :
    OperatorAlgebra.PeirceSpine.comm
        (cartanSplitConnection P X₁ Y₁) (cartanSplitConnection P X₂ Y₂) =
      riemannCartanCurvature P X₁ Y₁ X₂ Y₂ + elieCartanTorsion P X₁ Y₁ X₂ Y₂ ∧
    OperatorAlgebra.PeirceSpine.comm (invS P)
        (riemannCartanCurvature P X₁ Y₁ X₂ Y₂) = 0 ∧
    OperatorAlgebra.PeirceSpine.anticomm (invS P)
        (elieCartanTorsion P X₁ Y₁ X₂ Y₂) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (cartanSplitConnection P X₁ Y₁)
        (riemannCartanCurvature P X₂ Y₂ X₃ Y₃ + elieCartanTorsion P X₂ Y₂ X₃ Y₃) +
      OperatorAlgebra.PeirceSpine.comm (cartanSplitConnection P X₂ Y₂)
        (riemannCartanCurvature P X₃ Y₃ X₁ Y₁ + elieCartanTorsion P X₃ Y₃ X₁ Y₁) +
      OperatorAlgebra.PeirceSpine.comm (cartanSplitConnection P X₃ Y₃)
        (riemannCartanCurvature P X₁ Y₁ X₂ Y₂ + elieCartanTorsion P X₁ Y₁ X₂ Y₂) = 0 := by
  have h12 := (archetype_K6_elie_cartan_torsion_annihilation_and_macdowell_mansouri hP X₁ Y₁ X₂ Y₂).1
  have h23 := (archetype_K6_elie_cartan_torsion_annihilation_and_macdowell_mansouri hP X₂ Y₂ X₃ Y₃).1
  have h31 := (archetype_K6_elie_cartan_torsion_annihilation_and_macdowell_mansouri hP X₃ Y₃ X₁ Y₁).1
  have hEE :
      OperatorAlgebra.PeirceSpine.comm (invS P)
        (OperatorAlgebra.PeirceSpine.comm (evenGrade P X₁) (evenGrade P X₂)) = 0 := by
    peirce_nf hP
  have hOO :
      OperatorAlgebra.PeirceSpine.comm (invS P)
        (OperatorAlgebra.PeirceSpine.comm (oddGrade P Y₁) (oddGrade P Y₂)) = 0 := by
    peirce_nf hP
  have hEO :
      OperatorAlgebra.PeirceSpine.anticomm (invS P)
        (OperatorAlgebra.PeirceSpine.comm (evenGrade P X₁) (oddGrade P Y₂)) = 0 := by
    peirce_nf hP
  have hOE :
      OperatorAlgebra.PeirceSpine.anticomm (invS P)
        (OperatorAlgebra.PeirceSpine.comm (oddGrade P Y₁) (evenGrade P X₂)) = 0 := by
    peirce_nf hP
  refine ⟨h12, ?_, ?_, ?_⟩
  · unfold riemannCartanCurvature
    have hLin : ∀ U V : B,
        OperatorAlgebra.PeirceSpine.comm (invS P) (U + V) =
          OperatorAlgebra.PeirceSpine.comm (invS P) U +
            OperatorAlgebra.PeirceSpine.comm (invS P) V := by
      intro U V; dsimp [OperatorAlgebra.PeirceSpine.comm]; noncomm_ring
    rw [hLin, hEE, hOO, add_zero]
  · unfold elieCartanTorsion
    have hLin : ∀ U V : B,
        OperatorAlgebra.PeirceSpine.anticomm (invS P) (U + V) =
          OperatorAlgebra.PeirceSpine.anticomm (invS P) U +
            OperatorAlgebra.PeirceSpine.anticomm (invS P) V := by
      intro U V; dsimp [OperatorAlgebra.PeirceSpine.anticomm]; noncomm_ring
    rw [hLin, hEO, hOE, add_zero]
  · rw [← h23, ← h31, ← h12]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring

end StageE7

/-! ===========================================================================
    Section 8: Stage 𝔈₈ — 4th-Order Centrifugal Frame Dragging, Fisher Sectional
    Curvature, Operator Cramér–Rao Bound & Master Synthesis
    =========================================================================== -/

section StageE8

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔈₈` (`archetype_E8_centrifugal_dragging_and_fisher_cramer_rao`)**:
1. **4th-Order Centrifugal Spin Frame Dragging**:
   `comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) = (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)`
   (`[Σ, [Σ, Φ]] = 4 V² Φ`) and
   `comm (genSig P A C) (comm (genSig P A C) (genJ P A C)) = (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)`
   (`[Σ, [Σ, J]] = 4 V² J`),
2. **Fisher–Riemann Double-Commutator Sectional Curvature & Clocking Lock**:
   `-comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) = -((4 : ℤ) • (genV P A C * genJ P A C))`
   and `= -((2 : ℤ) • comm (genSig P A C) (genPhi P A C))`,
3. **Hilbert-Space Operator Cramér–Rao Gravitational Bound**:
   For any normalized state `ψ : NormalizedState H` and bounded operators `X_op, Y_op : H →L[ℂ] H`,
   `onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥ (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 + (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2`
   and `fubiniStudyMetric ψ X_op X_op * fubiniStudyMetric ψ Y_op Y_op ≥ (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2`. -/
theorem archetype_E8_centrifugal_dragging_and_fisher_cramer_rao
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ : NormalizedState H) (X_op Y_op : H →L[ℂ] H) (A C : B) :
    OperatorAlgebra.PeirceSpine.comm (genSig P A C)
        (OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C)
        (OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genJ P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) ∧
    -OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
      -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    -OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
      -((2 : ℤ) • OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) ∧
    onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
      (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
        (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 ∧
    fubiniStudyMetric ψ X_op X_op * fubiniStudyMetric ψ Y_op Y_op ≥
      (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 := by
  refine ⟨gemSecondOrderCentrifugal hP A C,
          gemSecondOrderCentrifugal_dual hP A C,
          by peirce_nf hP, by peirce_nf hP,
          cramerRao_metriplectic_full_bound ψ X_op Y_op,
          cramerRao_commutator_uncertainty_bound ψ X_op Y_op⟩

/-- **Master Operator Einstein–Cartan, Chiral Anomaly & Spin Frame Dragging Synthesis
(`einstein_cartan_chiral_anomaly_frame_dragging_master_synthesis`)**:
Coagulates the complete 8-stage Acyclic Causal Poset `𝔈₁ ≺ 𝔈₂ ≺ 𝔈₃ ≺ 𝔈₄ ≺ 𝔈₅ ≺ 𝔈₆ ≺ 𝔈₇ ≺ 𝔈₈`
into a single kernel-verified theorem. -/
theorem einstein_cartan_chiral_anomaly_frame_dragging_master_synthesis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ : NormalizedState H) (X_op Y_op : H →L[ℂ] H)
    (A C X₁ Y₁ X₂ Y₂ X₃ Y₃ : B) :
    -- (0) Acyclic 8-stage causal poset 𝔈₁ ≺ ⋯ ≺ 𝔈₈
    ((∀ st : EinsteinCartanAnomalyStage,
        ¬ Relation.TransGen EinsteinCartanAnomalyStage.causalEdge st st) ∧
     EinsteinCartanAnomalyStage.causalEdge
       .E1_ChiralCutAndMaurerCartanSolderForms
       .E2_OperatorFisherMetricAndSpinDipoleCurvature ∧
     EinsteinCartanAnomalyStage.causalEdge
       .E7_GeneralEinsteinCartanSplitAndBianchi
       .E8_CentrifugalDraggingAndFisherCramerRaoBound) ∧
    -- (1) Stage 𝔈₁ & 𝔈₂: Chiral duality, Fisher metric V = Φ² = -J², Spin-dipole Σ = JΦ
    (invS P * genPhi P A C = genJ P A C ∧
     invS P * genJ P A C = genPhi P A C ∧
     genPhi P A C * genPhi P A C = genV P A C ∧
     genJ P A C * genJ P A C = -genV P A C ∧
     genJ P A C * genPhi P A C = genSig P A C ∧
     peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C) ∧
    -- (2) Stage 𝔈₃ & 𝔈₄: Para-Kähler lock V = S_P Σ, Levi-Civita aporia & Chiral Einstein Anomaly
    (invS P * genSig P A C = genV P A C ∧
     (genSig P A C = 0 ↔ genV P A C = 0) ∧
     (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) = 0 →
       (2 : ℤ) • genSig P A C = 0 ∧ (2 : ℤ) • genV P A C = 0) ∧
     OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C) =
       -((2 : ℤ) • genSig P A C) ∧
     chiralEinsteinAnomaly P A C = -((2 : ℤ) • genV P A C)) ∧
    -- (3) Stage 𝔈₅: Spin frame dragging [Σ, Φ] = 2VJ & dressed torsion 𝒯_Σ(Φ) = (1 + 2V)J
    (OperatorAlgebra.PeirceSpine.anticomm (genSig P A C) (genPhi P A C) = 0 ∧
     OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C) =
       (2 : ℤ) • (genV P A C * genJ P A C) ∧
     OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genJ P A C) =
       (2 : ℤ) • (genV P A C * genPhi P A C) ∧
     dressedSpinTorsion P A C = (1 + (2 : ℤ) • genV P A C) * genJ P A C) ∧
    -- (4) Stage 𝔈₆: Soldered Cartan–Ehresmann split & Grade-3 Jordan associator
    (OperatorAlgebra.PeirceSpine.comm (solderedConnPhi P A C) (solderedConnJ P A C) =
       -((2 : ℤ) • genSig P A C) +
         (2 : ℤ) • (genV P A C * (genPhi P A C - genJ P A C)) ∧
     jordanAssociator (coneMinus P C) (conePlus P A) (conePlus P A) =
       (2 : ℤ) • (genV P A C * conePlus P A)) ∧
    -- (5) Stage 𝔈₇: General Einstein–Cartan split & Non-Abelian Bianchi identity
    (OperatorAlgebra.PeirceSpine.comm
         (cartanSplitConnection P X₁ Y₁) (cartanSplitConnection P X₂ Y₂) =
       riemannCartanCurvature P X₁ Y₁ X₂ Y₂ + elieCartanTorsion P X₁ Y₁ X₂ Y₂ ∧
     OperatorAlgebra.PeirceSpine.comm (invS P)
         (riemannCartanCurvature P X₁ Y₁ X₂ Y₂) = 0 ∧
     OperatorAlgebra.PeirceSpine.anticomm (invS P)
         (elieCartanTorsion P X₁ Y₁ X₂ Y₂) = 0 ∧
     OperatorAlgebra.PeirceSpine.comm (cartanSplitConnection P X₁ Y₁)
         (riemannCartanCurvature P X₂ Y₂ X₃ Y₃ + elieCartanTorsion P X₂ Y₂ X₃ Y₃) +
       OperatorAlgebra.PeirceSpine.comm (cartanSplitConnection P X₂ Y₂)
         (riemannCartanCurvature P X₃ Y₃ X₁ Y₁ + elieCartanTorsion P X₃ Y₃ X₁ Y₁) +
       OperatorAlgebra.PeirceSpine.comm (cartanSplitConnection P X₃ Y₃)
         (riemannCartanCurvature P X₁ Y₁ X₂ Y₂ + elieCartanTorsion P X₁ Y₁ X₂ Y₂) = 0) ∧
    -- (6) Stage 𝔈₈: 4th-order centrifugal frame dragging & Operator Cramér–Rao bound
    (OperatorAlgebra.PeirceSpine.comm (genSig P A C)
         (OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) =
       (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) ∧
     -OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
         (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
       -((2 : ℤ) • OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) ∧
     onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
       (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
         (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2) := by
  have hE1 := archetype_E1_chiral_cut_and_maurer_cartan_solder_forms hP A C
  have hE2 := archetype_E2_operator_fisher_metric_and_spin_dipole_curvature hP A C
  have hE3 := archetype_E3_para_kahler_lock_and_levi_civita_aporia hP A C
  have hE4 := archetype_E4_chiral_einstein_anomaly_cocycle hP A C
  have hE5 := archetype_E5_spin_frame_dragging_and_dressed_torsion hP A C
  have hE6 := archetype_E6_soldered_cartan_ehresmann_and_jordan_associator hP A C
  have hE7 := archetype_E7_general_einstein_cartan_split_and_bianchi hP X₁ Y₁ X₂ Y₂ X₃ Y₃
  have hE8 := archetype_E8_centrifugal_dragging_and_fisher_cramer_rao hP ψ X_op Y_op A C
  exact ⟨⟨EinsteinCartanAnomalyStage.causalEdge_acyclic,
          EinsteinCartanAnomalyStage.causalEdge_chain_and_diamond.1,
          EinsteinCartanAnomalyStage.causalEdge_chain_and_diamond.2.2.2.2.2.2.2⟩,
         ⟨hE1.2.2.2.1, hE1.2.2.2.2.2.1, hE2.1, hE2.2.1, hE2.2.2.1, hE2.2.2.2.2.2.2.1⟩,
         ⟨hE3.1, hE3.2.2.2.2.1, hE3.2.2.2.2.2.2, hE4.1, hE4.2.1⟩,
         ⟨hE5.1, hE5.2.2.1, hE5.2.2.2.1, hE5.2.2.2.2.2.2.2⟩,
         ⟨hE6.1, hE6.2.2.2.2.1⟩,
         hE7,
         ⟨hE8.1, hE8.2.2.2.1, hE8.2.2.2.2.1⟩⟩

end StageE8

end InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset

end
