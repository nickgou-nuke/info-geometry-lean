/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.GolayLeechMOGSheetPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Operator Surprisal Idempotent Normal Form, Relative Volume Resolvent Force, Master Clocking Identity, 5-Graded Kantor Sandwich & BKM Divided-Difference Poset

**Epistemic Status**: Algebraic identities and finite resolvent factorizations are kernel-proved under their stated hypotheses. This file does not construct operator logarithms, Fréchet derivatives, modular automorphism groups, or the improper BKM resolvent integral.
**Dependency Mode**: Native Non-Commutative Ring, Star-Ring, Algebra & Hilbert-Space Theory
**Gate-0 Screening**: Screened via `tools/infra/opengauss_screener.py`

This module formalizes in native Mathlib (Lean 4) the 8-stage Acyclic Causal Poset
(`𝔖₁ ≺ 𝔖₂ ≺ 𝔖₃ ≺ 𝔖₄ ≺ 𝔖₅ ≺ 𝔖₆ ≺ 𝔖₇ ≺ 𝔖₈`) governing the **Operator Surprisal
Idempotent Normal Form**, **Relative Volume Resolvent Force**, **Algebraic Modular-Commutator
Action**, **Master Clocking Identity**, **5-Graded Supercolor Kantor Sandwich**, and
**BKM Divided-Difference Factorization with a separately proved Metriplectic Cramér–Rao bound** over an arbitrary non-commutative
ring `[Ring B]` (and `[Algebra ℝ B]`):

```
                  𝔖₁: Supercolor Vacuum Deformation & Frozen Clock
                      ρ_sheet = p P + q(1-P),  (P + Φ)² - (P + Φ) = V
                      Zorn Supercolor Deficit: (e_L + Ψ)² - (e_L + Ψ) = V_Zorn + B_anom
                                 /                            \
                                /                              \
                               ▼                                ▼
         𝔖₂: Sheet Surprisal Idempotent Normal Form     𝔖₃: Relative Volume Resolvent Force
             2 K_sheet = (s_p + s_q)I - Δs S_P              (1 + βV) W_β = 1,  [W_β, Φ] = 0
             K_sheet(p,q) = s̄ I - ½ Δs S_P                  F_β = 2β W_β Φ, W_β⁻¹ = 1 + βV
                                \                              /
                                 \                            /
                                  ▼                          ▼
                  𝔖₄: Algebraic Modular-Commutator Action
                      [K_sheet, Φ] = -Δs J,  [K_sheet, J] = -Δs Φ
                      [Σ, Φ] = 2VJ  (Spin-Dipole Precession)
                                       │
                                       ▼
                  𝔖₅: Master Clocking Identity & Thermal Harmonic Oscillator
                      -[Φ, [Φ, J]] = -2[Σ, Φ] = -4VJ
                      [K_sheet, [K_sheet, Φ]] = (Δs)² Φ
                                       │
                                       ▼
                  𝔖₆: 5-Graded Supercolor Kantor Sandwich & 4th-Order Harmonics
                      K₀²(X) - {K₊₂, K₋₂}(X) = Σ X Σ,  K₀²(X) + {K₊₂, K₋₂}(X) = V X V
                      [Σ, [Σ, Φ]] = 4V²Φ
                                       │
                                       ▼
                  𝔖₇: BKM Resolvent Factorization & Divided Difference (no integral)
                      Φ(ρ + sI)⁻¹Φ(ρ + sI)⁻¹ = ((p+s)(q+s))⁻¹ V
                      g_BKM(Φ, Φ) = (-log(q/p) / (p - q)) τ(V)
                                       │
                                       ▼
                  𝔖₈: Metriplectic Cramér–Rao Closure & Master Synthesis
                      G_ψ(X,X) G_ψ(Y,Y) ≥ G_ψ(X,Y)² + ¼ Ω_ψ(X,Y)²
```

## i. Overview

Formalizes the 8-stage `ModularSurprisalClockingStage` poset (`𝔖₁ ≺ ⋯ ≺ 𝔖₈`) governing the
operator surprisal idempotent normal form, relative volume resolvent force, master clocking
identity, 5-graded Kantor sandwich, and BKM divided-difference factorization.

## ii. Key results

- `ModularSurprisalClockingStage.causalEdge_acyclic`
- `ModularSurprisalClockingStage.causalEdge_chain_and_diamond`
- `modular_surprisal_volume_clocking_bkm_master_synthesis`

## iii. Table of contents

- Section 0: The 8-Stage Acyclic Causal Poset (`𝔖₁ ≺ ⋯ ≺ 𝔖₈`)
- Sections 1–8: Stages `𝔖₁` through `𝔖₈`

## iv. References

- D. Petz, *Monotone metrics on matrix spaces* (1996).
- N. N. Bogoliubov, *Lectures on Quantum Statistics* (1967).

#### BUCKET 1: CLOSED FINITE THEOREMS
- `ModularSurprisalClockingStage.causalEdge_acyclic`, `ModularSurprisalClockingStage.causalEdge_chain_and_diamond`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- Stage `𝔖₁`–`𝔖₈` theorems over `[Ring B]` / `[Algebra ℝ B]` and Hilbert-space states.

#### BUCKET 3: OPEN CLOSURE DEBT
- Improper operator-resolvent integral representation of the BKM metric beyond algebraic divided differences.
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset (Vec3 ZornMatrix)
open InfoGeometry.Canonical.ChiralCondensateGMORBanksCasherNJLPoset
open InfoGeometry.Canonical.MaurerCartanSpectralAnnihilatorDefectPoset
open InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
open InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty
open InfoGeometry.QuantumGeometry.Projective
open scoped Matrix InnerProductSpace

/-! ===========================================================================
    Section 0: The 8-Stage Acyclic Causal Poset (`𝔖₁ ≺ 𝔖₂ ≺ 𝔖₃ ≺ 𝔖₄ ≺ 𝔖₅ ≺ 𝔖₆ ≺ 𝔖₇ ≺ 𝔖₈`)
    =========================================================================== -/

/-- The 8-stage epistemic poset `𝔖₁ ≺ 𝔖₂ ≺ 𝔖₃ ≺ 𝔖₄ ≺ 𝔖₅ ≺ 𝔖₆ ≺ 𝔖₇ ≺ 𝔖₈` of the
Operator Surprisal Idempotent Normal Form, Relative Volume Resolvent Gradient, Master Clocking
Identity, 5-Graded Kantor Sandwich, and BKM Metriplectic Closure spine. -/
inductive ModularSurprisalClockingStage : Type
  | S1_SupercolorVacuumDeformationAndFrozenClock
  | S2_SheetSurprisalIdempotentNormalForm
  | S3_RelativeVolumeAndResolventSurprisalForce
  | S4_AlgebraicModularCommutatorAction
  | S5_MasterClockingIdentityAndThermalHarmonicOscillator
  | S6_FiveGradedKantorSandwichAndFourthOrderHarmonics
  | S7_BKMResolventFactorizationAndDividedDifference
  | S8_MetriplecticCramerRaoClosureAndMasterSynthesis
  deriving DecidableEq, Repr

namespace ModularSurprisalClockingStage

/-- Topological rank embedding into `ℕ`. -/
def rank : ModularSurprisalClockingStage → ℕ
  | .S1_SupercolorVacuumDeformationAndFrozenClock => 0
  | .S2_SheetSurprisalIdempotentNormalForm => 1
  | .S3_RelativeVolumeAndResolventSurprisalForce => 2
  | .S4_AlgebraicModularCommutatorAction => 3
  | .S5_MasterClockingIdentityAndThermalHarmonicOscillator => 4
  | .S6_FiveGradedKantorSandwichAndFourthOrderHarmonics => 5
  | .S7_BKMResolventFactorizationAndDividedDifference => 6
  | .S8_MetriplecticCramerRaoClosureAndMasterSynthesis => 7

/-- `rank` is injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrderModularSurprisalClockingStage :
    LinearOrder ModularSurprisalClockingStage :=
  LinearOrder.lift' rank rank_injective

/-- Direct causal dependency relation `s₁ ≺ s₂`, encoding both the sequential chain and the
diamond fork (`𝔖₁ ≺ 𝔖₂`, `𝔖₁ ≺ 𝔖₃`) and join (`𝔖₂ ≺ 𝔖₄`, `𝔖₃ ≺ 𝔖₄`). -/
def causalEdge : ModularSurprisalClockingStage → ModularSurprisalClockingStage → Prop
  | a, b =>
      rank b = rank a + 1 ∨
      (a = .S1_SupercolorVacuumDeformationAndFrozenClock ∧
        b = .S3_RelativeVolumeAndResolventSurprisalForce) ∨
      (a = .S2_SheetSurprisalIdempotentNormalForm ∧
        b = .S4_AlgebraicModularCommutatorAction)

/-- Every direct causal edge strictly increases `rank`. -/
theorem causalEdge_strict_rank {a b : ModularSurprisalClockingStage}
    (h : causalEdge a b) : rank a < rank b := by
  rcases h with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · omega
  · decide
  · decide

/-- Every non-empty directed path in `Relation.TransGen causalEdge` strictly increases `rank`. -/
theorem transGen_causalEdge_strict_rank {a b : ModularSurprisalClockingStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_strict_rank hbc)

/-- **Strict Acyclicity (`causalEdge_acyclic`)**:
No stage in `ModularSurprisalClockingStage` has a non-empty directed cycle back to itself. -/
theorem causalEdge_acyclic (a : ModularSurprisalClockingStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank h)

/-- Verification of the 7 sequential cover edges and the diamond fork/join edges. -/
theorem causalEdge_chain_and_diamond :
    causalEdge .S1_SupercolorVacuumDeformationAndFrozenClock
      .S2_SheetSurprisalIdempotentNormalForm ∧
    causalEdge .S1_SupercolorVacuumDeformationAndFrozenClock
      .S3_RelativeVolumeAndResolventSurprisalForce ∧
    causalEdge .S2_SheetSurprisalIdempotentNormalForm
      .S4_AlgebraicModularCommutatorAction ∧
    causalEdge .S3_RelativeVolumeAndResolventSurprisalForce
      .S4_AlgebraicModularCommutatorAction ∧
    causalEdge .S4_AlgebraicModularCommutatorAction
      .S5_MasterClockingIdentityAndThermalHarmonicOscillator ∧
    causalEdge .S5_MasterClockingIdentityAndThermalHarmonicOscillator
      .S6_FiveGradedKantorSandwichAndFourthOrderHarmonics ∧
    causalEdge .S6_FiveGradedKantorSandwichAndFourthOrderHarmonics
      .S7_BKMResolventFactorizationAndDividedDifference ∧
    causalEdge .S7_BKMResolventFactorizationAndDividedDifference
      .S8_MetriplecticCramerRaoClosureAndMasterSynthesis := by
  refine ⟨Or.inl (by decide), Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr ⟨rfl, rfl⟩),
          Or.inl (by decide), Or.inl (by decide), Or.inl (by decide),
          Or.inl (by decide), Or.inl (by decide)⟩

end ModularSurprisalClockingStage

/-! ===========================================================================
    Section 1: Stage 𝔖₁ — Supercolor Vacuum Deformation & Frozen Isotropic Clock
    =========================================================================== -/

section StageS1

variable {B : Type*} [Ring B]

/-- The two-sheet block-diagonal thermal state `ρ_sheet(P, p, q) := p P + q (1 - P)`. -/
def sheetThermalState (P p q : B) : B :=
  p * P + q * (1 - P)

variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔖₁` (`archetype_S1_supercolor_vacuum_deformation_and_frozen_clock`)**:
1. **Isotropic Sheet Collapse**:
   When the two sheet weights coincide (`q = p`), `sheetThermalState P p p = p`,
2. **Frozen Isotropic Modular Clock**:
   For any central isotropic weight `s₀ : B` (`∀ X : B, s₀ * X = X * s₀`),
   `comm (sheetThermalState P s₀ s₀) X = 0` for every operator `X : B`,
3. **Grassmannian Idempotent Strain (`(P + Φ)² - (P + Φ) = V`)**:
   `(P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C` and
   `((1 - P) + genPhi P A C) * ((1 - P) + genPhi P A C) - ((1 - P) + genPhi P A C) = genV P A C`,
4. **Zorn Split-Octonion Supercolor Vacuum Strain**:
   For any color/anticolor vectors `u, v : Vec3 B` in `ZornMatrix B`,
   `ZornMatrix.zornV u v = ZornMatrix.bilinearCondensate u v` and
   `ZornMatrix.idempotentDeficit (ZornMatrix.eL + ZornMatrix.psiOffDiag u v) = ZornMatrix.bilinearCondensate u v + ⟨0, -Vec3.cross v v, Vec3.cross u u, 0⟩`. -/
theorem archetype_S1_supercolor_vacuum_deformation_and_frozen_clock
    (p s₀ A C : B) (hs₀ : ∀ X : B, s₀ * X = X * s₀) (u v : Vec3 B) :
    sheetThermalState P p p = p ∧
    (∀ X : B, OperatorAlgebra.PeirceSpine.comm (sheetThermalState P s₀ s₀) X = 0) ∧
    (P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C ∧
    ((1 - P) + genPhi P A C) * ((1 - P) + genPhi P A C) -
      ((1 - P) + genPhi P A C) = genV P A C ∧
    ZornMatrix.zornV u v = ZornMatrix.bilinearCondensate u v ∧
    ZornMatrix.idempotentDeficit (ZornMatrix.eL + ZornMatrix.psiOffDiag u v) =
      ZornMatrix.bilinearCondensate u v + ⟨0, -Vec3.cross v v, Vec3.cross u u, 0⟩ := by
  refine ⟨?_, ?_, by peirce_nf hP, by peirce_nf hP, ?_, ?_⟩
  · unfold sheetThermalState
    noncomm_ring
  · intro X
    have hIso : sheetThermalState P s₀ s₀ = s₀ := by
      unfold sheetThermalState
      noncomm_ring
    rw [hIso]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [hs₀ X, sub_self]
  · ext <;>
      simp [ZornMatrix.zornV, ZornMatrix.psiPlus, ZornMatrix.psiMinus,
            ZornMatrix.bilinearCondensate]
  · ext <;>
      simp [ZornMatrix.idempotentDeficit, ZornMatrix.eL, ZornMatrix.psiOffDiag,
            ZornMatrix.bilinearCondensate]

end StageS1

/-! ===========================================================================
    Section 2: Stage 𝔖₂ — Operator Surprisal Idempotent Normal Form
    =========================================================================== -/

section StageS2

variable {B : Type*} [Ring B]

/-- The ring-valued sheet surprisal operator `K_sheet(P, s_p, s_q) := s_p P + s_q (1 - P)`. -/
def sheetSurprisalOp (P s_p s_q : B) : B :=
  s_p * P + s_q * (1 - P)

/-- The real-logarithm sheet surprisal operator
`K_sheet(P, p, q) := (-log p) • P + (-log q) • (1 - P)` over an `ℝ`-algebra `B`. -/
noncomputable def realSheetSurprisalOp [Algebra ℝ B] (P : B) (p q : ℝ) : B :=
  (-Real.log p) • P + (-Real.log q) • (1 - P)

variable {P : B} (hP : P * P = P)
include hP

/-- Orthogonal idempotent multiplication rule:
`sheetThermalState P p₁ q₁ * sheetThermalState P p₂ q₂ = sheetThermalState P (p₁ * p₂) (q₁ * q₂)`
whenever `p₂, q₂` commute with `P`. -/
theorem sheetThermalState_mul {p₁ q₁ p₂ q₂ : B}
    (hp₂ : p₂ * P = P * p₂) (hq₂ : q₂ * P = P * q₂) :
    sheetThermalState P p₁ q₁ * sheetThermalState P p₂ q₂ =
      sheetThermalState P (p₁ * p₂) (q₁ * q₂) := by
  unfold sheetThermalState
  have hP2 : P * (1 - P) = 0 := by noncomm_ring [hP]
  have h1P2 : (1 - P) * P = 0 := by noncomm_ring [hP]
  have h1P_idem : (1 - P) * (1 - P) = 1 - P := by noncomm_ring [hP]
  calc
    (p₁ * P + q₁ * (1 - P)) * (p₂ * P + q₂ * (1 - P))
      = p₁ * (P * p₂) * P + p₁ * (P * q₂) * (1 - P) +
        q₁ * ((1 - P) * p₂) * P + q₁ * ((1 - P) * q₂) * (1 - P) := by noncomm_ring
    _ = p₁ * (p₂ * P) * P + p₁ * (q₂ * P) * (1 - P) +
        q₁ * (p₂ * (1 - P)) * P + q₁ * (q₂ * (1 - P)) * (1 - P) := by
          rw [← hp₂, ← hq₂]
          have hp₂' : (1 - P) * p₂ = p₂ * (1 - P) := by
            rw [sub_mul, one_mul, mul_sub, mul_one, hp₂]
          have hq₂' : (1 - P) * q₂ = q₂ * (1 - P) := by
            rw [sub_mul, one_mul, mul_sub, mul_one, hq₂]
          rw [hp₂', hq₂']
    _ = p₁ * p₂ * (P * P) + p₁ * q₂ * (P * (1 - P)) +
        q₁ * p₂ * ((1 - P) * P) + q₁ * q₂ * ((1 - P) * (1 - P)) := by noncomm_ring
    _ = p₁ * p₂ * P + q₁ * q₂ * (1 - P) := by
          rw [hP, hP2, h1P2, h1P_idem]
          noncomm_ring

/-- Orthogonal idempotent power law `(p P + q (1 - P))^(n + 1) = p^(n + 1) P + q^(n + 1) (1 - P)`. -/
theorem sheetThermalState_pow_succ {p q : B}
    (hp : p * P = P * p) (hq : q * P = P * q) (n : ℕ) :
    (sheetThermalState P p q) ^ (n + 1) =
      sheetThermalState P (p ^ (n + 1)) (q ^ (n + 1)) := by
  induction n with
  | zero => simp [sheetThermalState]
  | succ k ih =>
    rw [pow_succ (sheetThermalState P p q) (k + 1), ih,
        sheetThermalState_mul hP hp hq, ← pow_succ, ← pow_succ]

/-- **Archetype `𝔖₂` (`archetype_S2_sheet_surprisal_idempotent_normal_form`)**:
1. **Orthogonal Idempotent Power Law**:
   `(sheetThermalState P p q) ^ (n + 1) = sheetThermalState P (p ^ (n + 1)) (q ^ (n + 1))`,
2. **Division-Free Chiral Normal Form (`2 K_sheet = (s_p + s_q)I - Δs S_P` with `Δs = s_q - s_p`)**:
   `(2 : ℤ) • sheetSurprisalOp P s_p s_q = (s_p + s_q) - (s_q - s_p) * invS P`
   and `(2 : ℤ) • sheetSurprisalOp P s_p s_q = (s_p + s_q) + (s_p - s_q) * invS P`,
3. **Exact Real-Logarithm Surprisal Normal Form (`K_sheet(p,q) = s̄ I - ½ Δs S_P`)**:
   Over any `[Algebra ℝ B]`,
   `realSheetSurprisalOp P p_r q_r = ((-(Real.log p_r + Real.log q_r) / 2) : ℝ) • (1 : B) - (((-Real.log q_r - -Real.log p_r) / 2) : ℝ) • invS P`,
4. **Logarithm Ratio & Mean Identities for Positive Sheet Weights (`0 < p_r`, `0 < q_r`)**:
   `-Real.log (q_r / p_r) = Real.log (p_r / q_r) ∧ Real.log (p_r / q_r) = (-Real.log q_r) - (-Real.log p_r) ∧ -(Real.log p_r + Real.log q_r) / 2 = -Real.log (p_r * q_r) / 2`. -/
theorem archetype_S2_sheet_surprisal_idempotent_normal_form
    [Algebra ℝ B] {p q : B} (hp : p * P = P * p) (hq : q * P = P * q)
    (s_p s_q : B) (n : ℕ) {p_r q_r : ℝ} (hp_r : 0 < p_r) (hq_r : 0 < q_r) :
    (sheetThermalState P p q) ^ (n + 1) =
      sheetThermalState P (p ^ (n + 1)) (q ^ (n + 1)) ∧
    (2 : ℤ) • sheetSurprisalOp P s_p s_q = (s_p + s_q) - (s_q - s_p) * invS P ∧
    (2 : ℤ) • sheetSurprisalOp P s_p s_q = (s_p + s_q) + (s_p - s_q) * invS P ∧
    realSheetSurprisalOp P p_r q_r =
      ((-(Real.log p_r + Real.log q_r) / 2) : ℝ) • (1 : B) -
        (((-Real.log q_r - -Real.log p_r) / 2) : ℝ) • invS P ∧
    (-Real.log (q_r / p_r) = Real.log (p_r / q_r) ∧
     Real.log (p_r / q_r) = (-Real.log q_r) - (-Real.log p_r) ∧
     -(Real.log p_r + Real.log q_r) / 2 = -Real.log (p_r * q_r) / 2) := by
  refine ⟨sheetThermalState_pow_succ hP hp hq n, ?_, ?_, ?_, ?_⟩
  · unfold sheetSurprisalOp invS
    rw [two_zsmul]
    noncomm_ring
  · unfold sheetSurprisalOp invS
    rw [two_zsmul]
    noncomm_ring
  · unfold realSheetSurprisalOp invS
    module
  · refine ⟨?_, ?_, ?_⟩
    · rw [Real.log_div hq_r.ne' hp_r.ne', Real.log_div hp_r.ne' hq_r.ne']
      ring
    · rw [Real.log_div hp_r.ne' hq_r.ne']
      ring
    · rw [Real.log_mul hp_r.ne' hq_r.ne']

end StageS2

/-! ===========================================================================
Section 3: Stage 𝔖₃ — Relative Volume Resolvent Force
    =========================================================================== -/

section StageS3

variable {B : Type*} [Ring B]

/-- The deformed relative-volume metric denominator `D_vol(P, A, C, β) := 1 + β V`. -/
def volumeMetricDenom (P A C β : B) : B :=
  1 + β * genV P A C

/-- Algebraically specified relative-volume resolvent force
`F_β := 2 β W_β Φ`, with `W_β` supplied as a two-sided inverse of `1 + β V`.
This definition does not assert that `F_β` is a derivative of an operator logarithm. -/
def volumeResolventForce (P A C β W_β : B) : B :=
  (2 : ℤ) • (β * W_β * genPhi P A C)

/-- Universal two-sided inverse commutation lemma: if `D * W = 1` and `W * D = 1`, then `W`
commutes with every element `X` that commutes with `D`. -/
theorem two_sided_inv_comm_of_comm {D W X : B}
    (hW_right : D * W = 1) (hW_left : W * D = 1) (hDX : D * X = X * D) :
    W * X = X * W := by
  calc
    W * X = W * X * (D * W) := by rw [hW_right, mul_one]
    _ = W * (X * D) * W := by noncomm_ring
    _ = W * (D * X) * W := by rw [← hDX]
    _ = (W * D) * X * W := by noncomm_ring
    _ = X * W := by rw [hW_left, one_mul]

variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔖₃` (`archetype_S3_relative_volume_resolvent_force`)**:
For any central inverse-temperature parameter `β : B` (`∀ X : B, β * X = X * β`) and two-sided
resolvent inverse `W_β` of `volumeMetricDenom P A C β = 1 + β V`:
1. **Directional Quadratic Variation (`d(Φ²) = 2 Φ δΦ`)**:
   For any variation `δΦ : B` commuting with `genPhi P A C`,
   `(genPhi P A C + δΦ) * (genPhi P A C + δΦ) - genPhi P A C * genPhi P A C - δΦ * δΦ = (2 : ℤ) • (genPhi P A C * δΦ)`,
2. **Automatic Resolvent Commutation (`[W_β, P] = [W_β, V] = [W_β, Φ] = 0`)**:
   `W_β * P = P * W_β`, `W_β * genV P A C = genV P A C * W_β`, and
   `W_β * genPhi P A C = genPhi P A C * W_β`,
3. **Strict Odd Chiral Parity of the Resolvent Force**:
   `anticomm (invS P) (volumeResolventForce P A C β W_β) = 0`,
4. **Exact Linearized Resolvent Recovery**:
   `volumeMetricDenom P A C β * volumeResolventForce P A C β W_β = (2 : ℤ) • (β * genPhi P A C)`. -/
theorem archetype_S3_relative_volume_resolvent_force
    (A C β W_β δΦ : B)
    (hβ : ∀ X : B, β * X = X * β)
    (hW_right : volumeMetricDenom P A C β * W_β = 1)
    (hW_left : W_β * volumeMetricDenom P A C β = 1)
    (hδ : genPhi P A C * δΦ = δΦ * genPhi P A C) :
    (genPhi P A C + δΦ) * (genPhi P A C + δΦ) -
      genPhi P A C * genPhi P A C - δΦ * δΦ =
        (2 : ℤ) • (genPhi P A C * δΦ) ∧
    W_β * P = P * W_β ∧
    W_β * genV P A C = genV P A C * W_β ∧
    W_β * genPhi P A C = genPhi P A C * W_β ∧
    OperatorAlgebra.PeirceSpine.anticomm (invS P)
      (volumeResolventForce P A C β W_β) = 0 ∧
    volumeMetricDenom P A C β * volumeResolventForce P A C β W_β =
      (2 : ℤ) • (β * genPhi P A C) := by
  have hVP : genV P A C * P = P * genV P A C := by peirce_nf hP
  have hVPhi : genV P A C * genPhi P A C = genPhi P A C * genV P A C := by peirce_nf hP
  have hDP : volumeMetricDenom P A C β * P = P * volumeMetricDenom P A C β := by
    unfold volumeMetricDenom
    calc
      (1 + β * genV P A C) * P = P + β * (genV P A C * P) := by noncomm_ring
      _ = P + (β * P) * genV P A C := by rw [hVP]; noncomm_ring
      _ = P * (1 + β * genV P A C) := by rw [hβ P]; noncomm_ring
  have hDV : volumeMetricDenom P A C β * genV P A C = genV P A C * volumeMetricDenom P A C β := by
    unfold volumeMetricDenom
    calc
      (1 + β * genV P A C) * genV P A C = genV P A C + (β * genV P A C) * genV P A C := by
        noncomm_ring
      _ = genV P A C + (genV P A C * β) * genV P A C := by rw [hβ (genV P A C)]
      _ = genV P A C * (1 + β * genV P A C) := by noncomm_ring
  have hDPhi : volumeMetricDenom P A C β * genPhi P A C =
      genPhi P A C * volumeMetricDenom P A C β := by
    unfold volumeMetricDenom
    calc
      (1 + β * genV P A C) * genPhi P A C = genPhi P A C + β * (genV P A C * genPhi P A C) := by
        noncomm_ring
      _ = genPhi P A C + (β * genPhi P A C) * genV P A C := by rw [hVPhi]; noncomm_ring
      _ = genPhi P A C * (1 + β * genV P A C) := by rw [hβ (genPhi P A C)]; noncomm_ring
  have hWP : W_β * P = P * W_β := two_sided_inv_comm_of_comm hW_right hW_left hDP
  have hWV : W_β * genV P A C = genV P A C * W_β := two_sided_inv_comm_of_comm hW_right hW_left hDV
  have hWPhi : W_β * genPhi P A C = genPhi P A C * W_β :=
    two_sided_inv_comm_of_comm hW_right hW_left hDPhi
  refine ⟨?_, hWP, hWV, hWPhi, ?_, ?_⟩
  · rw [two_zsmul]
    calc
      (genPhi P A C + δΦ) * (genPhi P A C + δΦ) -
          genPhi P A C * genPhi P A C - δΦ * δΦ
        = genPhi P A C * δΦ + δΦ * genPhi P A C := by noncomm_ring
      _ = genPhi P A C * δΦ + genPhi P A C * δΦ := by rw [← hδ]
  · unfold volumeResolventForce
    dsimp [OperatorAlgebra.PeirceSpine.anticomm]
    rw [two_zsmul]
    have hSPhi : invS P * genPhi P A C + genPhi P A C * invS P = 0 := by peirce_nf hP
    have hPbw : P * (β * W_β) = (β * W_β) * P := by
      calc
        P * (β * W_β) = (P * β) * W_β := by noncomm_ring
        _ = β * (P * W_β) := by rw [← hβ P]; noncomm_ring
        _ = (β * W_β) * P := by rw [← hWP]; noncomm_ring
    have hSW : invS P * (β * W_β) = (β * W_β) * invS P := by
      unfold invS
      rw [sub_mul, sub_mul, one_mul, mul_sub, mul_sub, mul_one, hPbw]
    calc
      invS P * (β * W_β * genPhi P A C + β * W_β * genPhi P A C) +
          (β * W_β * genPhi P A C + β * W_β * genPhi P A C) * invS P
        = (invS P * (β * W_β)) * genPhi P A C + (invS P * (β * W_β)) * genPhi P A C +
          (β * W_β) * (genPhi P A C * invS P) + (β * W_β) * (genPhi P A C * invS P) := by
            noncomm_ring
      _ = (β * W_β) * (invS P * genPhi P A C + genPhi P A C * invS P) +
          (β * W_β) * (invS P * genPhi P A C + genPhi P A C * invS P) := by
            rw [hSW]; noncomm_ring
      _ = 0 := by rw [hSPhi, mul_zero, add_zero]
  · unfold volumeResolventForce
    rw [two_zsmul, two_zsmul]
    calc
      volumeMetricDenom P A C β * (β * W_β * genPhi P A C + β * W_β * genPhi P A C)
        = (volumeMetricDenom P A C β * β) * W_β * genPhi P A C +
          (volumeMetricDenom P A C β * β) * W_β * genPhi P A C := by noncomm_ring
      _ = β * (volumeMetricDenom P A C β * W_β) * genPhi P A C +
          β * (volumeMetricDenom P A C β * W_β) * genPhi P A C := by
            rw [← hβ (volumeMetricDenom P A C β)]; noncomm_ring
      _ = β * genPhi P A C + β * genPhi P A C := by
            rw [hW_right, mul_one]

end StageS3

/-! ===========================================================================
    Section 4: Stage 𝔖₄ — Algebraic Modular-Commutator Action
    =========================================================================== -/

section StageS4

variable {B : Type*} [Ring B]

/-- Universal commutator reduction for sheet operators: if `s_p, s_q` commute with `X`, then
`[s_p P + s_q (1 - P), X] = (s_p - s_q) [P, X]`. -/
theorem comm_sheetSurprisalOp_eq (P s_p s_q X : B)
    (hsp : s_p * X = X * s_p) (hsq : s_q * X = X * s_q) :
    OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) X =
      (s_p - s_q) * OperatorAlgebra.PeirceSpine.comm P X := by
  unfold sheetSurprisalOp
  dsimp [OperatorAlgebra.PeirceSpine.comm]
  calc
    (s_p * P + s_q * (1 - P)) * X - X * (s_p * P + s_q * (1 - P))
      = s_p * (P * X) + (s_q * X) - s_q * (P * X) -
        (X * s_p) * P - (X * s_q) + (X * s_q) * P := by noncomm_ring
    _ = (s_p - s_q) * (P * X - X * P) := by
          rw [← hsp, ← hsq]; noncomm_ring

variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔖₄` (`archetype_S4_algebraic_modular_commutator_action`)**:
For any central sheet surprisals `s_p, s_q : B` (`∀ X : B, s_p * X = X * s_p` and
`∀ X : B, s_q * X = X * s_q`) with surprisal gap `Δs = s_q - s_p`:
1. **Commutator Action on the Solder Form (`[K_sheet, Φ] = (s_p - s_q) J = -Δs J`)**:
   `comm (sheetSurprisalOp P s_p s_q) (genPhi P A C) = (s_p - s_q) * genJ P A C` and
   `= -((s_q - s_p) * genJ P A C)`,
2. **Commutator Action on the Chiral Dual (`[K_sheet, J] = (s_p - s_q) Φ = -Δs Φ`)**:
   `comm (sheetSurprisalOp P s_p s_q) (genJ P A C) = (s_p - s_q) * genPhi P A C` and
   `= -((s_q - s_p) * genPhi P A C)`,
3. **Real-Logarithm-Weighted Algebraic Commutator Action**:
   Over any `[Algebra ℝ B]` and `p_r, q_r : ℝ`,
   `comm (realSheetSurprisalOp P p_r q_r) (genPhi P A C) = ((-Real.log p_r - -Real.log q_r) : ℝ) • genJ P A C`
   and `comm (realSheetSurprisalOp P p_r q_r) (genJ P A C) = ((-Real.log p_r - -Real.log q_r) : ℝ) • genPhi P A C`,
4. **Spin-Dipole Precession (`[Σ, Φ] = 2 V J`)**:
   `comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)`. -/
theorem archetype_S4_algebraic_modular_commutator_action
    [Algebra ℝ B] (s_p s_q A C : B)
    (hsp : ∀ X : B, s_p * X = X * s_p) (hsq : ∀ X : B, s_q * X = X * s_q)
    (p_r q_r : ℝ) :
    OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genPhi P A C) =
      (s_p - s_q) * genJ P A C ∧
    OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genPhi P A C) =
      -((s_q - s_p) * genJ P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genJ P A C) =
      (s_p - s_q) * genPhi P A C ∧
    OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genJ P A C) =
      -((s_q - s_p) * genPhi P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (realSheetSurprisalOp P p_r q_r) (genPhi P A C) =
      ((-Real.log p_r - -Real.log q_r) : ℝ) • genJ P A C ∧
    OperatorAlgebra.PeirceSpine.comm (realSheetSurprisalOp P p_r q_r) (genJ P A C) =
      ((-Real.log p_r - -Real.log q_r) : ℝ) • genPhi P A C ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genJ P A C) := by
  have hPPhi : OperatorAlgebra.PeirceSpine.comm P (genPhi P A C) = genJ P A C := by
    peirce_nf hP
  have hPJ : OperatorAlgebra.PeirceSpine.comm P (genJ P A C) = genPhi P A C := by
    peirce_nf hP
  have h1 : OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genPhi P A C) =
      (s_p - s_q) * genJ P A C := by
    rw [comm_sheetSurprisalOp_eq P s_p s_q (genPhi P A C) (hsp _) (hsq _), hPPhi]
  have h2 : OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genJ P A C) =
      (s_p - s_q) * genPhi P A C := by
    rw [comm_sheetSurprisalOp_eq P s_p s_q (genJ P A C) (hsp _) (hsq _), hPJ]
  have hRealEq : realSheetSurprisalOp P p_r q_r =
      sheetSurprisalOp P (algebraMap ℝ B (-Real.log p_r)) (algebraMap ℝ B (-Real.log q_r)) := by
    unfold realSheetSurprisalOp sheetSurprisalOp
    rw [Algebra.smul_def, Algebra.smul_def]
  refine ⟨h1, ?_, h2, ?_, ?_, ?_, by peirce_nf hP⟩
  · rw [h1]; noncomm_ring
  · rw [h2]; noncomm_ring
  · rw [hRealEq, comm_sheetSurprisalOp_eq P _ _ (genPhi P A C)
          (Algebra.commutes _ _) (Algebra.commutes _ _), hPPhi,
        Algebra.smul_def, map_sub]
  · rw [hRealEq, comm_sheetSurprisalOp_eq P _ _ (genJ P A C)
          (Algebra.commutes _ _) (Algebra.commutes _ _), hPJ,
        Algebra.smul_def, map_sub]

end StageS4

/-! ===========================================================================
    Section 5: Stage 𝔖₅ — Master Clocking Identity & Thermal Harmonic Oscillator
    =========================================================================== -/

section StageS5

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔖₅` (`archetype_S5_master_clocking_identity_and_thermal_harmonic_oscillator`)**:
1. **Master Clocking Identity (Primary Orientation)**:
   `-comm (genPhi P A C) (comm (genPhi P A C) (genJ P A C)) = -((2 : ℤ) • comm (genSig P A C) (genPhi P A C))`
   and `= -((4 : ℤ) • (genV P A C * genJ P A C))`,
2. **Master Clocking Identity (Dual Orientation)**:
   `-comm (genJ P A C) (comm (genJ P A C) (genPhi P A C)) = (2 : ℤ) • comm (genSig P A C) (genJ P A C)`
   and `= (4 : ℤ) • (genV P A C * genPhi P A C)`,
3. **Thermal Harmonic Oscillator of the Modular Clock (`[K_sheet, [K_sheet, Φ]] = (Δs)² Φ`)**:
   For any central sheet surprisals `s_p, s_q : B` (`∀ X : B, s_p * X = X * s_p` and
   `∀ X : B, s_q * X = X * s_q`),
   `comm (sheetSurprisalOp P s_p s_q) (comm (sheetSurprisalOp P s_p s_q) (genPhi P A C)) = (s_q - s_p) * (s_q - s_p) * genPhi P A C`
   and `comm (sheetSurprisalOp P s_p s_q) (comm (sheetSurprisalOp P s_p s_q) (genJ P A C)) = (s_q - s_p) * (s_q - s_p) * genJ P A C`. -/
theorem archetype_S5_master_clocking_identity_and_thermal_harmonic_oscillator
    (s_p s_q A C : B)
    (hsp : ∀ X : B, s_p * X = X * s_p) (hsq : ∀ X : B, s_q * X = X * s_q) :
    -OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
      -((2 : ℤ) • OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) ∧
    -OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
      -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    -OperatorAlgebra.PeirceSpine.comm (genJ P A C)
        (OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C)) =
      (2 : ℤ) • OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genJ P A C) ∧
    -OperatorAlgebra.PeirceSpine.comm (genJ P A C)
        (OperatorAlgebra.PeirceSpine.comm (genJ P A C) (genPhi P A C)) =
      (4 : ℤ) • (genV P A C * genPhi P A C) ∧
    OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q)
        (OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genPhi P A C)) =
      (s_q - s_p) * (s_q - s_p) * genPhi P A C ∧
    OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q)
        (OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genJ P A C)) =
      (s_q - s_p) * (s_q - s_p) * genJ P A C := by
  have hPPhi : OperatorAlgebra.PeirceSpine.comm P (genPhi P A C) = genJ P A C := by
    peirce_nf hP
  have hPJ : OperatorAlgebra.PeirceSpine.comm P (genJ P A C) = genPhi P A C := by
    peirce_nf hP
  have h1 : OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genPhi P A C) =
      (s_p - s_q) * genJ P A C := by
    rw [comm_sheetSurprisalOp_eq P s_p s_q (genPhi P A C) (hsp _) (hsq _), hPPhi]
  have h2 : OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genJ P A C) =
      (s_p - s_q) * genPhi P A C := by
    rw [comm_sheetSurprisalOp_eq P s_p s_q (genJ P A C) (hsp _) (hsq _), hPJ]
  have hCommFactor : ∀ Y : B,
      OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) ((s_p - s_q) * Y) =
        (s_p - s_q) * OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) Y := by
    intro Y
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    have hK : sheetSurprisalOp P s_p s_q * (s_p - s_q) =
        (s_p - s_q) * sheetSurprisalOp P s_p s_q := by
      rw [mul_sub, sub_mul, ← hsp (sheetSurprisalOp P s_p s_q),
          ← hsq (sheetSurprisalOp P s_p s_q)]
    calc
      sheetSurprisalOp P s_p s_q * ((s_p - s_q) * Y) -
          ((s_p - s_q) * Y) * sheetSurprisalOp P s_p s_q
        = (sheetSurprisalOp P s_p s_q * (s_p - s_q)) * Y -
          (s_p - s_q) * (Y * sheetSurprisalOp P s_p s_q) := by noncomm_ring
      _ = (s_p - s_q) * (sheetSurprisalOp P s_p s_q * Y -
          Y * sheetSurprisalOp P s_p s_q) := by rw [hK]; noncomm_ring
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, ?_, ?_⟩
  · rw [h1, hCommFactor (genJ P A C), h2]
    noncomm_ring
  · rw [h2, hCommFactor (genPhi P A C), h1]
    noncomm_ring

end StageS5

/-! ===========================================================================
    Section 6: Stage 𝔖₆ — 5-Graded Supercolor Kantor Sandwich & 4th-Order Harmonics
    =========================================================================== -/

section StageS6

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔖₆` (`archetype_S6_five_graded_kantor_sandwich_and_fourth_order_harmonics`)**:
1. **Quadratic Kantor Uncertainty Sandwich (Spin-Dipole Difference Channel)**:
   `kantorG0 P A C (kantorG0 P A C X) - (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) = genSig P A C * X * genSig P A C`,
2. **Quadratic Kantor Uncertainty Sandwich (Fisher Metric Sum Channel)**:
   `kantorG0 P A C (kantorG0 P A C X) + (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) = genV P A C * X * genV P A C`,
3. **Evaluation on the Solder Form (`Σ Φ Σ = -V² Φ` and `V Φ V = V² Φ`)**:
   `genSig P A C * genPhi P A C * genSig P A C = -((genV P A C * genV P A C) * genPhi P A C)`
   and `genV P A C * genPhi P A C * genV P A C = (genV P A C * genV P A C) * genPhi P A C`,
4. **4th-Order Centrifugal Frame Dragging (`[Σ, [Σ, Φ]] = 4 V² Φ`)**:
   `comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) = (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)`. -/
theorem archetype_S6_five_graded_kantor_sandwich_and_fourth_order_harmonics (A C X : B) :
    kantorG0 P A C (kantorG0 P A C X) -
      (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
        genSig P A C * X * genSig P A C ∧
    kantorG0 P A C (kantorG0 P A C X) +
      (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
        genV P A C * X * genV P A C ∧
    genSig P A C * genPhi P A C * genSig P A C =
      -((genV P A C * genV P A C) * genPhi P A C) ∧
    genV P A C * genPhi P A C * genV P A C =
      (genV P A C * genV P A C) * genPhi P A C ∧
    OperatorAlgebra.PeirceSpine.comm (genSig P A C)
      (OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) =
        (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) := by
  unfold kantorG0 kantorTriple kantorGp2 kantorGm2
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

end StageS6

/-! ===========================================================================
Section 7: Stage 𝔖₇ — BKM Resolvent Factorization and Divided Difference
    =========================================================================== -/

section StageS7

variable {B : Type*} [Ring B]

/-- The explicit two-sheet resolvent operator
`R_sheet(P, p, q, s) := (p + s)⁻¹ • P + (q + s)⁻¹ • (1 - P)` over an `ℝ`-algebra `B`. -/
noncomputable def sheetResolventOp [Algebra ℝ B] (P : B) (p q s : ℝ) : B :=
  (p + s)⁻¹ • P + (q + s)⁻¹ • (1 - P)

/-- The Bogoliubov–Kubo–Mori (BKM) logarithmic divided difference
`K_BKM(p, q) := (-log(q / p)) / (p - q)`. -/
noncomputable def bkmKernel (p q : ℝ) : ℝ :=
  (-Real.log (q / p)) / (p - q)

/-- The operator-valued multiple of the strain by the scalar logarithmic divided difference.
This definition is a candidate coefficient form; no integral representation is asserted here. -/
noncomputable def bkmDividedDifferenceOperator [Algebra ℝ B] (P A C : B) (p q : ℝ) : B :=
  (bkmKernel p q) • genV P A C

variable {P : B} (hP : P * P = P)
include hP

/-- Cross-sheet commutation law: for any central scalars `u, v : B`,
`Φ * (u P + v (1 - P)) = (v P + u (1 - P)) * Φ`. -/
theorem genPhi_mul_sheetThermalState_eq (A C u v : B)
    (hu : ∀ X : B, u * X = X * u) (hv : ∀ X : B, v * X = X * v) :
    genPhi P A C * sheetThermalState P u v =
      sheetThermalState P v u * genPhi P A C := by
  unfold sheetThermalState
  have hPhiP : genPhi P A C * P = (1 - P) * genPhi P A C := by peirce_nf hP
  have hPhi1P : genPhi P A C * (1 - P) = P * genPhi P A C := by peirce_nf hP
  calc
    genPhi P A C * (u * P + v * (1 - P))
      = (genPhi P A C * u) * P + (genPhi P A C * v) * (1 - P) := by noncomm_ring
    _ = u * (genPhi P A C * P) + v * (genPhi P A C * (1 - P)) := by
          rw [← hu (genPhi P A C), ← hv (genPhi P A C)]; noncomm_ring
    _ = u * ((1 - P) * genPhi P A C) + v * (P * genPhi P A C) := by
          rw [hPhiP, hPhi1P]
    _ = (v * P + u * (1 - P)) * genPhi P A C := by noncomm_ring

/-- Cross-sheet sandwich collapse over any ring `B`: for central scalars `u, v : B`,
`Φ (u P + v(1 - P)) Φ (u P + v(1 - P)) = (u * v) * V` and
`(u P + v(1 - P)) Φ (u P + v(1 - P)) Φ = (u * v) * V`. -/
theorem sheetThermalState_genPhi_sandwich_eq (A C u v : B)
    (hu : ∀ X : B, u * X = X * u) (hv : ∀ X : B, v * X = X * v) :
    genPhi P A C * sheetThermalState P u v * genPhi P A C * sheetThermalState P u v =
      (u * v) * genV P A C ∧
    sheetThermalState P u v * genPhi P A C * sheetThermalState P u v * genPhi P A C =
      (u * v) * genV P A C := by
  have hSwap1 := genPhi_mul_sheetThermalState_eq hP A C u v hu hv
  have hSwap2 := genPhi_mul_sheetThermalState_eq hP A C v u hv hu
  have hPhi2 : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
  have hProd1 : sheetThermalState P v u * sheetThermalState P u v = u * v := by
    rw [sheetThermalState_mul hP (hu P) (hv P), ← hu v]
    unfold sheetThermalState
    noncomm_ring
  have hProd2 : sheetThermalState P u v * sheetThermalState P v u = u * v := by
    rw [sheetThermalState_mul hP (hv P) (hu P), ← hu v]
    unfold sheetThermalState
    noncomm_ring
  refine ⟨?_, ?_⟩
  · calc
      genPhi P A C * sheetThermalState P u v * genPhi P A C * sheetThermalState P u v
        = (genPhi P A C * sheetThermalState P u v) *
          (genPhi P A C * sheetThermalState P u v) := by noncomm_ring
      _ = (sheetThermalState P v u * genPhi P A C) *
          (sheetThermalState P v u * genPhi P A C) := by rw [hSwap1]
      _ = sheetThermalState P v u *
          (genPhi P A C * sheetThermalState P v u) * genPhi P A C := by noncomm_ring
      _ = (sheetThermalState P v u * sheetThermalState P u v) *
          (genPhi P A C * genPhi P A C) := by rw [hSwap2]; noncomm_ring
      _ = (u * v) * genV P A C := by rw [hProd1, hPhi2]
  · calc
      sheetThermalState P u v * genPhi P A C * sheetThermalState P u v * genPhi P A C
        = sheetThermalState P u v *
          (genPhi P A C * sheetThermalState P u v) * genPhi P A C := by noncomm_ring
      _ = (sheetThermalState P u v * sheetThermalState P v u) *
          (genPhi P A C * genPhi P A C) := by rw [hSwap1]; noncomm_ring
      _ = (u * v) * genV P A C := by rw [hProd2, hPhi2]

/-- **Archetype `𝔖₇` (`archetype_S7_bkm_resolvent_factorization_and_divided_difference`)**:
Over any `[Algebra ℝ B]`:
1. **Two-Sided Resolvent Inverse (`(ρ + s I) (ρ + s I)⁻¹ = 1`)**:
   When `p + s ≠ 0` and `q + s ≠ 0`,
   `((p + s) • P + (q + s) • (1 - P)) * sheetResolventOp P p q s = 1` and
   `sheetResolventOp P p q s * ((p + s) • P + (q + s) • (1 - P)) = 1`,
2. **Cross-Sheet Resolvent Sandwich Collapse (`Φ (ρ + s I)⁻¹ Φ (ρ + s I)⁻¹ = ((p+s)(q+s))⁻¹ V`)**:
   `genPhi P A C * sheetResolventOp P p q s * genPhi P A C * sheetResolventOp P p q s = ((p + s)⁻¹ * (q + s)⁻¹) • genV P A C`
   and `sheetResolventOp P p q s * genPhi P A C * sheetResolventOp P p q s * genPhi P A C = ((p + s)⁻¹ * (q + s)⁻¹) • genV P A C`,
3. **Exact BKM Partial-Fraction Decomposition**:
   When `p - q ≠ 0`, `p + s ≠ 0`, and `q + s ≠ 0`,
   `(p + s)⁻¹ * (q + s)⁻¹ = (p - q)⁻¹ * ((q + s)⁻¹ - (p + s)⁻¹)`,
4. **BKM Kernel Divided-Difference Symmetry (`bkmKernel p q = (log p - log q) / (p - q) = bkmKernel q p`)**:
   When `0 < p` and `0 < q`,
   `bkmKernel p q = (Real.log p - Real.log q) / (p - q) ∧ bkmKernel p q = bkmKernel q p`,
5. **Trace Evaluation of the Divided-Difference Multiple of the Strain**:
   For any `ℝ`-linear map `τ : B →ₗ[ℝ] ℝ`,
   `τ (bkmDividedDifferenceOperator P A C p q) = bkmKernel p q * τ (genV P A C)`.
The theorem does not evaluate an improper integral; it proves the algebraic resolvent identities
and the trace of the explicitly defined divided-difference multiple. -/
theorem archetype_S7_bkm_resolvent_factorization_and_divided_difference
    [Algebra ℝ B] (A C : B) {p q s : ℝ}
    (hps : p + s ≠ 0) (hqs : q + s ≠ 0) (hpq : p - q ≠ 0)
    (hp : 0 < p) (hq : 0 < q) (τ : B →ₗ[ℝ] ℝ) :
    ((p + s) • P + (q + s) • (1 - P)) * sheetResolventOp P p q s = 1 ∧
    sheetResolventOp P p q s * ((p + s) • P + (q + s) • (1 - P)) = 1 ∧
    genPhi P A C * sheetResolventOp P p q s * genPhi P A C * sheetResolventOp P p q s =
      ((p + s)⁻¹ * (q + s)⁻¹) • genV P A C ∧
    sheetResolventOp P p q s * genPhi P A C * sheetResolventOp P p q s * genPhi P A C =
      ((p + s)⁻¹ * (q + s)⁻¹) • genV P A C ∧
    (p + s)⁻¹ * (q + s)⁻¹ = (p - q)⁻¹ * ((q + s)⁻¹ - (p + s)⁻¹) ∧
    bkmKernel p q = (Real.log p - Real.log q) / (p - q) ∧
    bkmKernel p q = bkmKernel q p ∧
    τ (bkmDividedDifferenceOperator P A C p q) = bkmKernel p q * τ (genV P A C) := by
  have hResEq : sheetResolventOp P p q s =
      sheetThermalState P (algebraMap ℝ B (p + s)⁻¹) (algebraMap ℝ B (q + s)⁻¹) := by
    unfold sheetResolventOp sheetThermalState
    rw [Algebra.smul_def, Algebra.smul_def]
  have hShiftedEq : (p + s) • P + (q + s) • (1 - P) =
      sheetThermalState P (algebraMap ℝ B (p + s)) (algebraMap ℝ B (q + s)) := by
    unfold sheetThermalState
    rw [Algebra.smul_def, Algebra.smul_def]
  have hSand :=
    sheetThermalState_genPhi_sandwich_eq hP A C
      (algebraMap ℝ B (p + s)⁻¹) (algebraMap ℝ B (q + s)⁻¹)
      (Algebra.commutes _) (Algebra.commutes _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hShiftedEq, hResEq,
        sheetThermalState_mul hP (Algebra.commutes _ _) (Algebra.commutes _ _),
        ← map_mul, ← map_mul, mul_inv_cancel₀ hps, mul_inv_cancel₀ hqs, map_one]
    unfold sheetThermalState
    noncomm_ring
  · rw [hShiftedEq, hResEq,
        sheetThermalState_mul hP (Algebra.commutes _ _) (Algebra.commutes _ _),
        ← map_mul, ← map_mul, inv_mul_cancel₀ hps, inv_mul_cancel₀ hqs, map_one]
    unfold sheetThermalState
    noncomm_ring
  · rw [hResEq, hSand.1, ← map_mul, ← Algebra.smul_def]
  · rw [hResEq, hSand.2, ← map_mul, ← Algebra.smul_def]
  · field_simp [hps, hqs, hpq]
    ring
  · unfold bkmKernel
    rw [Real.log_div hq.ne' hp.ne']
    ring
  · unfold bkmKernel
    rw [Real.log_div hq.ne' hp.ne', Real.log_div hp.ne' hq.ne']
    have hqp : q - p = -(p - q) := by ring
    rw [hqp, div_neg]
    ring
  · unfold bkmDividedDifferenceOperator
    rw [map_smul, smul_eq_mul]

end StageS7

/-! ===========================================================================
    Section 8: Stage 𝔖₈ — Metriplectic Cramér–Rao Closure, Master Synthesis &
    Matrix Witnesses
    =========================================================================== -/

section StageS8

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Archetype `𝔖₈` (`archetype_S8_metriplectic_cramer_rao_closure`)**:
Combines the operator BKM relative-volume metric, the Master Clocking Identity, and the
Hilbert-space metriplectic Cramér–Rao bound into a unified closure theorem. -/
theorem archetype_S8_metriplectic_cramer_rao_closure
    [Algebra ℝ B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ : NormalizedState H) (X_op Y_op : H →L[ℂ] H)
    (A C : B) {p q s : ℝ} (hps : p + s ≠ 0) (hqs : q + s ≠ 0) (hpq : p - q ≠ 0)
    (hp : 0 < p) (hq : 0 < q) (τ : B →ₗ[ℝ] ℝ) :
    -OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
      -((2 : ℤ) • OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) ∧
    genPhi P A C * sheetResolventOp P p q s * genPhi P A C * sheetResolventOp P p q s =
      ((p + s)⁻¹ * (q + s)⁻¹) • genV P A C ∧
    τ (bkmDividedDifferenceOperator P A C p q) = bkmKernel p q * τ (genV P A C) ∧
    onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
      (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
        (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 ∧
    fubiniStudyMetric ψ X_op X_op * fubiniStudyMetric ψ Y_op Y_op ≥
      (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2 := by
  have hS7 :=
    archetype_S7_bkm_resolvent_factorization_and_divided_difference hP A C hps hqs hpq hp hq τ
  exact ⟨by peirce_nf hP, hS7.2.2.1, hS7.2.2.2.2.2.2.2,
         cramerRao_metriplectic_full_bound ψ X_op Y_op,
         cramerRao_commutator_uncertainty_bound ψ X_op Y_op⟩

/-- **Master Operator Surprisal, Volume Resolvent, Master Clocking, Kantor Sandwich & BKM Closure
Synthesis (`modular_surprisal_volume_clocking_bkm_master_synthesis`)**:
Coagulates the complete 8-stage Acyclic Causal Poset `𝔖₁ ≺ 𝔖₂ ≺ 𝔖₃ ≺ 𝔖₄ ≺ 𝔖₅ ≺ 𝔖₆ ≺ 𝔖₇ ≺ 𝔖₈`
into a single kernel-verified theorem. -/
theorem modular_surprisal_volume_clocking_bkm_master_synthesis
    [Algebra ℝ B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ : NormalizedState H) (X_op Y_op : H →L[ℂ] H)
    (A C X s_p s_q β W_β : B)
    (hsp : ∀ Y : B, s_p * Y = Y * s_p) (hsq : ∀ Y : B, s_q * Y = Y * s_q)
    (hβ : ∀ Y : B, β * Y = Y * β)
    (hW_right : volumeMetricDenom P A C β * W_β = 1)
    (hW_left : W_β * volumeMetricDenom P A C β = 1)
    (u v : Vec3 B)
    {p q s : ℝ} (hps : p + s ≠ 0) (hqs : q + s ≠ 0) (hpq : p - q ≠ 0)
    (hp : 0 < p) (hq : 0 < q) (τ : B →ₗ[ℝ] ℝ) :
    -- (0) Acyclic 8-stage causal poset 𝔖₁ ≺ ⋯ ≺ 𝔖₈
    ((∀ st : ModularSurprisalClockingStage,
        ¬ Relation.TransGen ModularSurprisalClockingStage.causalEdge st st) ∧
     ModularSurprisalClockingStage.causalEdge
       .S1_SupercolorVacuumDeformationAndFrozenClock
       .S2_SheetSurprisalIdempotentNormalForm ∧
     ModularSurprisalClockingStage.causalEdge
       .S7_BKMResolventFactorizationAndDividedDifference
       .S8_MetriplecticCramerRaoClosureAndMasterSynthesis) ∧
    -- (1) Stage 𝔖₁ & 𝔖₂: Supercolor vacuum strain & Sheet surprisal idempotent normal form
    (sheetThermalState P s_p s_p = s_p ∧
     (P + genPhi P A C) * (P + genPhi P A C) - (P + genPhi P A C) = genV P A C ∧
     ZornMatrix.zornV u v = ZornMatrix.bilinearCondensate u v ∧
     (2 : ℤ) • sheetSurprisalOp P s_p s_q = (s_p + s_q) - (s_q - s_p) * invS P ∧
     realSheetSurprisalOp P p q =
       ((-(Real.log p + Real.log q) / 2) : ℝ) • (1 : B) -
         (((-Real.log q - -Real.log p) / 2) : ℝ) • invS P) ∧
    -- (2) Stage 𝔖₃: Relative volume resolvent commutation & odd resolvent force
    (W_β * genPhi P A C = genPhi P A C * W_β ∧
    OperatorAlgebra.PeirceSpine.anticomm (invS P)
      (volumeResolventForce P A C β W_β) = 0 ∧
    volumeMetricDenom P A C β * volumeResolventForce P A C β W_β =
       (2 : ℤ) • (β * genPhi P A C)) ∧
    -- (3) Stage 𝔖₄ & 𝔖₅: Modular precession, Master Clocking Identity & Thermal oscillator
    (OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genPhi P A C) =
       -((s_q - s_p) * genJ P A C) ∧
     OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genJ P A C) =
       -((s_q - s_p) * genPhi P A C) ∧
     -OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
         (OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)) =
       -((2 : ℤ) • OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) ∧
     OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q)
         (OperatorAlgebra.PeirceSpine.comm (sheetSurprisalOp P s_p s_q) (genPhi P A C)) =
       (s_q - s_p) * (s_q - s_p) * genPhi P A C) ∧
    -- (4) Stage 𝔖₆: 5-graded Kantor uncertainty sandwich & 4th-order centrifugal harmonics
    (kantorG0 P A C (kantorG0 P A C X) -
       (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
         genSig P A C * X * genSig P A C ∧
     kantorG0 P A C (kantorG0 P A C X) +
       (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
         genV P A C * X * genV P A C ∧
     OperatorAlgebra.PeirceSpine.comm (genSig P A C)
         (OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)) =
       (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)) ∧
    -- (5) Stage 𝔖₇ & 𝔖₈: BKM resolvent factorization & Metriplectic Cramér–Rao bound
    (genPhi P A C * sheetResolventOp P p q s * genPhi P A C * sheetResolventOp P p q s =
       ((p + s)⁻¹ * (q + s)⁻¹) • genV P A C ∧
     (p + s)⁻¹ * (q + s)⁻¹ = (p - q)⁻¹ * ((q + s)⁻¹ - (p + s)⁻¹) ∧
     bkmKernel p q = (Real.log p - Real.log q) / (p - q) ∧
    τ (bkmDividedDifferenceOperator P A C p q) = bkmKernel p q * τ (genV P A C) ∧
     onsagerDissipativeMetric ψ X_op X_op * onsagerDissipativeMetric ψ Y_op Y_op ≥
       (onsagerDissipativeMetric ψ X_op Y_op) ^ 2 +
         (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X_op Y_op) ^ 2) := by
  have hS1 :=
    archetype_S1_supercolor_vacuum_deformation_and_frozen_clock hP s_p s_p A C hsp u v
  have hS2 :=
    archetype_S2_sheet_surprisal_idempotent_normal_form hP (hsp P) (hsq P) s_p s_q 0 hp hq
  have hS3 :=
    archetype_S3_relative_volume_resolvent_force hP A C β W_β 0 hβ
      hW_right hW_left (by simp)
  have hS4 :=
    archetype_S4_algebraic_modular_commutator_action hP s_p s_q A C hsp hsq p q
  have hS5 :=
    archetype_S5_master_clocking_identity_and_thermal_harmonic_oscillator hP s_p s_q A C hsp hsq
  have hS6 :=
    archetype_S6_five_graded_kantor_sandwich_and_fourth_order_harmonics hP A C X
  have hS7 :=
    archetype_S7_bkm_resolvent_factorization_and_divided_difference hP A C hps hqs hpq hp hq τ
  exact ⟨⟨ModularSurprisalClockingStage.causalEdge_acyclic,
          ModularSurprisalClockingStage.causalEdge_chain_and_diamond.1,
          ModularSurprisalClockingStage.causalEdge_chain_and_diamond.2.2.2.2.2.2.2⟩,
         ⟨hS1.1, hS1.2.2.1, hS1.2.2.2.2.1, hS2.2.1, hS2.2.2.2.1⟩,
         ⟨hS3.2.2.2.1, hS3.2.2.2.2.1, hS3.2.2.2.2.2⟩,
         ⟨hS4.2.1, hS4.2.2.2.1, hS5.1, hS5.2.2.2.2.1⟩,
         ⟨hS6.1, hS6.2.1, hS6.2.2.2.2⟩,
         ⟨hS7.2.2.1, hS7.2.2.2.2.1, hS7.2.2.2.2.2.1, hS7.2.2.2.2.2.2.2,
          cramerRao_metriplectic_full_bound ψ X_op Y_op⟩⟩

end StageS8

/-! ### Concrete Non-Commutative `2 × 2` and `3 × 3` Matrix Witnesses (`Trap T16` & `Trap T17`) -/

/-- Polymorphic `3 × 3` upper-left projector matrix `!![1, 0, 0; 0, 0, 0; 0, 0, 0]` over `[Ring R]`. -/
def witnessMat3Proj {R : Type*} [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; 0, 0, 0; 0, 0, 0]

/-- Polymorphic `3 × 3` off-diagonal potential matrix `!![0, 1, 0; 1, 0, 0; 0, 0, 0]` over `[Ring R]`. -/
def witnessMat3Pot {R : Type*} [Ring R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 0]

/-- **Trap T16 Non-Commutativity Witness (`witnessMat3Proj_witnessMat3Pot_noncomm`)**:
Over any nontrivial ring `[Ring R] [Nontrivial R]`, `witnessMat3Proj` and `witnessMat3Pot` do not
commute in `Matrix (Fin 3) (Fin 3) R`. -/
theorem witnessMat3Proj_witnessMat3Pot_noncomm {R : Type*} [Ring R] [Nontrivial R] :
    (witnessMat3Proj : Matrix (Fin 3) (Fin 3) R) * (witnessMat3Pot : Matrix (Fin 3) (Fin 3) R) ≠
      (witnessMat3Pot : Matrix (Fin 3) (Fin 3) R) * (witnessMat3Proj : Matrix (Fin 3) (Fin 3) R) := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  simp [witnessMat3Proj, witnessMat3Pot, Matrix.mul_apply, Fin.sum_univ_three] at h01

/-- **Trap T16 & T17 Witness (`modular_surprisal_clocking_matrix_witness`)**:
On the concrete `2 × 2` integer matrices `(witnessProj2, witnessPot2)` with scalar sheet surprisal
matrices `s_p = !![3, 0; 0, 3]` and `s_q = !![1, 0; 0, 1]`:
1. `witnessProj2 * witnessPot2 ≠ witnessPot2 * witnessProj2` (`T16`),
2. `sheetSurprisalOp witnessProj2 !![3, 0; 0, 3] !![1, 0; 0, 1] = !![3, 0; 0, 1] ≠ 0` (`T17`),
3. `comm (sheetSurprisalOp witnessProj2 !![3, 0; 0, 3] !![1, 0; 0, 1]) (genPhi witnessProj2 witnessPot2 witnessPot2) = !![0, 2; -2, 0] ≠ 0` (`T17`). -/
theorem modular_surprisal_clocking_matrix_witness :
    witnessProj2 * witnessPot2 ≠ witnessPot2 * witnessProj2 ∧
    sheetSurprisalOp witnessProj2 !![3, 0; 0, 3] !![1, 0; 0, 1] = !![3, 0; 0, 1] ∧
    sheetSurprisalOp witnessProj2 !![3, 0; 0, 3] !![1, 0; 0, 1] ≠ 0 ∧
    OperatorAlgebra.PeirceSpine.comm
        (sheetSurprisalOp witnessProj2 !![3, 0; 0, 3] !![1, 0; 0, 1])
        (genPhi witnessProj2 witnessPot2 witnessPot2) = !![0, 2; -2, 0] ∧
    OperatorAlgebra.PeirceSpine.comm
        (sheetSurprisalOp witnessProj2 !![3, 0; 0, 3] !![1, 0; 0, 1])
        (genPhi witnessProj2 witnessPot2 witnessPot2) ≠ 0 := by
  have hNoncomm := (witnessMatProj2_witnessMatPot2_noncomm (B := ℤ)).2
  have h1P : (1 : Matrix (Fin 2) (Fin 2) ℤ) - witnessProj2 = !![0, 0; 0, 1] := by
    unfold witnessProj2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hSurp : sheetSurprisalOp witnessProj2 !![3, 0; 0, 3] !![1, 0; 0, 1] = !![3, 0; 0, 1] := by
    unfold sheetSurprisalOp
    rw [h1P]
    unfold witnessProj2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hPhi := witnessProj2_pot2_evals.2.1
  have hComm :
      OperatorAlgebra.PeirceSpine.comm
          (sheetSurprisalOp witnessProj2 !![3, 0; 0, 3] !![1, 0; 0, 1])
          (genPhi witnessProj2 witnessPot2 witnessPot2) = !![0, 2; -2, 0] := by
    rw [hSurp, hPhi]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp
  refine ⟨hNoncomm, hSurp, ?_, hComm, ?_⟩
  · rw [hSurp]
    intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simp at h00
  · rw [hComm]
    intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp at h01

end InfoGeometry.Canonical.ModularSurprisalVolumeClockingBKMClosurePoset

end
