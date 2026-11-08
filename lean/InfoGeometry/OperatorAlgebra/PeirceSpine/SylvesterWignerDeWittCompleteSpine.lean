/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Order.Hom.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset

/-!
# Stage D₈₁ (Archetypes SW₁ → SW₁₀): Living Sylvester Clock–Shift Algebra, DeWitt–Schur 4-Block LDU Factorization, Bergman Unipotent Conjugations, and Multi-Site Jordan–Wigner Clifford Chains

1. **Archetype SW₁ (`SW1_livingSylvesterClockShift`)**:
   Sylvester clock–shift operators `sylClock P A C = genSig P A C`, `sylShiftX P A C = genPhi P A C`,
   and `sylShiftY P A C = genJ P A C`, satisfying mutual anticommutation and `sylShiftY * sylShiftX = sylClock`.
2. **Archetype SW₂ (`SW2_dewittSchurBlockLDU`)**:
   DeWitt–Schur block LDU factorization `dewittL P C * dewittSchur00 P A C M * dewittU P A = P + genPhi P A C + peirce00 P M`.
3. **Archetype SW₃ (`SW3_dewittUnipotentStripping`)**:
   Unipotent stripping `dewittLInv P C * (P + genPhi P A C + peirce00 P M) * dewittUInv P A = dewittSchur00 P A C M`.
4. **Archetype SW₄ (`SW4_internalJordanWignerStringTwist`)**:
   Internal Jordan–Wigner string twist `jwStringTwist P X = invS P * X` converting odd-grade
   commutators into anticommutators `anticomm (genPhi P A C) (jwStringTwist P X) = -(invS P * comm (genPhi P A C) X)`.
5. **Archetype SW₅ (`SW5_multisiteJordanWignerTensorChain`)**:
   Two-site nilpotent Jordan–Wigner chain with `(Ψp1 + Ψp2)² = 0`, `(Ψm1 + Ψm2)² = 0`, and
   `anticomm (Ψp1 + Ψp2) (Ψm1 + Ψm2) = genV P A C + anticomm Np2 Nm2`.
6. **Archetype SW₆ (`SW6_dewittBergmanUnipotentConjugations`)**:
   DeWitt–Bergman unipotent conjugations of `1 - qgtMinus`, `1 - qgtPlus`, unipotent invariance
   of `1 - genV P A C`, and LDU factorizations of `1 - genPhi P A C`.
7. **Archetype SW₇ (`SW7_fullFourBlockWeightedDeWittSchurLDU`)**:
   Full 4-block weighted DeWitt–Schur LDU factorization `dewittL P C * dewittSchurFull P A C M * dewittU P A`
   for arbitrary diagonal blocks `peirce11 P M` and `peirce00 P M`.
8. **Archetype SW₈ (`SW8_singleSiteCliffordExtension`)**:
   Single-site internal Jordan–Wigner Clifford extension `(genPhi P A C + jwStringTwist P E)² = genV P A C + E * E`
   and `(genJ P A C + jwStringTwist P E)² = -genV P A C + E * E`.
9. **Archetype SW₉ (`SW9_completeCl22JordanWignerQuartet`)**:
   Complete 2-site `Cl_{2,2}(V₁, V₂)` Clifford quartet `(Γ₁, Γ̃₁, Γ₂, Γ̃₂)` with
   `(Γ₁ + Γ₂)² = genV P A C + anticomm Np2 Nm2` and `(Γ̃₁ + Γ̃₂)² = -(genV P A C + anticomm Np2 Nm2)`.
10. **Archetype SW₁₀ (`SW10_compositeSylvesterClockAdditivity`)**:
    Composite Sylvester clock additivity `comm (Ψp1 + Ψp2) (Ψm1 + Ψm2) = genSig P A C + comm Np2 Nm2`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.SylvesterWignerDeWittCompleteSpine

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset

variable {B : Type*} [Ring B]

/-! ### Causal Poset of Stage D₈₁ Archetypes (SW₁ → SW₁₀) -/

/-- The 10-stage causal poset of Sylvester clock–shift, DeWitt–Schur LDU, Bergman unipotent
conjugation, and multi-site Jordan–Wigner Clifford chain archetypes (`SW₁ → SW₁₀`). -/
inductive StageD81Archetype
  | SW1_livingSylvesterClockShift
  | SW2_dewittSchurBlockLDU
  | SW3_dewittUnipotentStripping
  | SW4_internalJordanWignerStringTwist
  | SW5_multisiteJordanWignerTensorChain
  | SW6_dewittBergmanUnipotentConjugations
  | SW7_fullFourBlockWeightedDeWittSchurLDU
  | SW8_singleSiteCliffordExtension
  | SW9_completeCl22JordanWignerQuartet
  | SW10_compositeSylvesterClockAdditivity
  deriving DecidableEq, Repr

instance instInhabitedStageD81Archetype : Inhabited StageD81Archetype :=
  ⟨.SW1_livingSylvesterClockShift⟩

/-- Topological rank in the 10-stage causal poset. -/
def stageD81Rank : StageD81Archetype → ℕ
  | .SW1_livingSylvesterClockShift => 0
  | .SW2_dewittSchurBlockLDU => 1
  | .SW3_dewittUnipotentStripping => 2
  | .SW4_internalJordanWignerStringTwist => 3
  | .SW5_multisiteJordanWignerTensorChain => 4
  | .SW6_dewittBergmanUnipotentConjugations => 5
  | .SW7_fullFourBlockWeightedDeWittSchurLDU => 6
  | .SW8_singleSiteCliffordExtension => 7
  | .SW9_completeCl22JordanWignerQuartet => 8
  | .SW10_compositeSylvesterClockAdditivity => 9

theorem stageD81Rank_injective : Function.Injective stageD81Rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance instPartialOrderStageD81Archetype : PartialOrder StageD81Archetype :=
  PartialOrder.lift stageD81Rank stageD81Rank_injective

theorem stageD81_strict_causal_chain :
    StageD81Archetype.SW1_livingSylvesterClockShift < .SW2_dewittSchurBlockLDU ∧
    StageD81Archetype.SW2_dewittSchurBlockLDU < .SW3_dewittUnipotentStripping ∧
    StageD81Archetype.SW3_dewittUnipotentStripping < .SW4_internalJordanWignerStringTwist ∧
    StageD81Archetype.SW4_internalJordanWignerStringTwist < .SW5_multisiteJordanWignerTensorChain ∧
    StageD81Archetype.SW5_multisiteJordanWignerTensorChain < .SW6_dewittBergmanUnipotentConjugations ∧
    StageD81Archetype.SW6_dewittBergmanUnipotentConjugations < .SW7_fullFourBlockWeightedDeWittSchurLDU ∧
    StageD81Archetype.SW7_fullFourBlockWeightedDeWittSchurLDU < .SW8_singleSiteCliffordExtension ∧
    StageD81Archetype.SW8_singleSiteCliffordExtension < .SW9_completeCl22JordanWignerQuartet ∧
    StageD81Archetype.SW9_completeCl22JordanWignerQuartet < .SW10_compositeSylvesterClockAdditivity := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Stage 0: Sylvester, DeWitt–Schur & Jordan–Wigner Operator Primitives -/

/-- Sylvester clock operator `genSig P A C`. -/
def sylClock (P A C : B) : B := genSig P A C

/-- Symmetric Sylvester shift operator `genPhi P A C`. -/
def sylShiftX (P A C : B) : B := genPhi P A C

/-- Skew Sylvester shift operator `genJ P A C`. -/
def sylShiftY (P A C : B) : B := genJ P A C

/-- Lower DeWitt unipotent factor `1 + N₋(C)`. -/
def dewittL (P C : B) : B := 1 + coneMinus P C

/-- Inverse lower DeWitt unipotent factor `1 - N₋(C)`. -/
def dewittLInv (P C : B) : B := 1 - coneMinus P C

/-- Upper DeWitt unipotent factor `1 + N₊(A)`. -/
def dewittU (P A : B) : B := 1 + conePlus P A

/-- Inverse upper DeWitt unipotent factor `1 - N₊(A)`. -/
def dewittUInv (P A : B) : B := 1 - conePlus P A

/-- Lower-right DeWitt–Schur complement diagonal operator `P + (peirce00 P M - qgtMinus P A C)`. -/
def dewittSchur00 (P A C M : B) : B :=
  P + (peirce00 P M - qgtMinus P A C)

/-- Upper-left DeWitt–Schur complement diagonal operator `(1 - P) + (peirce11 P M - qgtPlus P A C)`. -/
def dewittSchur11 (P A C M : B) : B :=
  (1 - P) + (peirce11 P M - qgtPlus P A C)

/-- Full 4-block weighted DeWitt–Schur diagonal operator
`peirce11 P M + (peirce00 P M - coneMinus P C * peirce11 P M * conePlus P A)`. -/
def dewittSchurFull (P A C M : B) : B :=
  peirce11 P M + (peirce00 P M - coneMinus P C * peirce11 P M * conePlus P A)

/-- Bilateral tilted operator `P + genPhi P A C`. -/
def goldenOp (P A C : B) : B := P + genPhi P A C

/-- Internal Jordan–Wigner parity string twist `invS P * X`. -/
def jwStringTwist (P X : B) : B := invS P * X

/-- Constructor-indexed operator realization mapping each `StageD81Archetype` stage to its
canonical operator in `[Ring B]`. -/
def stageD81Operator (P A C M E Np2 Nm2 : B) : StageD81Archetype → B
  | .SW1_livingSylvesterClockShift => sylShiftY P A C * sylShiftX P A C
  | .SW2_dewittSchurBlockLDU => dewittL P C * dewittSchur00 P A C M * dewittU P A
  | .SW3_dewittUnipotentStripping =>
      dewittLInv P C * (P + genPhi P A C + peirce00 P M) * dewittUInv P A
  | .SW4_internalJordanWignerStringTwist => jwStringTwist P (genPhi P A C)
  | .SW5_multisiteJordanWignerTensorChain =>
      anticomm (conePlus P A + jwStringTwist P Np2) (coneMinus P C + jwStringTwist P Nm2)
  | .SW6_dewittBergmanUnipotentConjugations =>
      dewittU P A * (1 - genV P A C) * dewittUInv P A
  | .SW7_fullFourBlockWeightedDeWittSchurLDU =>
      dewittL P C * dewittSchurFull P A C M * dewittU P A
  | .SW8_singleSiteCliffordExtension =>
      (genPhi P A C + jwStringTwist P E) * (genPhi P A C + jwStringTwist P E)
  | .SW9_completeCl22JordanWignerQuartet =>
      ((conePlus P A + coneMinus P C) + (jwStringTwist P Np2 + jwStringTwist P Nm2)) *
      ((conePlus P A + coneMinus P C) + (jwStringTwist P Np2 + jwStringTwist P Nm2))
  | .SW10_compositeSylvesterClockAdditivity =>
      (conePlus P A + jwStringTwist P Np2) * (coneMinus P C + jwStringTwist P Nm2) -
      (coneMinus P C - jwStringTwist P Nm2) * (conePlus P A - jwStringTwist P Np2)

macro "peirce_abel_dewitt" hP:ident : tactic =>
  `(tactic| (
    simp only [jwStringTwist, goldenOp,
               dewittSchurFull, dewittSchur00, dewittSchur11,
               dewittL, dewittLInv, dewittU, dewittUInv,
               sylClock, sylShiftX, sylShiftY,
               qgtPlus, qgtMinus,
               genPhi, genJ, genV, genSig,
               evenGrade, oddGrade, peirce11, peirce00,
               invS, comm, anticomm, idemDefect, conePlus, coneMinus,
               smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg,
               smul_smul, smul_zero, zero_smul, add_smul, sub_smul,
               zsmul_add, zsmul_sub, neg_zsmul, two_zsmul,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               sub_self, mul_zero, zero_mul, add_zero, zero_add, neg_zero,
               mul_assoc, $hP:ident, P_assoc $hP:ident]
    try abel))

/-! ### Archetype SW₁: Living Operator Sylvester Clock–Shift Algebra & Block Matrix Units -/

theorem archetype_SW1_living_sylvester_clock_shift_algebra
    {P : B} (hP : P * P = P) (A C : B) :
    anticomm (sylShiftX P A C) (sylClock P A C) = 0 ∧
    anticomm (sylShiftY P A C) (sylClock P A C) = 0 ∧
    anticomm (sylShiftX P A C) (sylShiftY P A C) = 0 ∧
    sylShiftY P A C * sylShiftX P A C = sylClock P A C ∧
    sylShiftX P A C * sylClock P A C = -(genV P A C * sylShiftY P A C) ∧
    sylShiftY P A C * sylClock P A C = -(genV P A C * sylShiftX P A C) ∧
    sylClock P A C * sylClock P A C = genV P A C * genV P A C ∧
    peirce11 P (sylClock P A C) = qgtPlus P A C ∧
    peirce00 P (sylClock P A C) = -qgtMinus P A C ∧
    conePlus P (sylShiftX P A C) = conePlus P A ∧
    coneMinus P (sylShiftX P A C) = coneMinus P C ∧
    conePlus P A * qgtMinus P A C = qgtPlus P A C * conePlus P A ∧
    coneMinus P C * qgtPlus P A C = qgtMinus P A C * coneMinus P C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_abel_dewitt hP

/-! ### Archetype SW₂: The DeWitt–Schur Block LDU Decomposition of Operators -/

theorem archetype_SW2_dewitt_schur_block_ldu_decomposition
    {P : B} (hP : P * P = P) (A C M : B) :
    dewittL P C * dewittSchur00 P A C M * dewittU P A =
      P + genPhi P A C + peirce00 P M ∧
    dewittU P A * dewittSchur11 P A C M * dewittL P C =
      (1 - P) + genPhi P A C + peirce11 P M ∧
    dewittL P C * (P - qgtMinus P A C) * dewittU P A =
      goldenOp P A C ∧
    dewittL P C * P * dewittU P A =
      P + genPhi P A C + qgtMinus P A C ∧
    dewittU P A * (1 - P) * dewittL P C =
      (1 - P) + genPhi P A C + qgtPlus P A C ∧
    dewittL P C * P * dewittU P A + dewittU P A * (1 - P) * dewittL P C =
      1 + (2 : ℤ) • genPhi P A C + genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel_dewitt hP

/-! ### Archetype SW₃: DeWitt Unipotent Stripping & Block Diagonalization of Operators -/

theorem archetype_SW3_dewitt_unipotent_stripping_and_block_diagonalization
    {P : B} (hP : P * P = P) (A C M : B) :
    dewittLInv P C * dewittL P C = 1 ∧
    dewittL P C * dewittLInv P C = 1 ∧
    dewittUInv P A * dewittU P A = 1 ∧
    dewittU P A * dewittUInv P A = 1 ∧
    dewittLInv P C * (P + genPhi P A C + peirce00 P M) * dewittUInv P A =
      dewittSchur00 P A C M ∧
    dewittUInv P A * ((1 - P) + genPhi P A C + peirce11 P M) * dewittLInv P C =
      dewittSchur11 P A C M ∧
    dewittLInv P C * goldenOp P A C * dewittUInv P A =
      P - qgtMinus P A C ∧
    dewittU P A * dewittL P C = 1 + genPhi P A C + qgtPlus P A C ∧
    dewittL P C * dewittU P A = 1 + genPhi P A C + qgtMinus P A C ∧
    dewittUInv P A * (1 + genPhi P A C + qgtPlus P A C) * dewittLInv P C = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel_dewitt hP

/-! ### Archetype SW₄: Internal Jordan–Wigner String Twist on a Single Peirce Grading -/

theorem archetype_SW4_internal_jordan_wigner_string_twist
    {P : B} (hP : P * P = P) (A C X Y : B) :
    anticomm (invS P) (oddGrade P Y) = 0 ∧
    comm (invS P) (evenGrade P X) = 0 ∧
    jwStringTwist P (oddGrade P Y) = comm P Y ∧
    jwStringTwist P (genPhi P A C) = genJ P A C ∧
    jwStringTwist P (genJ P A C) = genPhi P A C ∧
    jwStringTwist P (genV P A C) = genSig P A C ∧
    jwStringTwist P (genSig P A C) = genV P A C ∧
    anticomm (genPhi P A C) (jwStringTwist P X) =
      -(invS P * comm (genPhi P A C) X) ∧
    anticomm (genJ P A C) (jwStringTwist P X) =
      -(invS P * comm (genJ P A C) X) ∧
    anticomm (conePlus P A) (jwStringTwist P X) =
      -(invS P * comm (conePlus P A) X) ∧
    anticomm (coneMinus P C) (jwStringTwist P X) =
      -(invS P * comm (coneMinus P C) X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel_dewitt hP

/-! ### Archetype SW₅: Multi-Site Jordan–Wigner Fermion/Parafermion Tensor Chain in `B` -/

theorem archetype_SW5_multisite_jordan_wigner_tensor_chain
    {P : B} (hP : P * P = P) (A C Np2 Nm2 : B)
    (hNp2 : Np2 * Np2 = 0) (hNm2 : Nm2 * Nm2 = 0)
    (hCommP_p : comm P Np2 = 0) (hCommP_m : comm P Nm2 = 0)
    (hComm12_pp : comm (conePlus P A) Np2 = 0)
    (hComm12_pm : comm (conePlus P A) Nm2 = 0)
    (hComm12_mp : comm (coneMinus P C) Np2 = 0)
    (hComm12_mm : comm (coneMinus P C) Nm2 = 0) :
    let Ψp1 := conePlus P A
    let Ψm1 := coneMinus P C
    let Ψp2 := jwStringTwist P Np2
    let Ψm2 := jwStringTwist P Nm2
    anticomm Ψp1 Ψp2 = 0 ∧
    anticomm Ψp1 Ψm2 = 0 ∧
    anticomm Ψm1 Ψp2 = 0 ∧
    anticomm Ψm1 Ψm2 = 0 ∧
    Ψp2 * Ψp2 = 0 ∧
    Ψm2 * Ψm2 = 0 ∧
    (Ψp1 + Ψp2) * (Ψp1 + Ψp2) = 0 ∧
    (Ψm1 + Ψm2) * (Ψm1 + Ψm2) = 0 ∧
    anticomm (Ψp1 + Ψp2) (Ψm1 + Ψm2) =
      genV P A C + anticomm Np2 Nm2 := by
  intro Ψp1 Ψm1 Ψp2 Ψm2
  have hAnti_pp : anticomm Ψp1 Ψp2 = 0 := by
    have h := (archetype_SW4_internal_jordan_wigner_string_twist hP A C Np2 Np2).2.2.2.2.2.2.2.2.2.1
    dsimp [Ψp1, Ψp2]; rw [h, hComm12_pp, mul_zero, neg_zero]
  have hAnti_pm : anticomm Ψp1 Ψm2 = 0 := by
    have h := (archetype_SW4_internal_jordan_wigner_string_twist hP A C Nm2 Nm2).2.2.2.2.2.2.2.2.2.1
    dsimp [Ψp1, Ψm2]; rw [h, hComm12_pm, mul_zero, neg_zero]
  have hAnti_mp : anticomm Ψm1 Ψp2 = 0 := by
    have h := (archetype_SW4_internal_jordan_wigner_string_twist hP A C Np2 Np2).2.2.2.2.2.2.2.2.2.2
    dsimp [Ψm1, Ψp2]; rw [h, hComm12_mp, mul_zero, neg_zero]
  have hAnti_mm : anticomm Ψm1 Ψm2 = 0 := by
    have h := (archetype_SW4_internal_jordan_wigner_string_twist hP A C Nm2 Nm2).2.2.2.2.2.2.2.2.2.2
    dsimp [Ψm1, Ψm2]; rw [h, hComm12_mm, mul_zero, neg_zero]
  have hS_p : Np2 * invS P = invS P * Np2 := by
    have h1 : Np2 * invS P - invS P * Np2 = -((2 : ℤ) • comm P Np2) := by
      simp only [invS, comm, two_zsmul, sub_mul, mul_sub, one_mul, mul_one]; abel
    rw [hCommP_p, smul_zero, neg_zero] at h1
    exact sub_eq_zero.mp h1
  have hS_m : Nm2 * invS P = invS P * Nm2 := by
    have h1 : Nm2 * invS P - invS P * Nm2 = -((2 : ℤ) • comm P Nm2) := by
      simp only [invS, comm, two_zsmul, sub_mul, mul_sub, one_mul, mul_one]; abel
    rw [hCommP_m, smul_zero, neg_zero] at h1
    exact sub_eq_zero.mp h1
  have hSS : invS P * invS P = 1 := by peirce_abel_dewitt hP
  have hNil_p2 : Ψp2 * Ψp2 = 0 := by
    dsimp [Ψp2, jwStringTwist]
    calc (invS P * Np2) * (invS P * Np2)
      _ = invS P * (Np2 * invS P) * Np2 := by simp only [mul_assoc]
      _ = (invS P * invS P) * (Np2 * Np2) := by rw [hS_p]; simp only [mul_assoc]
      _ = 1 * 0 := by rw [hSS, hNp2]
      _ = 0 := mul_zero 1
  have hNil_m2 : Ψm2 * Ψm2 = 0 := by
    dsimp [Ψm2, jwStringTwist]
    calc (invS P * Nm2) * (invS P * Nm2)
      _ = invS P * (Nm2 * invS P) * Nm2 := by simp only [mul_assoc]
      _ = (invS P * invS P) * (Nm2 * Nm2) := by rw [hS_m]; simp only [mul_assoc]
      _ = 1 * 0 := by rw [hSS, hNm2]
      _ = 0 := mul_zero 1
  have hNil_p1 : Ψp1 * Ψp1 = 0 := by dsimp [Ψp1]; peirce_abel_dewitt hP
  have hNil_m1 : Ψm1 * Ψm1 = 0 := by dsimp [Ψm1]; peirce_abel_dewitt hP
  have hTot_p : (Ψp1 + Ψp2) * (Ψp1 + Ψp2) = 0 := by
    have hExp : (Ψp1 + Ψp2) * (Ψp1 + Ψp2) = Ψp1 * Ψp1 + anticomm Ψp1 Ψp2 + Ψp2 * Ψp2 := by
      simp only [anticomm, add_mul, mul_add]; abel
    rw [hExp, hNil_p1, hAnti_pp, hNil_p2, add_zero, add_zero]
  have hTot_m : (Ψm1 + Ψm2) * (Ψm1 + Ψm2) = 0 := by
    have hExp : (Ψm1 + Ψm2) * (Ψm1 + Ψm2) = Ψm1 * Ψm1 + anticomm Ψm1 Ψm2 + Ψm2 * Ψm2 := by
      simp only [anticomm, add_mul, mul_add]; abel
    rw [hExp, hNil_m1, hAnti_mm, hNil_m2, add_zero, add_zero]
  have hV2 : anticomm Ψp2 Ψm2 = anticomm Np2 Nm2 := by
    dsimp [Ψp2, Ψm2, jwStringTwist, anticomm]
    have hL : (invS P * Np2) * (invS P * Nm2) = Np2 * Nm2 := by
      calc (invS P * Np2) * (invS P * Nm2)
        _ = invS P * (Np2 * invS P) * Nm2 := by simp only [mul_assoc]
        _ = (invS P * invS P) * (Np2 * Nm2) := by rw [hS_p]; simp only [mul_assoc]
        _ = Np2 * Nm2 := by rw [hSS, one_mul]
    have hR : (invS P * Nm2) * (invS P * Np2) = Nm2 * Np2 := by
      calc (invS P * Nm2) * (invS P * Np2)
        _ = invS P * (Nm2 * invS P) * Np2 := by simp only [mul_assoc]
        _ = (invS P * invS P) * (Nm2 * Np2) := by rw [hS_m]; simp only [mul_assoc]
        _ = Nm2 * Np2 := by rw [hSS, one_mul]
    rw [hL, hR]
  have hTot_V : anticomm (Ψp1 + Ψp2) (Ψm1 + Ψm2) = genV P A C + anticomm Np2 Nm2 := by
    have hExp : anticomm (Ψp1 + Ψp2) (Ψm1 + Ψm2) =
        anticomm Ψp1 Ψm1 + anticomm Ψp1 Ψm2 + anticomm Ψm1 Ψp2 + anticomm Ψp2 Ψm2 := by
      simp only [anticomm, add_mul, mul_add]; abel
    rw [hExp, hAnti_pm, hAnti_mp, hV2, add_zero, add_zero]
    rfl
  exact ⟨hAnti_pp, hAnti_pm, hAnti_mp, hAnti_mm,
         hNil_p2, hNil_m2, hTot_p, hTot_m, hTot_V⟩

/-! ### Archetype SW₆: DeWitt–Bergman Unipotent Conjugations -/

theorem archetype_SW6_dewitt_bergman_unipotent_conjugations
    {P : B} (hP : P * P = P) (A C : B) :
    dewittU P A * (1 - qgtMinus P A C) * dewittUInv P A =
      1 - qgtMinus P A C - genV P A C * conePlus P A ∧
    dewittL P C * (1 - qgtPlus P A C) * dewittLInv P C =
      1 - qgtPlus P A C - genV P A C * coneMinus P C ∧
    dewittU P A * (1 - genV P A C) * dewittUInv P A = 1 - genV P A C ∧
    dewittL P C * (1 - genV P A C) * dewittLInv P C = 1 - genV P A C ∧
    dewittUInv P A * (1 - qgtPlus P A C) * dewittLInv P C =
      1 - genPhi P A C ∧
    dewittLInv P C * (1 - qgtMinus P A C) * dewittUInv P A =
      1 - genPhi P A C ∧
    dewittU P A * (1 - genPhi P A C) * dewittL P C =
      1 - qgtPlus P A C ∧
    dewittL P C * (1 - genPhi P A C) * dewittU P A =
      1 - qgtMinus P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_abel_dewitt hP

/-! ### Archetype SW₇: Full 4-Block Weighted DeWitt–Schur LDU Decomposition -/

theorem archetype_SW7_full_four_block_weighted_dewitt_schur_ldu
    {P : B} (hP : P * P = P) (A C M : B) :
    dewittL P C * dewittSchurFull P A C M * dewittU P A =
      peirce11 P M + peirce11 P M * conePlus P A +
      coneMinus P C * peirce11 P M + peirce00 P M ∧
    dewittLInv P C *
      (peirce11 P M + peirce11 P M * conePlus P A +
       coneMinus P C * peirce11 P M + peirce00 P M) *
      dewittUInv P A =
      dewittSchurFull P A C M := by
  refine ⟨?_, ?_⟩ <;> peirce_abel_dewitt hP

/-! ### Archetype SW₈: Single-Site Internal Jordan–Wigner Clifford Extension `(Φ + S_P E)² = V + E²` -/

theorem archetype_SW8_single_site_clifford_extension
    {P : B} (hP : P * P = P) (A C E : B)
    (hPE : comm P E = 0)
    (hNpE : comm (conePlus P A) E = 0)
    (hNmE : comm (coneMinus P C) E = 0) :
    anticomm (conePlus P A) (jwStringTwist P E) = 0 ∧
    anticomm (coneMinus P C) (jwStringTwist P E) = 0 ∧
    anticomm (genPhi P A C) (jwStringTwist P E) = 0 ∧
    anticomm (genJ P A C) (jwStringTwist P E) = 0 ∧
    jwStringTwist P E * jwStringTwist P E = E * E ∧
    (genPhi P A C + jwStringTwist P E) * (genPhi P A C + jwStringTwist P E) =
      genV P A C + E * E ∧
    (genJ P A C + jwStringTwist P E) * (genJ P A C + jwStringTwist P E) =
      -genV P A C + E * E := by
  rcases archetype_SW4_internal_jordan_wigner_string_twist hP A C E E with
    ⟨_, _, _, _, _, _, _, hPhi, hJ, hNp, hNm⟩
  have hPhiE : comm (genPhi P A C) E = 0 := by
    have h1 : comm (genPhi P A C) E = comm (conePlus P A) E + comm (coneMinus P C) E := by
      simp only [genPhi, comm, add_mul, mul_add]; abel
    rw [h1, hNpE, hNmE, add_zero]
  have hJE : comm (genJ P A C) E = 0 := by
    have h1 : comm (genJ P A C) E = comm (conePlus P A) E - comm (coneMinus P C) E := by
      simp only [genJ, comm, sub_mul, mul_sub]; abel
    rw [h1, hNpE, hNmE, sub_self]
  have hAntiNp : anticomm (conePlus P A) (jwStringTwist P E) = 0 := by
    rw [hNp, hNpE, mul_zero, neg_zero]
  have hAntiNm : anticomm (coneMinus P C) (jwStringTwist P E) = 0 := by
    rw [hNm, hNmE, mul_zero, neg_zero]
  have hAntiPhi : anticomm (genPhi P A C) (jwStringTwist P E) = 0 := by
    rw [hPhi, hPhiE, mul_zero, neg_zero]
  have hAntiJ : anticomm (genJ P A C) (jwStringTwist P E) = 0 := by
    rw [hJ, hJE, mul_zero, neg_zero]
  have hSE : E * invS P = invS P * E := by
    have h1 : E * invS P - invS P * E = -((2 : ℤ) • comm P E) := by
      simp only [invS, comm, two_zsmul, sub_mul, mul_sub, one_mul, mul_one]; abel
    rw [hPE, smul_zero, neg_zero] at h1
    exact sub_eq_zero.mp h1
  have hSS : invS P * invS P = 1 := by peirce_abel_dewitt hP
  have hSqE : jwStringTwist P E * jwStringTwist P E = E * E := by
    unfold jwStringTwist
    calc (invS P * E) * (invS P * E)
      _ = invS P * (E * invS P) * E := by simp only [mul_assoc]
      _ = (invS P * invS P) * (E * E) := by rw [hSE]; simp only [mul_assoc]
      _ = E * E := by rw [hSS, one_mul]
  have hPhiSq : genPhi P A C * genPhi P A C = genV P A C := by peirce_abel_dewitt hP
  have hJSq : genJ P A C * genJ P A C = -genV P A C := by peirce_abel_dewitt hP
  refine ⟨hAntiNp, hAntiNm, hAntiPhi, hAntiJ, hSqE, ?_, ?_⟩
  · have hExp : (genPhi P A C + jwStringTwist P E) * (genPhi P A C + jwStringTwist P E) =
        genPhi P A C * genPhi P A C +
        anticomm (genPhi P A C) (jwStringTwist P E) +
        jwStringTwist P E * jwStringTwist P E := by
      simp only [anticomm, add_mul, mul_add]; abel
    rw [hExp, hPhiSq, hAntiPhi, hSqE, add_zero]
  · have hExp : (genJ P A C + jwStringTwist P E) * (genJ P A C + jwStringTwist P E) =
        genJ P A C * genJ P A C +
        anticomm (genJ P A C) (jwStringTwist P E) +
        jwStringTwist P E * jwStringTwist P E := by
      simp only [anticomm, add_mul, mul_add]; abel
    rw [hExp, hJSq, hAntiJ, hSqE, add_zero]

/-! ### Archetype SW₉ & SW₁₀: Complete `Cl_{2,2}(V₁, V₂)` Quartet & Composite Sylvester Clock Additivity -/

theorem archetype_SW9_SW10_complete_cl22_quartet_and_sylvester_clock_additivity
    {P : B} (hP : P * P = P) (A C Np2 Nm2 : B)
    (hNp2 : Np2 * Np2 = 0) (hNm2 : Nm2 * Nm2 = 0)
    (hCommP_p : comm P Np2 = 0) (hCommP_m : comm P Nm2 = 0)
    (hComm12_pp : comm (conePlus P A) Np2 = 0)
    (hComm12_pm : comm (conePlus P A) Nm2 = 0)
    (hComm12_mp : comm (coneMinus P C) Np2 = 0)
    (hComm12_mm : comm (coneMinus P C) Nm2 = 0) :
    let Ψp1 := conePlus P A
    let Ψm1 := coneMinus P C
    let Ψp2 := jwStringTwist P Np2
    let Ψm2 := jwStringTwist P Nm2
    let Γ₁  := Ψp1 + Ψm1
    let Γt₁ := Ψp1 - Ψm1
    let Γ₂  := Ψp2 + Ψm2
    let Γt₂ := Ψp2 - Ψm2
    anticomm Γ₁ Γ₂ = 0 ∧
    anticomm Γt₁ Γt₂ = 0 ∧
    anticomm Γ₁ Γt₂ = 0 ∧
    anticomm Γt₁ Γ₂ = 0 ∧
    anticomm Γ₂ Γt₂ = 0 ∧
    (Γ₁ + Γ₂) * (Γ₁ + Γ₂) = genV P A C + anticomm Np2 Nm2 ∧
    (Γt₁ + Γt₂) * (Γt₁ + Γt₂) = -(genV P A C + anticomm Np2 Nm2) ∧
    (Ψp1 + Ψp2) * (Ψm1 + Ψm2) - (Ψm1 - Ψm2) * (Ψp1 - Ψp2) =
      genSig P A C + comm Np2 Nm2 := by
  intro Ψp1 Ψm1 Ψp2 Ψm2 Γ₁ Γt₁ Γ₂ Γt₂
  rcases archetype_SW5_multisite_jordan_wigner_tensor_chain
    hP A C Np2 Nm2 hNp2 hNm2 hCommP_p hCommP_m
    hComm12_pp hComm12_pm hComm12_mp hComm12_mm with
    ⟨hApp, hApm, hAmp, hAmm, hNil_p2, hNil_m2, hTot_p, hTot_m, hTot_V⟩
  have hLin : ∀ U₁ U₂ W₁ W₂ : B,
      anticomm (U₁ + U₂) (W₁ + W₂) =
        anticomm U₁ W₁ + anticomm U₁ W₂ + anticomm U₂ W₁ + anticomm U₂ W₂ ∧
      anticomm (U₁ - U₂) (W₁ - W₂) =
        anticomm U₁ W₁ - anticomm U₁ W₂ - anticomm U₂ W₁ + anticomm U₂ W₂ ∧
      anticomm (U₁ + U₂) (W₁ - W₂) =
        anticomm U₁ W₁ - anticomm U₁ W₂ + anticomm U₂ W₁ - anticomm U₂ W₂ ∧
      anticomm (U₁ - U₂) (W₁ + W₂) =
        anticomm U₁ W₁ + anticomm U₁ W₂ - anticomm U₂ W₁ - anticomm U₂ W₂ := by
    intro U₁ U₂ W₁ W₂
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [anticomm, add_mul, mul_add, sub_mul, mul_sub]; abel
  rcases hLin Ψp1 Ψm1 Ψp2 Ψm2 with ⟨hL1, hL2, hL3, hL4⟩
  have hG12 : anticomm Γ₁ Γ₂ = 0 := by
    dsimp [Γ₁, Γ₂]; rw [hL1, hApp, hApm, hAmp, hAmm, add_zero, add_zero, add_zero]
  have hGt12 : anticomm Γt₁ Γt₂ = 0 := by
    dsimp [Γt₁, Γt₂]; rw [hL2, hApp, hApm, hAmp, hAmm, sub_zero, sub_zero, add_zero]
  have hG1t2 : anticomm Γ₁ Γt₂ = 0 := by
    dsimp [Γ₁, Γt₂]; rw [hL3, hApp, hApm, hAmp, hAmm, sub_zero, add_zero, sub_zero]
  have hGt1G2 : anticomm Γt₁ Γ₂ = 0 := by
    dsimp [Γt₁, Γ₂]; rw [hL4, hApp, hApm, hAmp, hAmm, add_zero, sub_zero, sub_zero]
  have hG2t2 : anticomm Γ₂ Γt₂ = 0 := by
    dsimp [Γ₂, Γt₂]
    have hExp : anticomm (Ψp2 + Ψm2) (Ψp2 - Ψm2) =
        (2 : ℤ) • (Ψp2 * Ψp2 - Ψm2 * Ψm2) := by
      simp only [anticomm, two_zsmul, add_mul, mul_add, sub_mul, mul_sub]; abel
    rw [hExp, hNil_p2, hNil_m2, sub_self, smul_zero]
  have hSumEq : Γ₁ + Γ₂ = (Ψp1 + Ψp2) + (Ψm1 + Ψm2) := by
    dsimp [Γ₁, Γ₂]; abel
  have hDiffEq : Γt₁ + Γt₂ = (Ψp1 + Ψp2) - (Ψm1 + Ψm2) := by
    dsimp [Γt₁, Γt₂]; abel
  have hS_p : Np2 * invS P = invS P * Np2 := by
    have h1 : Np2 * invS P - invS P * Np2 = -((2 : ℤ) • comm P Np2) := by
      simp only [invS, comm, two_zsmul, sub_mul, mul_sub, one_mul, mul_one]; abel
    rw [hCommP_p, smul_zero, neg_zero] at h1
    exact sub_eq_zero.mp h1
  have hS_m : Nm2 * invS P = invS P * Nm2 := by
    have h1 : Nm2 * invS P - invS P * Nm2 = -((2 : ℤ) • comm P Nm2) := by
      simp only [invS, comm, two_zsmul, sub_mul, mul_sub, one_mul, mul_one]; abel
    rw [hCommP_m, smul_zero, neg_zero] at h1
    exact sub_eq_zero.mp h1
  have hSS : invS P * invS P = 1 := by peirce_abel_dewitt hP
  have hSig2 : comm Ψp2 Ψm2 = comm Np2 Nm2 := by
    dsimp [Ψp2, Ψm2, jwStringTwist, comm]
    have hL : (invS P * Np2) * (invS P * Nm2) = Np2 * Nm2 := by
      calc (invS P * Np2) * (invS P * Nm2)
        _ = invS P * (Np2 * invS P) * Nm2 := by simp only [mul_assoc]
        _ = (invS P * invS P) * (Np2 * Nm2) := by rw [hS_p]; simp only [mul_assoc]
        _ = Np2 * Nm2 := by rw [hSS, one_mul]
    have hR : (invS P * Nm2) * (invS P * Np2) = Nm2 * Np2 := by
      calc (invS P * Nm2) * (invS P * Np2)
        _ = invS P * (Nm2 * invS P) * Np2 := by simp only [mul_assoc]
        _ = (invS P * invS P) * (Nm2 * Np2) := by rw [hS_m]; simp only [mul_assoc]
        _ = Nm2 * Np2 := by rw [hSS, one_mul]
    rw [hL, hR]
  refine ⟨hG12, hGt12, hG1t2, hGt1G2, hG2t2, ?_, ?_, ?_⟩
  · rw [hSumEq]
    have hExp : ((Ψp1 + Ψp2) + (Ψm1 + Ψm2)) * ((Ψp1 + Ψp2) + (Ψm1 + Ψm2)) =
        (Ψp1 + Ψp2) * (Ψp1 + Ψp2) +
        anticomm (Ψp1 + Ψp2) (Ψm1 + Ψm2) +
        (Ψm1 + Ψm2) * (Ψm1 + Ψm2) := by
      simp only [anticomm, add_mul, mul_add]; abel
    rw [hExp, hTot_p, hTot_m, hTot_V, zero_add, add_zero]
  · rw [hDiffEq]
    have hExp : ((Ψp1 + Ψp2) - (Ψm1 + Ψm2)) * ((Ψp1 + Ψp2) - (Ψm1 + Ψm2)) =
        (Ψp1 + Ψp2) * (Ψp1 + Ψp2) -
        anticomm (Ψp1 + Ψp2) (Ψm1 + Ψm2) +
        (Ψm1 + Ψm2) * (Ψm1 + Ψm2) := by
      simp only [anticomm, sub_mul, mul_sub, add_mul, mul_add]; abel
    rw [hExp, hTot_p, hTot_m, hTot_V, zero_sub, add_zero]
  · have hExp : (Ψp1 + Ψp2) * (Ψm1 + Ψm2) - (Ψm1 - Ψm2) * (Ψp1 - Ψp2) =
        comm Ψp1 Ψm1 + anticomm Ψp1 Ψm2 + anticomm Ψm1 Ψp2 + comm Ψp2 Ψm2 := by
      simp only [comm, anticomm, add_mul, mul_add, sub_mul, mul_sub]; abel
    rw [hExp, hApm, hAmp, hSig2, add_zero, add_zero]
    rfl

/-! ### Master Theorem D₈₁: Complete Synthesis of Archetypes SW₁ → SW₁₀ -/

/-- **Master Theorem D₈₁ (Living Sylvester Clock–Shift Algebra, DeWitt–Schur 4-Block LDU Factorization,
Bergman Unipotent Conjugations & Multi-Site Jordan–Wigner Clifford Chains):**
Unifies all 10 archetypes (`SW₁ → SW₁₀`) and `stageD81Operator` in native Mathlib4 with zero `sorry`s. -/
theorem stage_D81_sylvester_wigner_dewitt_complete_spine_master_synthesis
    {P : B} (hP : P * P = P) (A C M E Np2 Nm2 : B)
    (hPE : comm P E = 0)
    (hNpE : comm (conePlus P A) E = 0)
    (hNmE : comm (coneMinus P C) E = 0)
    (hNp2 : Np2 * Np2 = 0) (hNm2 : Nm2 * Nm2 = 0)
    (hCommP_p : comm P Np2 = 0) (hCommP_m : comm P Nm2 = 0)
    (hComm12_pp : comm (conePlus P A) Np2 = 0)
    (hComm12_pm : comm (conePlus P A) Nm2 = 0)
    (hComm12_mp : comm (coneMinus P C) Np2 = 0)
    (hComm12_mm : comm (coneMinus P C) Nm2 = 0) :
    stageD81Operator P A C M E Np2 Nm2 .SW1_livingSylvesterClockShift = sylClock P A C ∧
    stageD81Operator P A C M E Np2 Nm2 .SW2_dewittSchurBlockLDU =
      P + genPhi P A C + peirce00 P M ∧
    stageD81Operator P A C M E Np2 Nm2 .SW3_dewittUnipotentStripping =
      dewittSchur00 P A C M ∧
    stageD81Operator P A C M E Np2 Nm2 .SW4_internalJordanWignerStringTwist =
      genJ P A C ∧
    stageD81Operator P A C M E Np2 Nm2 .SW5_multisiteJordanWignerTensorChain =
      genV P A C + anticomm Np2 Nm2 ∧
    stageD81Operator P A C M E Np2 Nm2 .SW6_dewittBergmanUnipotentConjugations =
      1 - genV P A C ∧
    stageD81Operator P A C M E Np2 Nm2 .SW7_fullFourBlockWeightedDeWittSchurLDU =
      peirce11 P M + peirce11 P M * conePlus P A +
      coneMinus P C * peirce11 P M + peirce00 P M ∧
    stageD81Operator P A C M E Np2 Nm2 .SW8_singleSiteCliffordExtension =
      genV P A C + E * E ∧
    stageD81Operator P A C M E Np2 Nm2 .SW9_completeCl22JordanWignerQuartet =
      genV P A C + anticomm Np2 Nm2 ∧
    stageD81Operator P A C M E Np2 Nm2 .SW10_compositeSylvesterClockAdditivity =
      genSig P A C + comm Np2 Nm2 := by
  dsimp only [stageD81Operator]
  rcases archetype_SW1_living_sylvester_clock_shift_algebra hP A C with
    ⟨_, _, _, h1, _, _, _, _, _, _, _, _, _⟩
  rcases archetype_SW2_dewitt_schur_block_ldu_decomposition hP A C M with
    ⟨h2, _, _, _, _, _⟩
  rcases archetype_SW3_dewitt_unipotent_stripping_and_block_diagonalization hP A C M with
    ⟨_, _, _, _, h3, _, _, _, _, _⟩
  rcases archetype_SW4_internal_jordan_wigner_string_twist hP A C M M with
    ⟨_, _, _, h4, _, _, _, _, _, _, _⟩
  rcases archetype_SW5_multisite_jordan_wigner_tensor_chain
    hP A C Np2 Nm2 hNp2 hNm2 hCommP_p hCommP_m
    hComm12_pp hComm12_pm hComm12_mp hComm12_mm with
    ⟨_, _, _, _, _, _, _, _, h5⟩
  rcases archetype_SW6_dewitt_bergman_unipotent_conjugations hP A C with
    ⟨_, _, h6, _, _, _, _, _⟩
  rcases archetype_SW7_full_four_block_weighted_dewitt_schur_ldu hP A C M with
    ⟨h7, _⟩
  rcases archetype_SW8_single_site_clifford_extension hP A C E hPE hNpE hNmE with
    ⟨_, _, _, _, _, h8, _⟩
  rcases archetype_SW9_SW10_complete_cl22_quartet_and_sylvester_clock_additivity
    hP A C Np2 Nm2 hNp2 hNm2 hCommP_p hCommP_m
    hComm12_pp hComm12_pm hComm12_mp hComm12_mm with
    ⟨_, _, _, _, _, h9, _, h10⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.SylvesterWignerDeWittCompleteSpine
