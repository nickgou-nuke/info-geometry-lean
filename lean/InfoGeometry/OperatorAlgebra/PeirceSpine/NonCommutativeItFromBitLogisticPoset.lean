/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Order.Hom.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeOperatorTimePoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.KMSOperatorMonodromy
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceTetradPoset

/-!
# Stage D₃₇ (Archetypes I₁ → I₅): Logistic Variance, Nilpotent–Idempotent Peirce Split, Orthogonal Defect Additivity, and Five-Way Full-Circle Defect Closure (`D₃₇ → D₁`)

1. **Archetype I₁ (`I1_logisticBitVarianceDefect`)**:
   The non-commutative logistic variance `logisticBitVariance P A C = logisticBitPlus P A C * logisticBitMinus P A C`
   equals `-idemDefect (logisticBitPlus P A C) = -idemDefect (genV P A C)`.
2. **Archetype I₂ (`I2_nilpotentIdempotentPeirceSplit`)**:
   The nilpotent–idempotent Peirce decomposition of `P`: `idemDefect P = 0`, `idemDefect (1 - P) = 0`,
   `conePlus P A * conePlus P A = 0`, `coneMinus P C * coneMinus P C = 0`, `idemDefect (P - conePlus P A) = 0`,
   `idemDefect (P + coneMinus P C) = 0`, `idemDefect (P + genPhi P A C) = genV P A C`, and
   `idemDefect (P + genJ P A C) = -genV P A C`.
3. **Archetype I₃ (`I3_onShellIdempotentCrystallization`)**:
   Equivalence between idempotency of `logisticBitPlus P A C`, vanishing of `logisticBitVariance P A C`,
   and vanishing of `idemDefect (genV P A C)`.
4. **Archetype I₄ (`I4_orthogonalChannelDefectAdditivity`)**:
   Additivity of `idemDefect` across mutually orthogonal elements (`V₁ * V₂ = 0 → V₂ * V₁ = 0 → idemDefect (V₁ + V₂) = idemDefect V₁ + idemDefect V₂`)
   and integer corner-flux pairing `bitCounterOp P C (unipotentCornerOp k P A) (unipotentCornerOpInv k P A) = k • genV P A C`.
5. **Archetype I₅ (`I5_fiveWayFullCircleDefectClosure`)**:
   Five-way algebraic coincidence equating `-logisticBitVariance P A C`, `idemDefect (logisticBitPlus P A C)`,
   `-(cohomologyProj P A C * genV P A C)`, `zornNorm P (genV P A C + genPhi P A C)`, and
   `idemDefectBar (genPhi P A C) * idemDefect (genPhi P A C)` with `idemDefect (genV P A C)`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeItFromBitLogisticPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeOperatorTimePoset

variable {B : Type*} [Ring B]

/-! ### Causal Poset of Stage D₃₇ Archetypes (I₁ → I₅) -/

/-- The 5-stage causal poset of non-commutative logistic variance, nilpotent–idempotent Peirce
split, idempotent crystallization, orthogonal defect additivity, and five-way full-circle
defect closure archetypes (`I₁ → I₅`). -/
inductive StageD37Archetype
  | I1_logisticBitVarianceDefect
  | I2_nilpotentIdempotentPeirceSplit
  | I3_onShellIdempotentCrystallization
  | I4_orthogonalChannelDefectAdditivity
  | I5_fiveWayFullCircleDefectClosure
  deriving DecidableEq, Repr

instance instInhabitedStageD37Archetype : Inhabited StageD37Archetype :=
  ⟨.I1_logisticBitVarianceDefect⟩

/-- Topological rank in the 5-stage causal poset. -/
def stageD37Rank : StageD37Archetype → ℕ
  | .I1_logisticBitVarianceDefect => 0
  | .I2_nilpotentIdempotentPeirceSplit => 1
  | .I3_onShellIdempotentCrystallization => 2
  | .I4_orthogonalChannelDefectAdditivity => 3
  | .I5_fiveWayFullCircleDefectClosure => 4

theorem stageD37Rank_injective : Function.Injective stageD37Rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance instPartialOrderStageD37Archetype : PartialOrder StageD37Archetype :=
  PartialOrder.lift stageD37Rank stageD37Rank_injective

theorem stageD37_strict_causal_chain :
    StageD37Archetype.I1_logisticBitVarianceDefect < .I2_nilpotentIdempotentPeirceSplit ∧
    StageD37Archetype.I2_nilpotentIdempotentPeirceSplit < .I3_onShellIdempotentCrystallization ∧
    StageD37Archetype.I3_onShellIdempotentCrystallization < .I4_orthogonalChannelDefectAdditivity ∧
    StageD37Archetype.I4_orthogonalChannelDefectAdditivity < .I5_fiveWayFullCircleDefectClosure := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Stage 0: Core Operator Primitives for Archetypes I₁ → I₅ -/

/-- Dual idempotency defect polynomial `X² + X`. -/
def idemDefectBar (X : B) : B := X * X + X

abbrev logisticBitPlus (P A C : B) : B := peirceLogisticPlus P A C

/-- Complementary logistic operator `(1 - P) * (1 - Q₋) + P * Q₊` (re-exported from Stage D₃₅). -/
abbrev logisticBitMinus (P A C : B) : B := peirceLogisticMinus P A C

/-- Non-commutative logistic variance `logisticBitPlus P A C * logisticBitMinus P A C`. -/
def logisticBitVariance (P A C : B) : B :=
  logisticBitPlus P A C * logisticBitMinus P A C

/-- Complementary projector `1 - V(A, C)`. -/
def cohomologyProj (P A C : B) : B :=
  1 - genV P A C

/-- Corner anticommutator pairing `{U⁻¹ [P, U], N₋(C)}`. -/
def bitCounterOp (P C U U_inv : B) : B :=
  anticomm (U_inv * comm P U) (coneMinus P C)

/-- Constructor-indexed operator realization mapping each `StageD37Archetype` stage to its
canonical operator in `[Ring B]`. -/
def stageD37Operator (k : ℤ) (P A C : B) : StageD37Archetype → B
  | .I1_logisticBitVarianceDefect => logisticBitVariance P A C
  | .I2_nilpotentIdempotentPeirceSplit => idemDefect (P + genPhi P A C)
  | .I3_onShellIdempotentCrystallization => idemDefect (logisticBitPlus P A C)
  | .I4_orthogonalChannelDefectAdditivity =>
      bitCounterOp P C (unipotentCornerOp k P A) (unipotentCornerOpInv k P A)
  | .I5_fiveWayFullCircleDefectClosure => zornNorm P (genV P A C + genPhi P A C)

macro "bit_abel" hP:ident : tactic =>
  `(tactic| (
    simp only [bitCounterOp, unipotentCornerOp, unipotentCornerOpInv,
               unipotentCornerOp, unipotentCornerOpInv,
               cohomologyProj, logisticBitVariance, logisticBitPlus, logisticBitMinus,
               peirceLogisticPlus, peirceLogisticMinus,
               zornNorm, zornConj,
               genPhi, genJ, genV, genSig, qgtPlus, qgtMinus,
               conePlus, coneMinus, invS, comm, anticomm,
               NonCommutativeOperatorTimePoset.idemDefect, idemDefectBar,
               smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg,
               smul_smul, smul_zero, zero_smul, add_smul, sub_smul,
               zsmul_add, zsmul_sub, neg_zsmul, two_zsmul,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               sub_self, mul_zero, zero_mul, add_zero, zero_add, neg_zero,
               mul_assoc, $hP:ident,
               NonCommutativeOperatorTimePoset.P_assoc $hP:ident]
    try abel))

/-! ### Individual Theorems for Archetypes I₁ → I₅ -/

/-- For every element of an associative ring, the Bernoulli product is the
negative of its idempotency defect. -/
theorem one_sub_mul_eq_neg_idemDefect (X : B) :
    X * (1 - X) = -NonCommutativeOperatorTimePoset.idemDefect X := by
  unfold NonCommutativeOperatorTimePoset.idemDefect
  simp only [mul_sub, mul_one, neg_sub]

/-- **Theorem I₁.1 (Logistic Bit Variance Equals Minus the Idempotency Defect):**
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. `logisticBitPlus P A C + logisticBitMinus P A C = 1`;
2. `idemDefect (logisticBitPlus P A C) = idemDefect (genV P A C)` and
   `idemDefect (logisticBitMinus P A C) = idemDefect (genV P A C)`;
3. `logisticBitVariance P A C = -idemDefect (genV P A C)`. -/
theorem logistic_bit_variance_and_defect_equivalence {P : B} (hP : P * P = P) (A C : B) :
    logisticBitPlus P A C + logisticBitMinus P A C = 1 ∧
    NonCommutativeOperatorTimePoset.idemDefect (logisticBitPlus P A C) =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    NonCommutativeOperatorTimePoset.idemDefect (logisticBitMinus P A C) =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    logisticBitVariance P A C =
      -NonCommutativeOperatorTimePoset.idemDefect (genV P A C) := by
  refine ⟨by bit_abel hP,
          by bit_abel hP,
          by bit_abel hP,
          by bit_abel hP⟩

/-- **Theorem I₁.2 (Order Independence of the Logistic Variance):**
The two complementary Peirce logistic operators commute, so reversing the
ordered variance product does not change it. Both orders equal the negative
idempotency defect of the bulk operator. This holds in every associative ring;
no star structure or commutativity of the ambient ring is required. -/
theorem logistic_bit_variance_order_independence
    {P : B} (hP : P * P = P) (A C : B) :
    logisticBitMinus P A C * logisticBitPlus P A C =
      -NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    comm (logisticBitPlus P A C) (logisticBitMinus P A C) = 0 ∧
    logisticBitVariance P A C =
      logisticBitMinus P A C * logisticBitPlus P A C := by
  refine ⟨by bit_abel hP, by bit_abel hP, by bit_abel hP⟩

/-- **Theorem I₂.1 (Nilpotent–Idempotent Peirce Split of `P`, `P - N₊`, `P + Φ`, and `P + J`):**
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. `idemDefect P = 0` and `idemDefect (1 - P) = 0`;
2. `conePlus P A * conePlus P A = 0`, `coneMinus P C * coneMinus P C = 0`,
   `idemDefect (P - conePlus P A) = 0`, and `idemDefect (P + coneMinus P C) = 0`;
3. `idemDefect (P + genPhi P A C) = genV P A C`, `idemDefect (P + genJ P A C) = -genV P A C`,
   and `idemDefect (P + genPhi P A C) - idemDefect (P + genJ P A C) = (2 : ℤ) • genV P A C`. -/
theorem nilpotent_idempotent_it_from_bit_split {P : B} (hP : P * P = P) (A C : B) :
    NonCommutativeOperatorTimePoset.idemDefect P = 0 ∧
    NonCommutativeOperatorTimePoset.idemDefect (1 - P) = 0 ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    NonCommutativeOperatorTimePoset.idemDefect (P - conePlus P A) = 0 ∧
    NonCommutativeOperatorTimePoset.idemDefect (P + coneMinus P C) = 0 ∧
    NonCommutativeOperatorTimePoset.idemDefect (P + genPhi P A C) = genV P A C ∧
    NonCommutativeOperatorTimePoset.idemDefect (P + genJ P A C) = -genV P A C ∧
    NonCommutativeOperatorTimePoset.idemDefect (P + genPhi P A C) -
      NonCommutativeOperatorTimePoset.idemDefect (P + genJ P A C) =
      (2 : ℤ) • genV P A C := by
  refine ⟨by bit_abel hP, by bit_abel hP, by bit_abel hP, by bit_abel hP,
          by bit_abel hP, by bit_abel hP, by bit_abel hP, by bit_abel hP, by bit_abel hP⟩

/-- **Theorem I₃.1 (On-Shell Idempotent Crystallization Equivalence):**
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. `logisticBitPlus P A C * logisticBitPlus P A C = logisticBitPlus P A C ↔ idemDefect (genV P A C) = 0`;
2. `logisticBitVariance P A C = 0 ↔ idemDefect (genV P A C) = 0`. -/
theorem bit_crystallization_iff_zero_logistic_variance {P : B} (hP : P * P = P) (A C : B) :
    (logisticBitPlus P A C * logisticBitPlus P A C = logisticBitPlus P A C ↔
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) = 0) ∧
    (logisticBitVariance P A C = 0 ↔
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) = 0) := by
  rcases logistic_bit_variance_and_defect_equivalence hP A C with
    ⟨_, hDefPlus, _, hVar⟩
  constructor
  · rw [← sub_eq_zero]
    change NonCommutativeOperatorTimePoset.idemDefect (logisticBitPlus P A C) = 0 ↔
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) = 0
    rw [hDefPlus]
  · rw [hVar, neg_eq_zero]

/-- **Theorem I₃.2 (Full Logistic Crystallization Chain):**
The logistic bit is idempotent exactly when its ordered variance product vanishes,
and that is exactly when the bulk operator has zero idempotency defect.  The order
`L₊ * L₋` is retained throughout; no commutation hypothesis is used. -/
theorem logistic_bit_crystallization_full_equivalence
    {P : B} (hP : P * P = P) (A C : B) :
    (logisticBitPlus P A C * logisticBitPlus P A C = logisticBitPlus P A C ↔
      logisticBitVariance P A C = 0) ∧
    (logisticBitVariance P A C = 0 ↔
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) = 0) := by
  rcases bit_crystallization_iff_zero_logistic_variance hP A C with ⟨hIdem, hVariance⟩
  exact ⟨hIdem.trans hVariance.symm, hVariance⟩

/-- Idempotency defect is additive on a pair of mutually annihilating
noncommutative channels. No idempotency or commutativity assumptions on the
channels are required. -/
theorem orthogonal_idempotency_defect_additivity
    {V₁ V₂ : B} (h12 : V₁ * V₂ = 0) (h21 : V₂ * V₁ = 0) :
    NonCommutativeOperatorTimePoset.idemDefect (V₁ + V₂) =
      NonCommutativeOperatorTimePoset.idemDefect V₁ +
        NonCommutativeOperatorTimePoset.idemDefect V₂ := by
  unfold NonCommutativeOperatorTimePoset.idemDefect
  rw [add_mul, mul_add, mul_add, h12, h21, add_zero, zero_add]
  abel

/-- The idempotency defect of a finite sum of pairwise two-sided
annihilating channels is the sum of the individual defects. This is the
finite-family extension of the two-channel D₃₇ law; no idempotency or
commutativity assumptions are imposed on the summands. -/
theorem orthogonal_idempotency_defect_sum
    {ι : Type*} (s : Finset ι) (f : ι → B)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      f i * f j = 0 ∧ f j * f i = 0) :
    NonCommutativeOperatorTimePoset.idemDefect (∑ i ∈ s, f i) =
      ∑ i ∈ s, NonCommutativeOperatorTimePoset.idemDefect (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [NonCommutativeOperatorTimePoset.idemDefect]
  | @insert a s ha ih =>
      have hsum : (∑ i ∈ insert a s, f i) = f a + ∑ i ∈ s, f i := by
        simp [ha]
      have hleft : f a * (∑ i ∈ s, f i) = 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro i hi
        exact (horth a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi)
          (by intro heq; exact ha (heq ▸ hi))).1
      have hright : (∑ i ∈ s, f i) * f a = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro i hi
        exact (horth i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self a s)
          (by intro heq; exact ha (heq.symm ▸ hi))).1
      rw [hsum, orthogonal_idempotency_defect_additivity hleft hright,
        Finset.sum_insert ha, ih (by
          intro i hi j hj hij
          exact horth i (Finset.mem_insert_of_mem hi) j
            (Finset.mem_insert_of_mem hj) hij)]

/-- **Theorem I₄.1 (Orthogonal Multi-Channel Defect Additivity & Integer Corner-Flux Counter):**
For any idempotent `P` (`P * P = P`), any orthogonal `V₁, V₂ : B` (`V₁ * V₂ = 0`, `V₂ * V₁ = 0`),
any `A, C : B`, and any `k : ℤ`:
1. `idemDefect (V₁ + V₂) = idemDefect V₁ + idemDefect V₂`;
2. `bitCounterOp P C (unipotentCornerOp k P A) (unipotentCornerOpInv k P A) = k • genV P A C`. -/
theorem multi_channel_bit_counting_and_additivity
    {P V₁ V₂ : B} (hP : P * P = P) (h12 : V₁ * V₂ = 0) (h21 : V₂ * V₁ = 0)
    (A C : B) (k : ℤ) :
    NonCommutativeOperatorTimePoset.idemDefect (V₁ + V₂) =
      NonCommutativeOperatorTimePoset.idemDefect V₁ +
        NonCommutativeOperatorTimePoset.idemDefect V₂ ∧
    bitCounterOp P C (unipotentCornerOp k P A) (unipotentCornerOpInv k P A) =
      k • genV P A C := by
  constructor
  · exact orthogonal_idempotency_defect_additivity h12 h21
  · bit_abel hP

/-- **Theorem I₅.1 (The Five-Way Full-Circle Unification Identity Across Stages `D₁ → D₃₇`):**
For any idempotent `P` (`P * P = P`) and any `A, C : B`, all five invariants coincide with
`idemDefect (genV P A C)`:
1. `-logisticBitVariance P A C = idemDefect (genV P A C)`;
2. `idemDefect (logisticBitPlus P A C) = idemDefect (genV P A C)`;
3. `-(cohomologyProj P A C * genV P A C) = idemDefect (genV P A C)`;
4. `zornNorm P (genV P A C + genPhi P A C) = idemDefect (genV P A C)`;
5. `idemDefectBar (genPhi P A C) * idemDefect (genPhi P A C) = idemDefect (genV P A C)`. -/
theorem five_way_full_circle_unification_identity {P : B} (hP : P * P = P) (A C : B) :
    -logisticBitVariance P A C =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    NonCommutativeOperatorTimePoset.idemDefect (logisticBitPlus P A C) =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    -(cohomologyProj P A C * genV P A C) =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    zornNorm P (genV P A C + genPhi P A C) =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    idemDefectBar (genPhi P A C) *
      NonCommutativeOperatorTimePoset.idemDefect (genPhi P A C) =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) := by
  refine ⟨by bit_abel hP, by bit_abel hP, by bit_abel hP, by bit_abel hP, by bit_abel hP⟩

/-! ### Master Theorem D₃₇: Complete Full-Circle Synthesis of Archetypes I₁ → I₅ -/

/-- **Master Theorem D₃₇ (Non-Commutative Logistic Variance, Nilpotent–Idempotent Peirce Split,
On-Shell Idempotent Crystallization, Orthogonal Defect Additivity & Five-Way Full-Circle Closure `D₃₇ → D₁`):**
Unifies all five archetypes (`I₁ → I₅`) and their operator realization. -/
theorem stage_D37_it_from_bit_logistic_variance_and_full_circle_master_synthesis
    {P V₁ V₂ A C : B} (hP : P * P = P) (h12 : V₁ * V₂ = 0) (h21 : V₂ * V₁ = 0) (k : ℤ) :
    logisticBitPlus P A C + logisticBitMinus P A C = 1 ∧
    stageD37Operator k P A C .I1_logisticBitVarianceDefect =
      -NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    NonCommutativeOperatorTimePoset.idemDefect (P - conePlus P A) = 0 ∧
    stageD37Operator k P A C .I2_nilpotentIdempotentPeirceSplit = genV P A C ∧
    NonCommutativeOperatorTimePoset.idemDefect (P + genJ P A C) = -genV P A C ∧
    (logisticBitPlus P A C * logisticBitPlus P A C = logisticBitPlus P A C ↔
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) = 0) ∧
    NonCommutativeOperatorTimePoset.idemDefect (V₁ + V₂) =
      NonCommutativeOperatorTimePoset.idemDefect V₁ +
        NonCommutativeOperatorTimePoset.idemDefect V₂ ∧
    stageD37Operator k P A C .I4_orthogonalChannelDefectAdditivity = k • genV P A C ∧
    stageD37Operator k P A C .I3_onShellIdempotentCrystallization =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    -(cohomologyProj P A C * genV P A C) =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    stageD37Operator k P A C .I5_fiveWayFullCircleDefectClosure =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    idemDefectBar (genPhi P A C) *
      NonCommutativeOperatorTimePoset.idemDefect (genPhi P A C) =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) := by
  dsimp only [stageD37Operator]
  rcases logistic_bit_variance_and_defect_equivalence hP A C with
    ⟨hL2, _, _, hL5⟩
  rcases nilpotent_idempotent_it_from_bit_split hP A C with
    ⟨_, _, _, _, hS5, _, hS7, hS8, _⟩
  rcases bit_crystallization_iff_zero_logistic_variance hP A C with ⟨hC1, _⟩
  rcases multi_channel_bit_counting_and_additivity hP h12 h21 A C k with ⟨hM1, hM2⟩
  rcases five_way_full_circle_unification_identity hP A C with
    ⟨_, hU2, hU3, hU4, hU5⟩
  exact ⟨hL2, hL5, hS5, hS7, hS8, hC1, hM1, hM2, hU2, hU3, hU4, hU5⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeItFromBitLogisticPoset
