/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import Mathlib.Algebra.Star.Basic

/-!
# KMS operator midline, monodromy, logistic pair, and edge transitions

This file gives a ring-level companion to the real-coordinate KMS strip owner.
It proves affine midline correspondence, Peirce parity period two, algebraic
complementarity and variance for a self-adjoint Peirce pair, and twisted edge
composition. A bare star ring has no positivity order, so the logistic result
is an algebraic partition identity and not an assertion of strict positivity.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B]

/-! ## Causal stage order -/

inductive KMSOperatorStage
  | centeredMidline
  | parityMonodromy
  | logisticPartition
  | twistedEdgeComposition
  | unipotentEdgeClosure
  deriving DecidableEq, Repr

/-- Rank records the dependency order of the five operator constructions. -/
def kmsOperatorStageRank : KMSOperatorStage → ℕ
  | .centeredMidline => 0
  | .parityMonodromy => 1
  | .logisticPartition => 2
  | .twistedEdgeComposition => 3
  | .unipotentEdgeClosure => 4

theorem kmsOperatorStageRank_injective : Function.Injective kmsOperatorStageRank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : PartialOrder KMSOperatorStage :=
  PartialOrder.lift kmsOperatorStageRank kmsOperatorStageRank_injective

theorem kmsOperatorStage_causal_chain :
    KMSOperatorStage.centeredMidline < KMSOperatorStage.parityMonodromy ∧
    KMSOperatorStage.parityMonodromy < KMSOperatorStage.logisticPartition ∧
    KMSOperatorStage.logisticPartition < KMSOperatorStage.twistedEdgeComposition ∧
    KMSOperatorStage.twistedEdgeComposition < KMSOperatorStage.unipotentEdgeClosure := by
  change kmsOperatorStageRank .centeredMidline < kmsOperatorStageRank .parityMonodromy ∧
    kmsOperatorStageRank .parityMonodromy < kmsOperatorStageRank .logisticPartition ∧
    kmsOperatorStageRank .logisticPartition < kmsOperatorStageRank .twistedEdgeComposition ∧
    kmsOperatorStageRank .twistedEdgeComposition < kmsOperatorStageRank .unipotentEdgeClosure
  norm_num [kmsOperatorStageRank]

/-! ## L₁: centered coordinates and the fixed seam -/

/-- Translate a KMS operator to the affine chart centered at the idempotent. -/
def kmsToCentered (P S : B) : B := S - P

/-- Translate a centered operator back to the KMS affine chart. -/
def centeredToKms (P X : B) : B := P + X

/-- Krein reflection of the centered coordinate, expressed using the native
Peirce parity automorphism and the star operation. -/
def kmsKreinReflect (P S : B) : B :=
  P + parityConj P (star (kmsToCentered P S))

/-- The two affine coordinate maps are inverse ring translations, and fixed
points of the reflected KMS chart are exactly fixed points of centered Krein
reflection. -/
theorem kms_centered_midline_equivalence (P S X : B) :
    kmsToCentered P (centeredToKms P X) = X ∧
    centeredToKms P (kmsToCentered P S) = S ∧
    (kmsKreinReflect P S = S ↔
      parityConj P (star (kmsToCentered P S)) = kmsToCentered P S) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold kmsToCentered centeredToKms
    exact add_sub_cancel_left P X
  · unfold centeredToKms kmsToCentered
    abel
  · unfold kmsKreinReflect kmsToCentered
    constructor
    · intro h
      have hAffine : P + (S - P) = S := by abel
      have h' := congrArg (fun Z : B => Z - P) h
      simpa only [add_sub_cancel_left] using h'
    · intro h
      rw [h]
      abel

/-! ## L₂: finite winding under the parity automorphism -/

/-- Iteration of the native inner Peirce parity automorphism. -/
def kmsMonodromyIter (P : B) : ℕ → B → B
  | 0, X => X
  | n + 1, X => parityConj P (kmsMonodromyIter P n X)

omit [StarRing B] in
theorem kmsMonodromy_period_two_and_multiplicative
    {P : B} (hP : P * P = P) (n : ℕ) (X Y : B) :
    kmsMonodromyIter P (n + 2) X = kmsMonodromyIter P n X ∧
    kmsMonodromyIter P n (X * Y) =
      kmsMonodromyIter P n X * kmsMonodromyIter P n Y := by
  have hInv : ∀ Z : B, parityConj P (parityConj P Z) = Z :=
    fun Z => (parityConj_involutive_ring_action hP Z 1).1
  have hMult : ∀ U V : B,
      parityConj P (U * V) = parityConj P U * parityConj P V := by
    intro U V
    exact (parityConj_involutive_ring_action hP U V).2.1
  constructor
  · induction n with
    | zero => exact hInv X
    | succ n ih =>
        change parityConj P (kmsMonodromyIter P (n + 2) X) =
          parityConj P (kmsMonodromyIter P n X)
        rw [ih]
  · induction n with
    | zero => rfl
    | succ n ih =>
        change parityConj P (kmsMonodromyIter P n (X * Y)) =
          parityConj P (kmsMonodromyIter P n X) *
            parityConj P (kmsMonodromyIter P n Y)
        rw [ih]
        exact hMult _ _

omit [StarRing B] in
theorem kmsMonodromy_even_odd_sheets {P : B} (hP : P * P = P)
    (k : ℕ) (X : B) :
    kmsMonodromyIter P (2 * k) X = X ∧
    kmsMonodromyIter P (2 * k + 1) X = parityConj P X := by
  have hTwoStep (n : ℕ) :
      kmsMonodromyIter P (n + 2) X = kmsMonodromyIter P n X :=
    (kmsMonodromy_period_two_and_multiplicative hP n X 1).1
  have hEven : ∀ k : ℕ, kmsMonodromyIter P (2 * k) X = X := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Nat.mul_succ, hTwoStep (2 * k), ih]
  constructor
  · exact hEven k
  · calc
      kmsMonodromyIter P (2 * k + 1) X =
          parityConj P (kmsMonodromyIter P (2 * k) X) := by
            simp only [kmsMonodromyIter]
      _ = parityConj P X := congrArg (parityConj P) (hEven k)

/-! ## L₃: complementary logistic operators -/

/-- The first Peirce-supported member of the complementary operator pair. -/
def peirceLogisticPlus (P A C : B) : B :=
  P * (1 - qgtPlus P A C) + (1 - P) * qgtMinus P A C

/-- The second Peirce-supported member of the complementary operator pair. -/
def peirceLogisticMinus (P A C : B) : B :=
  (1 - P) * (1 - qgtMinus P A C) + P * qgtPlus P A C

/-- The pair partitions the unit and its ordered products are both the
idempotency-defect complement `V - V²`. For self-adjoint paired inputs both
members are self-adjoint. -/
theorem peirceLogistic_pair_properties
    {P : B} (hP : P * P = P) (hPs : star P = P) (A C : B) :
    peirceLogisticPlus P A C + peirceLogisticMinus P A C = 1 ∧
    1 - peirceLogisticPlus P A C = peirceLogisticMinus P A C ∧
    peirceLogisticPlus P A C * peirceLogisticMinus P A C =
      -(genV P A C * genV P A C - genV P A C) ∧
    peirceLogisticMinus P A C * peirceLogisticPlus P A C =
      -(genV P A C * genV P A C - genV P A C) ∧
    star (peirceLogisticPlus P A (star A)) = peirceLogisticPlus P A (star A) ∧
    star (peirceLogisticMinus P A (star A)) = peirceLogisticMinus P A (star A) := by
  have hStarN : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPs, mul_assoc]
  have hStarNm : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hStarN, star_star]
  have hStarQp : star (qgtPlus P A (star A)) = qgtPlus P A (star A) := by
    unfold qgtPlus
    rw [star_mul, hStarN, hStarNm]
  have hStarQm : star (qgtMinus P A (star A)) = qgtMinus P A (star A) := by
    unfold qgtMinus
    rw [star_mul, hStarN, hStarNm]
  have hLogPlus : peirceLogisticPlus P A (star A) =
      P - qgtPlus P A (star A) + qgtMinus P A (star A) := by
    unfold peirceLogisticPlus qgtPlus qgtMinus
    peirce_nf hP
  have hLogMinus : peirceLogisticMinus P A (star A) =
      (1 - P) - qgtMinus P A (star A) + qgtPlus P A (star A) := by
    unfold peirceLogisticMinus qgtPlus qgtMinus
    peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold peirceLogisticPlus peirceLogisticMinus qgtPlus qgtMinus
    peirce_nf hP
  · unfold peirceLogisticPlus peirceLogisticMinus qgtPlus qgtMinus
    peirce_nf hP
  · unfold peirceLogisticPlus peirceLogisticMinus qgtPlus qgtMinus genV anticomm
    peirce_nf hP
  · unfold peirceLogisticPlus peirceLogisticMinus qgtPlus qgtMinus genV anticomm
    peirce_nf hP
  · calc
      star (peirceLogisticPlus P A (star A)) = star
          (P - qgtPlus P A (star A) + qgtMinus P A (star A)) :=
            congrArg star hLogPlus
      _ = P - qgtPlus P A (star A) + qgtMinus P A (star A) := by
        rw [star_add, star_sub, hPs, hStarQp, hStarQm]
      _ = peirceLogisticPlus P A (star A) := hLogPlus.symm
  · calc
      star (peirceLogisticMinus P A (star A)) = star
          ((1 - P) - qgtMinus P A (star A) + qgtPlus P A (star A)) :=
            congrArg star hLogMinus
      _ = (1 - P) - qgtMinus P A (star A) + qgtPlus P A (star A) := by
        rw [star_add, star_sub, star_sub, star_one, hPs, hStarQp, hStarQm]
      _ = peirceLogisticMinus P A (star A) := hLogMinus.symm

/-! ## L₄–L₅: twisted edge cocycle and unipotent two-crossing closure -/

/-- Apply the parity automorphism, then conjugate by an edge operator. -/
def peirceEdgeTransition (P G GInv X : B) : B :=
  G * parityConj P X * GInv

omit [StarRing B] in
theorem peirceEdgeTransition_comp {P : B} (hP : P * P = P)
    (G₁ G₁Inv G₂ G₂Inv X : B) :
    peirceEdgeTransition P G₂ G₂Inv
      (peirceEdgeTransition P G₁ G₁Inv X) =
    (G₂ * parityConj P G₁) * X * (parityConj P G₁Inv * G₂Inv) := by
  have hAutoMul (U V : B) :
      parityConj P (U * V) = parityConj P U * parityConj P V :=
    (parityConj_involutive_ring_action hP U V).2.1
  have hAutoInv (U : B) : parityConj P (parityConj P U) = U :=
    (parityConj_involutive_ring_action hP U 1).1
  unfold peirceEdgeTransition
  calc
    G₂ * parityConj P (G₁ * parityConj P X * G₁Inv) * G₂Inv =
        G₂ * (parityConj P G₁ * parityConj P (parityConj P X) *
          parityConj P G₁Inv) * G₂Inv := by
            rw [hAutoMul, hAutoMul]
    _ = (G₂ * parityConj P G₁) * X *
        (parityConj P G₁Inv * G₂Inv) := by
          rw [hAutoInv]
          noncomm_ring

omit [StarRing B] in
theorem peirceEdgeTransition_upper_two_step {P : B} (hP : P * P = P)
    (A X : B) :
    peirceEdgeTransition P (1 + conePlus P A) (1 - conePlus P A)
      (peirceEdgeTransition P (1 + conePlus P A) (1 - conePlus P A) X) = X := by
  have hLeft : (1 + conePlus P A) * parityConj P (1 + conePlus P A) = 1 := by
    unfold parityConj invS conePlus
    peirce_nf hP
  have hRight : parityConj P (1 - conePlus P A) *
      (1 - conePlus P A) = 1 := by
    unfold parityConj invS conePlus
    peirce_nf hP
  rw [peirceEdgeTransition_comp hP, hLeft, hRight, one_mul, mul_one]

end InfoGeometry.OperatorAlgebra.PeirceSpine
