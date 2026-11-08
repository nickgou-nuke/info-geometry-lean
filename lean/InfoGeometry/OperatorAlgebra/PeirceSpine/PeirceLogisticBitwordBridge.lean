/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.KMSOperatorMonodromy
import Mathlib.Data.List.Basic

/-!
# D₄₂: Peirce logistic operators, finite bitword cylinders, and additive readout

The Peirce logistic elements remain in the noncommutative ring `B`. An
additive map `ω : B → R` is a separate readout; no multiplicativity,
positivity, trace property, or identification of `B` with `R` is assumed.

`branchCompression` is an algebraic two-corner compression. It is not the
topological Cantor stream quotient already owned by
`InfoGeometry.Canonical.CantorBoundaryReadoutKernelQuotientTopCat`. This file
proves the finite algebraic bridge and makes no claim that an arbitrary
operator-valued cylinder defines a point or measure on that topological
quotient.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ### Dependency order -/

inductive LogisticBitwordStage where
  | operatorReadoutSeparation
  | branchCompression
  | finiteCylinders
  | refinementAndConcatenation
  | varianceAndStateTransport
  deriving DecidableEq, Repr

def logisticBitwordRank : LogisticBitwordStage → ℕ
  | .operatorReadoutSeparation => 0
  | .branchCompression => 1
  | .finiteCylinders => 2
  | .refinementAndConcatenation => 3
  | .varianceAndStateTransport => 4

theorem logisticBitwordRank_strict_chain :
    logisticBitwordRank .operatorReadoutSeparation < logisticBitwordRank .branchCompression ∧
    logisticBitwordRank .branchCompression < logisticBitwordRank .finiteCylinders ∧
    logisticBitwordRank .finiteCylinders < logisticBitwordRank .refinementAndConcatenation ∧
    logisticBitwordRank .refinementAndConcatenation < logisticBitwordRank .varianceAndStateTransport := by
  decide

variable {B : Type*} [Ring B] [StarRing B]

/-! ### Two-branch operator compression -/

/-- Keep the two diagonal Peirce branches of an operator. -/
def branchCompression (P Q X : B) : B := P * X * P + Q * X * Q

/-- The complementary corner after deleting the two orthogonal branches. -/
def branchGap (P Q : B) : B := 1 - P - Q

theorem branchCompression_idempotent
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (X : B) :
    branchCompression P Q (branchCompression P Q X) = branchCompression P Q X := by
  unfold branchCompression
  calc
    P * (P * X * P + Q * X * Q) * P +
        Q * (P * X * P + Q * X * Q) * Q
      = (P * P) * X * (P * P) + (Q * Q) * X * (Q * Q) := by
          simp only [add_mul, mul_add, mul_assoc, hPQ, hQP,
            zero_mul, mul_zero, add_zero, zero_add]
    _ = P * X * P + Q * X * Q := by rw [hP, hQ]

theorem branchGap_annihilates_branches
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    P * branchGap P Q = 0 ∧ branchGap P Q * P = 0 ∧
    Q * branchGap P Q = 0 ∧ branchGap P Q * Q = 0 := by
  unfold branchGap
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [mul_sub, sub_mul, mul_one, one_mul, hP, hQ, hPQ, hQP,
      sub_self, zero_sub, sub_zero]

theorem branchCompression_ignores_gap
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (X Y : B) :
    branchCompression P Q (X + branchGap P Q * Y * branchGap P Q) =
      branchCompression P Q X := by
  rcases branchGap_annihilates_branches hP hQ hPQ hQP with
    ⟨hPg, hgP, hQg, hgQ⟩
  unfold branchCompression
  have hpZero : P * (branchGap P Q * Y * branchGap P Q) * P = 0 := by
    calc
      P * (branchGap P Q * Y * branchGap P Q) * P =
          (P * branchGap P Q) * Y * branchGap P Q * P := by simp only [mul_assoc]
      _ = 0 := by rw [hPg]; simp
  have hqZero : Q * (branchGap P Q * Y * branchGap P Q) * Q = 0 := by
    calc
      Q * (branchGap P Q * Y * branchGap P Q) * Q =
          (Q * branchGap P Q) * Y * branchGap P Q * Q := by simp only [mul_assoc]
      _ = 0 := by rw [hQg]; simp
  calc
    P * (X + branchGap P Q * Y * branchGap P Q) * P +
        Q * (X + branchGap P Q * Y * branchGap P Q) * Q
      = P * X * P + Q * X * Q +
          (P * (branchGap P Q * Y * branchGap P Q) * P +
            Q * (branchGap P Q * Y * branchGap P Q) * Q) := by noncomm_ring
    _ = P * X * P + Q * X * Q := by rw [hpZero, hqZero]; simp

/-- With complementary idempotents, branch compression fixes the logistic
operator. This is the algebraic Peirce-coordinate statement; it is not a
map to the Cantor topological quotient. -/
theorem branchCompression_fixes_logistic
    {P : B} (hP : P * P = P) (A C : B) :
    branchCompression P (1 - P) (peirceLogisticPlus P A C) =
      peirceLogisticPlus P A C := by
  unfold branchCompression peirceLogisticPlus qgtPlus qgtMinus
  peirce_nf hP

/-! ### Finite noncommutative cylinders -/

/-- Select the positive or complementary logistic branch. -/
def operatorBitSelect (b : Bool) (L : B) : B :=
  match b with
  | true => L
  | false => 1 - L

/-- Ordered product cylinder for a finite Boolean word. -/
def operatorBitwordCylinder : List Bool → B → B
  | [], _ => 1
  | b :: w, L => operatorBitSelect b L * operatorBitwordCylinder w L

theorem operatorBitSelect_partition (L : B) :
    operatorBitSelect true L + operatorBitSelect false L = 1 := by
  simp [operatorBitSelect]

theorem operatorBitwordCylinder_refinement (L : B) (w : List Bool) :
    operatorBitwordCylinder (true :: w) L + operatorBitwordCylinder (false :: w) L =
      operatorBitwordCylinder w L := by
  calc
    operatorBitwordCylinder (true :: w) L + operatorBitwordCylinder (false :: w) L
      = (operatorBitSelect true L + operatorBitSelect false L) *
          operatorBitwordCylinder w L := by simp only [operatorBitwordCylinder, ← add_mul]
    _ = operatorBitwordCylinder w L := by rw [operatorBitSelect_partition]; simp

theorem operatorBitwordCylinder_append (L : B) (u v : List Bool) :
    operatorBitwordCylinder (u ++ v) L =
      operatorBitwordCylinder u L * operatorBitwordCylinder v L := by
  induction u with
  | nil => simp [operatorBitwordCylinder]
  | cons b u ih =>
      simp only [List.cons_append, operatorBitwordCylinder, ih, mul_assoc]

/-- The two length-two mixed cylinders are the same polynomial `L(1-L)`;
this equality itself needs no idempotency or commutativity assumption. -/
theorem operatorBitwordCylinder_mixed_pair (L : B) :
    operatorBitwordCylinder [true, false] L = L * (1 - L) ∧
    operatorBitwordCylinder [false, true] L = (1 - L) * L := by
  simp [operatorBitwordCylinder, operatorBitSelect]

/-- On-shell, selectors are complementary orthogonal idempotents. Any word
with an adjacent change of bit therefore has zero cylinder operator. -/
def hasAdjacentBitChange : List Bool → Prop
  | [] => False
  | [_] => False
  | b :: c :: w => b ≠ c ∨ hasAdjacentBitChange (c :: w)

theorem operatorBitwordCylinder_adjacentChange_zero
    {L : B} (hL : L * L = L) :
    ∀ {w : List Bool}, hasAdjacentBitChange w → operatorBitwordCylinder w L = 0 := by
  intro w
  induction w with
  | nil => simp [hasAdjacentBitChange]
  | cons b w ih =>
      cases w with
      | nil => simp [hasAdjacentBitChange]
      | cons c w =>
          have hForward : L * (1 - L) = 0 := by
            rw [mul_sub, mul_one, hL, sub_self]
          have hBackward : (1 - L) * L = 0 := by
            rw [sub_mul, one_mul, hL, sub_self]
          intro h
          rcases h with hbc | htail
          · have hcross : operatorBitSelect b L * operatorBitSelect c L = 0 := by
              cases b <;> cases c <;>
                simp_all [operatorBitSelect, hForward, hBackward]
            change operatorBitSelect b L *
              (operatorBitSelect c L * operatorBitwordCylinder w L) = 0
            rw [← mul_assoc, hcross, zero_mul]
          · change operatorBitSelect b L *
              operatorBitwordCylinder (c :: w) L = 0
            rw [ih htail, mul_zero]

/-! ### Logistic variance and separate additive readout -/

theorem peirceLogistic_operator_identities
    {P : B} (hP : P * P = P) (A C : B) :
    peirceLogisticPlus P A C + peirceLogisticMinus P A C = 1 ∧
    1 - peirceLogisticPlus P A C = peirceLogisticMinus P A C ∧
    peirceLogisticPlus P A C * peirceLogisticMinus P A C =
      -(genV P A C * genV P A C - genV P A C) ∧
    peirceLogisticMinus P A C * peirceLogisticPlus P A C =
      -(genV P A C * genV P A C - genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirceLogisticPlus, peirceLogisticMinus, qgtPlus, qgtMinus,
      genV, anticomm]; peirce_nf hP)

theorem peirceLogistic_mixed_cylinders_are_variance
    {P : B} (hP : P * P = P) (A C : B) :
    operatorBitwordCylinder [true, false] (peirceLogisticPlus P A C) =
      -(genV P A C * genV P A C - genV P A C) ∧
    operatorBitwordCylinder [false, true] (peirceLogisticPlus P A C) =
      -(genV P A C * genV P A C - genV P A C) := by
  rcases peirceLogistic_operator_identities hP A C with ⟨_, hComp, hPlus, hMinus⟩
  rcases operatorBitwordCylinder_mixed_pair (peirceLogisticPlus P A C) with
    ⟨hTF, hFT⟩
  exact ⟨hTF.trans (by rw [hComp]; exact hPlus),
    hFT.trans (by rw [hComp]; exact hMinus)⟩

/-- Additivity and normalization are explicit properties of the readout map;
the operator-valued partition remains a theorem in `B`. -/
theorem peirceLogistic_additive_readout
    {R : Type*} [Ring R] (ω : B → R)
    (hAdd : ∀ X Y : B, ω (X + Y) = ω X + ω Y)
    {P : B} (hP : P * P = P) (A C : B) :
    ω (peirceLogisticPlus P A C) + ω (peirceLogisticMinus P A C) = ω 1 := by
  rw [← hAdd, (peirceLogistic_operator_identities hP A C).1]

theorem peirceLogistic_normalized_readout
    {R : Type*} [Ring R] (ω : B → R)
    (hAdd : ∀ X Y : B, ω (X + Y) = ω X + ω Y)
    (hOne : ω 1 = 1) {P : B} (hP : P * P = P) (A C : B) :
    ω (peirceLogisticPlus P A C) + ω (peirceLogisticMinus P A C) = 1 := by
  rw [peirceLogistic_additive_readout ω hAdd hP A C, hOne]

theorem peirceLogistic_readout_transports_variance
    {R : Type*} [Ring R] (ω : B → R)
    {P : B} (hP : P * P = P) (A C : B) :
    ω (peirceLogisticPlus P A C * peirceLogisticMinus P A C) =
      ω (-(genV P A C * genV P A C - genV P A C)) := by
  rw [(peirceLogistic_operator_identities hP A C).2.2.1]

theorem stateReadout_refinement
    {R : Type*} [Ring R] (ω : B → R)
    (hAdd : ∀ X Y : B, ω (X + Y) = ω X + ω Y)
    (L : B) (w : List Bool) :
    ω (operatorBitwordCylinder (true :: w) L) +
      ω (operatorBitwordCylinder (false :: w) L) =
      ω (operatorBitwordCylinder w L) := by
  rw [← hAdd, operatorBitwordCylinder_refinement]

theorem stateReadout_mixed_variance
    {R : Type*} [Ring R] (ω : B → R)
    {P : B} (hP : P * P = P) (A C : B) :
    ω (operatorBitwordCylinder [true, false] (peirceLogisticPlus P A C)) =
      ω (-(genV P A C * genV P A C - genV P A C)) ∧
    ω (operatorBitwordCylinder [false, true] (peirceLogisticPlus P A C)) =
      ω (-(genV P A C * genV P A C - genV P A C)) := by
  rcases peirceLogistic_mixed_cylinders_are_variance hP A C with ⟨hTF, hFT⟩
  exact ⟨congrArg ω hTF, congrArg ω hFT⟩

theorem onShell_logistic_is_idempotent
    {P : B} (hP : P * P = P) (A C : B)
    (hV : genV P A C * genV P A C - genV P A C = 0) :
    peirceLogisticPlus P A C * peirceLogisticPlus P A C =
      peirceLogisticPlus P A C ∧
    peirceLogisticMinus P A C * peirceLogisticMinus P A C =
      peirceLogisticMinus P A C := by
  rcases peirceLogistic_operator_identities hP A C with ⟨_, hComp, hVar, hVarRev⟩
  have hProd : peirceLogisticPlus P A C * peirceLogisticMinus P A C = 0 := by
    rw [hVar, hV]
    simp
  have hVarianceZero : peirceLogisticPlus P A C *
      (1 - peirceLogisticPlus P A C) = 0 := by
    calc
      peirceLogisticPlus P A C * (1 - peirceLogisticPlus P A C) =
          peirceLogisticPlus P A C * peirceLogisticMinus P A C := by rw [hComp]
      _ = 0 := hProd
  have hL : peirceLogisticPlus P A C * peirceLogisticPlus P A C =
      peirceLogisticPlus P A C := by
    apply sub_eq_zero.mp
    calc
      peirceLogisticPlus P A C * peirceLogisticPlus P A C -
          peirceLogisticPlus P A C =
          -(peirceLogisticPlus P A C *
            (1 - peirceLogisticPlus P A C)) := by noncomm_ring
      _ = 0 := by rw [hVarianceZero]; simp
  have hLm : peirceLogisticMinus P A C * peirceLogisticMinus P A C =
      peirceLogisticMinus P A C := by
    rw [← hComp]
    calc
      (1 - peirceLogisticPlus P A C) * (1 - peirceLogisticPlus P A C)
        = 1 - peirceLogisticPlus P A C - peirceLogisticPlus P A C +
            peirceLogisticPlus P A C * peirceLogisticPlus P A C := by noncomm_ring
      _ = 1 - peirceLogisticPlus P A C := by rw [hL]; abel
  exact ⟨hL, hLm⟩

theorem onShell_adjacent_mixed_cylinder_zero
    {P : B} (hP : P * P = P) (A C : B)
    (hV : genV P A C * genV P A C - genV P A C = 0)
    {w : List Bool} (hw : hasAdjacentBitChange w) :
    operatorBitwordCylinder w (peirceLogisticPlus P A C) = 0 := by
  have hL := (onShell_logistic_is_idempotent hP A C hV).1
  exact operatorBitwordCylinder_adjacentChange_zero hL hw

theorem onShell_pure_cylinder_true
    {P : B} (hP : P * P = P) (A C : B)
    (hV : genV P A C * genV P A C - genV P A C = 0) (n : ℕ) (hn : 0 < n) :
    operatorBitwordCylinder (List.replicate n true) (peirceLogisticPlus P A C) =
      peirceLogisticPlus P A C := by
  have hL := (onShell_logistic_is_idempotent hP A C hV).1
  have hAll : ∀ m : ℕ,
      operatorBitwordCylinder (List.replicate (m + 1) true)
        (peirceLogisticPlus P A C) = peirceLogisticPlus P A C := by
    intro m
    induction m with
    | zero => simp [operatorBitwordCylinder, operatorBitSelect]
    | succ m ih =>
        simp only [List.replicate_succ, operatorBitwordCylinder,
          operatorBitSelect] at ih ⊢
        rw [ih, hL]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa using hAll m

theorem onShell_pure_cylinder_false
    {P : B} (hP : P * P = P) (A C : B)
    (hV : genV P A C * genV P A C - genV P A C = 0) (n : ℕ) (hn : 0 < n) :
    operatorBitwordCylinder (List.replicate n false) (peirceLogisticPlus P A C) =
      peirceLogisticMinus P A C := by
  have hL := (onShell_logistic_is_idempotent hP A C hV).2
  have hComp := (peirceLogistic_operator_identities hP A C).2.1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  induction m with
  | zero => simpa [operatorBitwordCylinder, operatorBitSelect] using hComp
  | succ m ih =>
      simp only [List.replicate_succ, operatorBitwordCylinder,
        operatorBitSelect] at ih ⊢
      rw [ih (by omega), hComp, hL]

/-! ### Master synthesis -/

/-- D₄₂ synthesis: operator partition, normalized readout, two-branch gap
invariance, cylinder refinement/concatenation, and state-level refinement.
The readout remains a separate additive map and is normalized only here. -/
theorem stage_D42_logistic_cantor_bitword_readout
    {R : Type*} [Ring R] (ω : B → R)
    (hAdd : ∀ X Y : B, ω (X + Y) = ω X + ω Y) (hOne : ω 1 = 1)
    {P P₁ P₂ : B} (hP : P * P = P)
    (hP₁ : P₁ * P₁ = P₁) (hP₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = 0) (h₂₁ : P₂ * P₁ = 0)
    (X Y A C : B) (u v w : List Bool) :
    peirceLogisticPlus P A C + peirceLogisticMinus P A C = 1 ∧
    ω (peirceLogisticPlus P A C) + ω (peirceLogisticMinus P A C) = 1 ∧
    branchCompression P₁ P₂
      (X + branchGap P₁ P₂ * Y * branchGap P₁ P₂) = branchCompression P₁ P₂ X ∧
    branchCompression P (1 - P) (peirceLogisticPlus P A C) =
      peirceLogisticPlus P A C ∧
    operatorBitwordCylinder (true :: w) (peirceLogisticPlus P A C) +
      operatorBitwordCylinder (false :: w) (peirceLogisticPlus P A C) =
      operatorBitwordCylinder w (peirceLogisticPlus P A C) ∧
    operatorBitwordCylinder (u ++ v) (peirceLogisticPlus P A C) =
      operatorBitwordCylinder u (peirceLogisticPlus P A C) *
        operatorBitwordCylinder v (peirceLogisticPlus P A C) ∧
    operatorBitwordCylinder [true, false] (peirceLogisticPlus P A C) =
      -(genV P A C * genV P A C - genV P A C) ∧
    ω (operatorBitwordCylinder (true :: w) (peirceLogisticPlus P A C)) +
      ω (operatorBitwordCylinder (false :: w) (peirceLogisticPlus P A C)) =
      ω (operatorBitwordCylinder w (peirceLogisticPlus P A C)) := by
  have hOp := peirceLogistic_operator_identities hP A C
  have hRead := peirceLogistic_normalized_readout ω hAdd hOne hP A C
  have hGap := branchCompression_ignores_gap hP₁ hP₂ h₁₂ h₂₁ X Y
  have hFixed := branchCompression_fixes_logistic hP A C
  have hRef := operatorBitwordCylinder_refinement (peirceLogisticPlus P A C) w
  have hAppend := operatorBitwordCylinder_append (peirceLogisticPlus P A C) u v
  have hMix := peirceLogistic_mixed_cylinders_are_variance hP A C
  have hState := stateReadout_refinement ω hAdd (peirceLogisticPlus P A C) w
  exact ⟨hOp.1, hRead, hGap, hFixed, hRef, hAppend, hMix.1, hState⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
