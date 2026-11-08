/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel
import Mathlib.Order.Hom.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Stage D₃₅ (Archetypes L₁ → L₅): Non-Commutative KMS Strip, Winding Monodromy, Logistic Compactification, and Edge Transition Closure

1. **Archetype L₁ (`L1_kmsToCriticalStripMidline`)**:
   KMS-to-Critical-Strip coordinate map `kmsToCrit`, inverse `critToKms`, and midline
   correspondence `kmsReflect P S_kms = S_kms ↔ kreinReflect P (kmsToCrit P S_kms) = kmsToCrit P S_kms`.
2. **Archetype L₂ (`L2_periodTwoWindingMonodromy`)**:
   Period-two winding monodromy `monodromyIter (n + 2) P X = monodromyIter n P X` for the
   involutive automorphism `zornAuto P` of a non-commutative operator ring `[Ring B]`.
3. **Archetype L₃ (`L3_noncommLogisticCompactification`)**:
   Non-commutative logistic compactification operators `logisticOpPlus` and `logisticOpMinus`
   satisfying `logisticOpPlus + logisticOpMinus = 1`, self-adjointness `star L_± = L_±`,
   and logistic variance product `logisticOpPlus * logisticOpMinus = -idemDefect (genV P A C)`.
4. **Archetype L₄ (`L4_twistedEdgeTransitionCocycle`)**:
   Operator-valued boundary data and twisted semidirect edge-transition cocycle
   `edgeTransition P G₂ G₂_inv (edgeTransition P G₁ G₁_inv X)`.
5. **Archetype L₅ (`L5_unipotentKleinQuotientClosure`)**:
   Exact period-two closure of unipotent horizon edge transitions
   `edgeTransition P (1 + conePlus P A) (1 - conePlus P A) (edgeTransition P (1 + conePlus P A) (1 - conePlus P A) X) = X`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B]

/-! ### Causal Poset of Stage D₃₅ Archetypes (L₁ → L₅) -/

/-- The 5-stage causal poset of non-commutative KMS strip, logistic compactification,
and boundary edge-transition archetypes (`L₁ → L₅`). -/
inductive StageD35Archetype
  | L1_kmsToCriticalStripMidline
  | L2_periodTwoWindingMonodromy
  | L3_noncommLogisticCompactification
  | L4_twistedEdgeTransitionCocycle
  | L5_unipotentKleinQuotientClosure
  deriving DecidableEq, Repr

instance instInhabitedStageD35Archetype : Inhabited StageD35Archetype :=
  ⟨.L1_kmsToCriticalStripMidline⟩

/-- Topological rank in the 5-stage causal poset. -/
def stageD35Rank : StageD35Archetype → ℕ
  | .L1_kmsToCriticalStripMidline => 0
  | .L2_periodTwoWindingMonodromy => 1
  | .L3_noncommLogisticCompactification => 2
  | .L4_twistedEdgeTransitionCocycle => 3
  | .L5_unipotentKleinQuotientClosure => 4

theorem stageD35Rank_injective : Function.Injective stageD35Rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance instPartialOrderStageD35Archetype : PartialOrder StageD35Archetype :=
  PartialOrder.lift stageD35Rank stageD35Rank_injective

theorem stageD35_strict_causal_chain :
    StageD35Archetype.L1_kmsToCriticalStripMidline < .L2_periodTwoWindingMonodromy ∧
    StageD35Archetype.L2_periodTwoWindingMonodromy < .L3_noncommLogisticCompactification ∧
    StageD35Archetype.L3_noncommLogisticCompactification < .L4_twistedEdgeTransitionCocycle ∧
    StageD35Archetype.L4_twistedEdgeTransitionCocycle < .L5_unipotentKleinQuotientClosure := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Stage 0: Core Peirce, KMS Strip, Monodromy, Logistic & Edge-Transition Primitives -/

/-- Idempotency defect `X² - X`. -/
def idemDefect (X : B) : B := X * X - X

/-- Upper corner quadratic product `N₊ N₋`. -/
def qgtPlus (P A C : B) : B := conePlus P A * coneMinus P C

/-- Lower corner quadratic product `N₋ N₊`. -/
def qgtMinus (P A C : B) : B := coneMinus P C * conePlus P A

/-- Involutive Zorn parity automorphism `τ_S(X) = S_P X S_P`. -/
def zornAuto (P X : B) : B := invS P * X * invS P

/-- Krein critical reflection `τ_Krein(X) = S_P X^⋆ S_P`. -/
def kreinReflect (P X : B) : B := invS P * star X * invS P

/-- **Archetype L₁: KMS-to-Critical-Strip Coordinate Map (`kmsToCrit`), Inverse (`critToKms`),
and KMS Strip Reflection (`kmsReflect`).** -/
def kmsToCrit (P S_kms : B) : B := S_kms - P

def critToKms (P X_crit : B) : B := P + X_crit

def kmsReflect (P S_kms : B) : B :=
  critToKms P (kreinReflect P (kmsToCrit P S_kms))

/-- **Archetype L₂: Iterated Winding Monodromy (`monodromyIter`) of the Involutive Automorphism `zornAuto P`.** -/
def monodromyIter : ℕ → B → B → B
  | 0, _, X => X
  | n + 1, P, X => zornAuto P (monodromyIter n P X)

/-- **Archetype L₃: Non-Commutative Logistic Compactification Operators (`logisticOpPlus`, `logisticOpMinus`).** -/
def logisticOpPlus (P A C : B) : B :=
  P * (1 - qgtPlus P A C) + (1 - P) * qgtMinus P A C

def logisticOpMinus (P A C : B) : B :=
  (1 - P) * (1 - qgtMinus P A C) + P * qgtPlus P A C

/-- **Archetype L₄ & L₅: Explicit Boundary Edge Transition (`edgeTransition`)
and Boundary Defect (`boundaryJumpDefect`).** -/
def edgeTransition (P G_edge G_inv X : B) : B :=
  G_edge * zornAuto P X * G_inv

def boundaryJumpDefect (P G_edge G_inv X : B) : B :=
  edgeTransition P G_edge G_inv X - X

/-- Constructor-indexed operator realization mapping each `StageD35Archetype` stage to its
canonical operator in `[Ring B] [StarRing B]`. -/
def stageD35Operator (P A C X : B) : StageD35Archetype → B
  | .L1_kmsToCriticalStripMidline => kmsToCrit P (critToKms P X)
  | .L2_periodTwoWindingMonodromy => zornAuto P X
  | .L3_noncommLogisticCompactification => logisticOpPlus P A C
  | .L4_twistedEdgeTransitionCocycle => logisticOpMinus P A C
  | .L5_unipotentKleinQuotientClosure =>
      edgeTransition P (1 + conePlus P A) (1 - conePlus P A) X

omit [StarRing B] in
theorem P_assoc {P : B} (hP : P * P = P) (X : B) : P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

macro "monodromy_abel" hP:ident : tactic =>
  `(tactic| (
    simp only [boundaryJumpDefect, edgeTransition,
               logisticOpPlus, logisticOpMinus,
               kmsReflect, kmsToCrit, critToKms, kreinReflect, zornAuto,
               genPhi, genJ, genV, qgtPlus, qgtMinus,
               conePlus, coneMinus, invS, comm, anticomm, idemDefect,
               zsmul_add, zsmul_sub, neg_zsmul, two_zsmul,
               sub_neg_eq_add, neg_mul, mul_neg, neg_neg,
               add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
               sub_self, mul_zero, zero_mul, add_zero, zero_add, neg_zero,
               mul_assoc, $hP:ident, P_assoc $hP:ident]
    try abel))

/-! ### Individual Theorems for Archetypes L₁ → L₅ -/

/-- **Theorem L₁.1 (KMS-to-Critical-Strip Coordinate Bijection & Midline Correspondence):**
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `S_kms, X_crit, B_im : B`:
1. `kmsToCrit P (critToKms P X_crit) = X_crit` and `critToKms P (kmsToCrit P S_kms) = S_kms`;
2. `kmsReflect P S_kms = S_kms ↔ kreinReflect P (kmsToCrit P S_kms) = kmsToCrit P S_kms`;
3. `kmsReflect P (critToKms P (genJ P B_im (star B_im))) = critToKms P (genJ P B_im (star B_im))`. -/
theorem kms_to_critical_strip_and_midline_correspondence
    {P : B} (hP : P * P = P) (hPsym : star P = P) (S_kms X_crit B_im : B) :
    kmsToCrit P (critToKms P X_crit) = X_crit ∧
    critToKms P (kmsToCrit P S_kms) = S_kms ∧
    (kmsReflect P S_kms = S_kms ↔
      kreinReflect P (kmsToCrit P S_kms) = kmsToCrit P S_kms) ∧
    kmsReflect P (critToKms P (genJ P B_im (star B_im))) =
      critToKms P (genJ P B_im (star B_im)) := by
  have hStarCone : star (conePlus P B_im) = coneMinus P (star B_im) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hStarConeM : star (coneMinus P (star B_im)) = conePlus P B_im := by
    rw [← hStarCone, star_star]
  have hStarJ : star (genJ P B_im (star B_im)) = -genJ P B_im (star B_im) := by
    unfold genJ; rw [star_sub, hStarCone, hStarConeM, neg_sub]
  refine ⟨by monodromy_abel hP, by monodromy_abel hP, ?_, ?_⟩
  · unfold kmsReflect critToKms kmsToCrit
    constructor
    · intro h
      have hSub : P + kreinReflect P (S_kms - P) - P = S_kms - P := by rw [h]
      simpa only [add_sub_cancel_left] using hSub
    · intro h
      rw [h]
      abel
  · unfold kmsReflect
    have hKmsJ : kmsToCrit P (critToKms P (genJ P B_im (star B_im))) = genJ P B_im (star B_im) := by
      monodromy_abel hP
    rw [hKmsJ]
    have hKreinJ : kreinReflect P (genJ P B_im (star B_im)) = genJ P B_im (star B_im) := by
      unfold kreinReflect; rw [hStarJ]; monodromy_abel hP
    rw [hKreinJ]

omit [StarRing B] in
/-- **Theorem L₂.1 (Involutive Ring Automorphism & Period-Two Winding Monodromy):**
For any idempotent `P` (`P * P = P`), any `X, Y : B`, and any winding step `n, k : ℕ`:
1. `zornAuto P` is an involutive ring automorphism;
2. `monodromyIter (n + 2) P X = monodromyIter n P X`, `monodromyIter (2 * k) P X = X`,
   and `monodromyIter (2 * k + 1) P X = zornAuto P X`. -/
theorem period_two_winding_monodromy {P : B} (hP : P * P = P) (X Y : B) (n k : ℕ) :
    zornAuto P (X + Y) = zornAuto P X + zornAuto P Y ∧
    zornAuto P (X * Y) = zornAuto P X * zornAuto P Y ∧
    zornAuto P (zornAuto P X) = X ∧
    monodromyIter (n + 2) P X = monodromyIter n P X ∧
    monodromyIter (2 * k) P X = X ∧
    monodromyIter (2 * k + 1) P X = zornAuto P X := by
  have hInv : ∀ Z : B, zornAuto P (zornAuto P Z) = Z := by
    intro Z; monodromy_abel hP
  have hStep2 : ∀ m : ℕ, monodromyIter (m + 2) P X = monodromyIter m P X := by
    intro m
    simp only [monodromyIter]
    exact hInv (monodromyIter m P X)
  have hEven : monodromyIter (2 * k) P X = X := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Nat.mul_succ, hStep2 (2 * k), ih]
  refine ⟨by monodromy_abel hP, by monodromy_abel hP, hInv X, hStep2 n, hEven, ?_⟩
  simp only [monodromyIter, hEven]

/-- **Theorem L₃.1 (Non-Commutative Logistic Compactification Operator in `[0, 1]`):**
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `A, C : B`:
1. `logisticOpPlus P A C + logisticOpMinus P A C = 1` and `1 - logisticOpPlus P A C = logisticOpMinus P A C`;
2. `logisticOpPlus P A C * logisticOpMinus P A C = -idemDefect (genV P A C)` and
   `logisticOpMinus P A C * logisticOpPlus P A C = -idemDefect (genV P A C)`;
3. `star (logisticOpPlus P A (star A)) = logisticOpPlus P A (star A)` and
   `star (logisticOpMinus P A (star A)) = logisticOpMinus P A (star A)`. -/
theorem noncomm_logistic_compactification_properties
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A C : B) :
    logisticOpPlus P A C + logisticOpMinus P A C = 1 ∧
    1 - logisticOpPlus P A C = logisticOpMinus P A C ∧
    logisticOpPlus P A C * logisticOpMinus P A C = -idemDefect (genV P A C) ∧
    logisticOpMinus P A C * logisticOpPlus P A C = -idemDefect (genV P A C) ∧
    star (logisticOpPlus P A (star A)) = logisticOpPlus P A (star A) ∧
    star (logisticOpMinus P A (star A)) = logisticOpMinus P A (star A) := by
  have hStarCone : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hStarConeM : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hStarCone, star_star]
  have hStarQp : star (qgtPlus P A (star A)) = qgtPlus P A (star A) := by
    unfold qgtPlus; rw [star_mul, hStarCone, hStarConeM]
  have hStarQm : star (qgtMinus P A (star A)) = qgtMinus P A (star A) := by
    unfold qgtMinus; rw [star_mul, hStarCone, hStarConeM]
  refine ⟨by monodromy_abel hP, by monodromy_abel hP,
          by monodromy_abel hP, by monodromy_abel hP, ?_, ?_⟩
  · unfold logisticOpPlus
    rw [star_add, star_mul, star_mul, star_sub, star_sub, star_one, hPsym, hStarQp, hStarQm]
    monodromy_abel hP
  · unfold logisticOpMinus
    rw [star_add, star_mul, star_mul, star_sub, star_sub, star_one, hPsym, hStarQp, hStarQm]
    monodromy_abel hP

omit [StarRing B] in
/-- **Theorem L₄.1 & L₅.1 (Twisted Boundary Edge Transition Cocycle & `KleinQuotientBridge` Period-Two Closure):**
For any idempotent `P` (`P * P = P`) and any `G₁, G₁_inv, G₂, G₂_inv, A, X : B`:
1. `edgeTransition P G₂ G₂_inv (edgeTransition P G₁ G₁_inv X) = (G₂ * zornAuto P G₁) * X * (zornAuto P G₁_inv * G₂_inv)`;
2. `(1 + conePlus P A) * zornAuto P (1 + conePlus P A) = 1` and `zornAuto P (1 - conePlus P A) * (1 - conePlus P A) = 1`;
3. `edgeTransition P (1 + conePlus P A) (1 - conePlus P A) (edgeTransition P (1 + conePlus P A) (1 - conePlus P A) X) = X`. -/
theorem twisted_edge_transition_cocycle_and_klein_quotient_bridge
    {P : B} (hP : P * P = P) (G₁ G₁_inv G₂ G₂_inv A X : B) :
    edgeTransition P G₂ G₂_inv (edgeTransition P G₁ G₁_inv X) =
      (G₂ * zornAuto P G₁) * X * (zornAuto P G₁_inv * G₂_inv) ∧
    (1 + conePlus P A) * zornAuto P (1 + conePlus P A) = 1 ∧
    zornAuto P (1 - conePlus P A) * (1 - conePlus P A) = 1 ∧
    edgeTransition P (1 + conePlus P A) (1 - conePlus P A)
      (edgeTransition P (1 + conePlus P A) (1 - conePlus P A) X) = X := by
  refine ⟨by monodromy_abel hP, by monodromy_abel hP, by monodromy_abel hP, by monodromy_abel hP⟩

/-- **Master Theorem D₃₅ (KMS-to-Critical-Strip Midline Bijection, Period-Two Winding Monodromy,
Non-Commutative Logistic Compactification & Twisted Klein Edge-Transition Closure):**
Unifies all 5 archetypes (`L₁ → L₅`) and `stageD35Operator` in native Mathlib4 with zero `sorry`s. -/
theorem stage_D35_kms_strip_klein_monodromy_logistic_and_edge_bridge_master_synthesis
    {P S_kms X_crit B_im A C X : B}
    (hP : P * P = P) (hPsym : star P = P) (n k : ℕ) :
    stageD35Operator P A C X_crit .L1_kmsToCriticalStripMidline = X_crit ∧
    kmsToCrit P (critToKms P X_crit) = X_crit ∧
    critToKms P (kmsToCrit P S_kms) = S_kms ∧
    (kmsReflect P S_kms = S_kms ↔
      kreinReflect P (kmsToCrit P S_kms) = kmsToCrit P S_kms) ∧
    monodromyIter (n + 2) P X = monodromyIter n P X ∧
    monodromyIter (2 * k) P X = X ∧
    monodromyIter (2 * k + 1) P X =
      stageD35Operator P A C X .L2_periodTwoWindingMonodromy ∧
    stageD35Operator P A C X .L3_noncommLogisticCompactification +
      stageD35Operator P A C X .L4_twistedEdgeTransitionCocycle = 1 ∧
    stageD35Operator P A C X .L3_noncommLogisticCompactification *
      stageD35Operator P A C X .L4_twistedEdgeTransitionCocycle = -idemDefect (genV P A C) ∧
    star (logisticOpPlus P A (star A)) = logisticOpPlus P A (star A) ∧
    (1 + conePlus P A) * zornAuto P (1 + conePlus P A) = 1 ∧
    edgeTransition P (1 + conePlus P A) (1 - conePlus P A)
      (stageD35Operator P A C X .L5_unipotentKleinQuotientClosure) = X := by
  dsimp only [stageD35Operator]
  rcases kms_to_critical_strip_and_midline_correspondence hP hPsym S_kms X_crit B_im with
    ⟨hM1, hM2, hM3, _⟩
  rcases period_two_winding_monodromy hP X X n k with
    ⟨_, _, _, hW4, hW5, hW6⟩
  rcases noncomm_logistic_compactification_properties hP hPsym A C with
    ⟨hL1, _, hL3, _, hL5, _⟩
  rcases twisted_edge_transition_cocycle_and_klein_quotient_bridge
    hP (1 + conePlus P A) (1 - conePlus P A) (1 + conePlus P A) (1 - conePlus P A) A X with
    ⟨_, hB2, _, hB4⟩
  exact ⟨hM1, hM1, hM2, hM3, hW4, hW5, hW6, hL1, hL3, hL5, hB2, hB4⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeKMSStripKleinMonodromyPoset
