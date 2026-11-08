/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge
import InfoGeometry.Optics.OperatorDerivationForms
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations
import InfoGeometry.OperatorAlgebra.PeirceSpine.IrreduciblePeirceKernel
import InfoGeometry.OperatorAlgebra.PeirceSpine.DiracPolynomialAction
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Tactic.NoncommRing

/-!
# Peirce cuts as finite-operator Fréchet Leibniz derivation archetypes

This module connects the repository's algebraic Peirce commutator with its
continuous operator-derivation carrier.  `FrechetOperatorDerivation` means a
continuous linear operator equipped with the noncommutative Leibniz law; the
results below do not identify it with a nonlinear Fréchet derivative.

The cut is represented by a subtype, so idempotency is part of the carrier
rather than an extra premise on each theorem. The causal stages record the
cut-generated inner derivation, its Leibniz action, and its square as the
off-diagonal Peirce projection.
-/

noncomputable section

namespace InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes

open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open SouriauOnsagerBKM

set_option synthInstance.maxHeartbeats 100000

/-- The carrier of finite operator-algebra Peirce cuts. -/
abbrev PeirceCut (n : ℕ) :=
  {P : FiniteOperatorAlgebra n // P * P = P}

/-- The continuous inner derivation associated to a cut. -/
def cutDerivation {n : ℕ} (P : PeirceCut n) :
    FrechetOperatorDerivation ℝ (FiniteOperatorAlgebra n) :=
  FrechetOperatorDerivation.ofInner (P : FiniteOperatorAlgebra n)

@[simp] theorem cutDerivation_apply {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    cutDerivation P X = peirceGradingDeriv (P : FiniteOperatorAlgebra n) X := by
  simp [cutDerivation, FrechetOperatorDerivation.ofInner_apply,
    peirceGradingDeriv, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]

/-- The cut commutator satisfies the noncommutative Leibniz law on the finite
operator algebra. This is a continuous operator derivation statement. -/
theorem cutDerivation_leibniz {n : ℕ} (P : PeirceCut n)
    (X Y : FiniteOperatorAlgebra n) :
    cutDerivation P (X * Y) =
      cutDerivation P X * Y + X * cutDerivation P Y := by
  exact (cutDerivation P).leibniz X Y

/-- The Yukawa operator associated with a Peirce cut determines its continuous
operator-valued Connes one-form derivation by the inner commutator. -/
def yukawaOneFormDerivation {n : ℕ} (P : PeirceCut n)
    (A C : FiniteOperatorAlgebra n) :
    FrechetOperatorDerivation ℝ (FiniteOperatorAlgebra n) :=
  FrechetOperatorDerivation.ofInner
    (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
      (P : FiniteOperatorAlgebra n) A C)

@[simp] theorem yukawaOneFormDerivation_apply {n : ℕ} (P : PeirceCut n)
    (A C X : FiniteOperatorAlgebra n) :
    yukawaOneFormDerivation P A C X =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
          (P : FiniteOperatorAlgebra n) A C) X := rfl

/-- The finite-operator Yukawa one-form is a continuous linear derivation
whose action obeys the noncommutative Leibniz rule. -/
theorem yukawaOneFormDerivation_leibniz {n : ℕ} (P : PeirceCut n)
    (A C X Y : FiniteOperatorAlgebra n) :
    yukawaOneFormDerivation P A C (X * Y) =
      yukawaOneFormDerivation P A C X * Y +
        X * yukawaOneFormDerivation P A C Y := by
  exact (yukawaOneFormDerivation P A C).leibniz X Y

/-- The idempotent-cut witness forces the inner derivation to vanish on the
Peirce corner supported by that cut. -/
theorem cutDerivation_leftCorner_zero {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    cutDerivation P ((P : FiniteOperatorAlgebra n) * X * P) = 0 := by
  rw [cutDerivation_apply]
  change (P : FiniteOperatorAlgebra n) *
      ((P : FiniteOperatorAlgebra n) * X * P) -
      ((P : FiniteOperatorAlgebra n) * X * P) * P = 0
  have hleft : (P : FiniteOperatorAlgebra n) *
      ((P : FiniteOperatorAlgebra n) * X * P) =
      (P : FiniteOperatorAlgebra n) * X * P := by
    calc
      _ = ((P : FiniteOperatorAlgebra n) * P) * X * P := by
        simp only [mul_assoc]
      _ = (P : FiniteOperatorAlgebra n) * X * P := by rw [P.property]
  have hright : ((P : FiniteOperatorAlgebra n) * X * P) * P =
      (P : FiniteOperatorAlgebra n) * X * P := by
    calc
      _ = (P : FiniteOperatorAlgebra n) * X *
          ((P : FiniteOperatorAlgebra n) * P) := by simp only [mul_assoc]
      _ = (P : FiniteOperatorAlgebra n) * X * P := by rw [P.property]
  rw [hleft, hright, sub_self]

/-- The Fréchet cut derivation vanishes on the full block-diagonal Peirce
projection, including both the cut corner and its complementary corner. -/
theorem cutDerivation_evenGrade_zero {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    cutDerivation P
      (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
        (P : FiniteOperatorAlgebra n) X) = 0 := by
  rw [cutDerivation_apply]
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    (P : FiniteOperatorAlgebra n)
    (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
      (P : FiniteOperatorAlgebra n) X) = 0
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
  peirce_nf P.property

/-- Squaring the continuous inner derivation generated by an idempotent
recovers exactly the odd Peirce projection. -/
theorem cutDerivation_square_eq_oddGrade {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    cutDerivation P (cutDerivation P X) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade
        (P : FiniteOperatorAlgebra n) X := by
  rw [cutDerivation_apply, cutDerivation_apply]
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (P : FiniteOperatorAlgebra n)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (P : FiniteOperatorAlgebra n) X) =
    InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade
      (P : FiniteOperatorAlgebra n) X
  exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A2_peirce_cartan_grading_and_tangent_closure
    (P := (P : FiniteOperatorAlgebra n)) P.property X X).2.1

/-- The inner derivation of an idempotent satisfies the polynomial identity
`ad_P^3 = ad_P`; its square is the off-diagonal Peirce projection. -/
theorem cutDerivation_cube_eq_self {n : ℕ} (P : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    cutDerivation P (cutDerivation P (cutDerivation P X)) = cutDerivation P X := by
  rw [cutDerivation_apply, cutDerivation_apply, cutDerivation_apply]
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (P : FiniteOperatorAlgebra n)
      (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (P : FiniteOperatorAlgebra n)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          (P : FiniteOperatorAlgebra n) X)) =
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (P : FiniteOperatorAlgebra n) X
  exact InfoGeometry.OperatorAlgebra.IrreduciblePeirceKernel.triple_commutator_eq_commutator
    P.property X

/-- The off-diagonal Peirce cone generates a square-zero graded differential.
Idempotency is carried by `P`; no independent square-zero or parity premise
is supplied to this theorem. -/
theorem cutOddDifferential_square_zero {n : ℕ} (P : PeirceCut n)
    (A X : FiniteOperatorAlgebra n) :
    InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
      (P : FiniteOperatorAlgebra n) A
      (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
        (P : FiniteOperatorAlgebra n) A X) = 0 := by
  exact InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus_square_zero
    (P := (P : FiniteOperatorAlgebra n)) A X P.property

/-- The same cut-generated graded differential satisfies the signed product
rule. This is an operator-algebraic graded Leibniz law, distinct from the
ordinary Fréchet Leibniz derivation `cutDerivation`. -/
theorem cutOddDifferential_graded_leibniz {n : ℕ} (P : PeirceCut n)
    (A X Y : FiniteOperatorAlgebra n) :
    InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
        (P : FiniteOperatorAlgebra n) A (X * Y) =
      InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
          (P : FiniteOperatorAlgebra n) A X * Y +
        InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.parity
          (P : FiniteOperatorAlgebra n) X *
          InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
            (P : FiniteOperatorAlgebra n) A Y := by
  exact InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus_graded_leibniz
    (P := (P : FiniteOperatorAlgebra n)) A X Y P.property

/-- The commutator of two cut-generated continuous operator derivations is
again a continuous operator derivation, with its pointwise action given by the
commutator of the two actions. -/
theorem cutDerivation_commutator_action {n : ℕ} (P Q : PeirceCut n)
    (X : FiniteOperatorAlgebra n) :
    FrechetOperatorDerivation.commutator (cutDerivation P) (cutDerivation Q) X =
      cutDerivation P (cutDerivation Q X) -
        cutDerivation Q (cutDerivation P X) := by
  exact FrechetOperatorDerivation.commutator_apply _ _ _

/-! ## Causal order of the proved archetypes -/

inductive Archetype where
  | idempotentCut
  | innerOperatorDerivation
  | yukawaDiracOperator
  | connesOneForm
  | peirceOddDifferential
  | leibnizAction
  | gradedLeibnizAction
  | squareZero
  | innerSquareProjection
  | innerCubicRelation
  | commutatorClosure
  deriving DecidableEq

def rank : Archetype → ℕ
  | .idempotentCut => 0
  | .innerOperatorDerivation => 1
  | .yukawaDiracOperator => 1
  | .connesOneForm => 2
  | .peirceOddDifferential => 1
  | .leibnizAction => 3
  | .gradedLeibnizAction => 2
  | .squareZero => 2
  | .innerSquareProjection => 2
  | .innerCubicRelation => 2
  | .commutatorClosure => 4

/-- Direct edges carry the precise operator identity that witnesses the
construction dependency. In particular, the one-form edge uses the continuous
Fréchet-Leibniz derivation owner, not a nonlinear derivative surrogate. -/
def edge : Archetype → Archetype → Prop
  | .idempotentCut, .innerOperatorDerivation =>
      ∀ (n : ℕ) (P : PeirceCut n) (X : FiniteOperatorAlgebra n),
        cutDerivation P X = peirceGradingDeriv (P : FiniteOperatorAlgebra n) X
  | .idempotentCut, .yukawaDiracOperator =>
      ∀ (n : ℕ) (P : PeirceCut n) (A C X : FiniteOperatorAlgebra n),
        InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
            (P : FiniteOperatorAlgebra n) A C =
          InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
              (P : FiniteOperatorAlgebra n) A +
            InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
              (P : FiniteOperatorAlgebra n) C
  | .yukawaDiracOperator, .connesOneForm =>
      ∀ (n : ℕ) (P : PeirceCut n) (A C X : FiniteOperatorAlgebra n),
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm
            (P : FiniteOperatorAlgebra n) X = 0 →
          InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm
              (InfoGeometry.OperatorAlgebra.PeirceSpine.invS
                (P : FiniteOperatorAlgebra n))
              (yukawaOneFormDerivation P A C X) = 0
  | .connesOneForm, .leibnizAction =>
      ∀ (n : ℕ) (P : PeirceCut n) (A C X Y : FiniteOperatorAlgebra n),
        yukawaOneFormDerivation P A C (X * Y) =
          yukawaOneFormDerivation P A C X * Y + X * yukawaOneFormDerivation P A C Y
  | .idempotentCut, .peirceOddDifferential =>
      ∀ (n : ℕ) (P : PeirceCut n) (A X : FiniteOperatorAlgebra n),
        InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
          (P : FiniteOperatorAlgebra n) A
          (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
            (P : FiniteOperatorAlgebra n) A X) = 0
  | .innerOperatorDerivation, .leibnizAction =>
      ∀ (n : ℕ) (P : PeirceCut n) (X Y : FiniteOperatorAlgebra n),
        cutDerivation P (X * Y) =
          cutDerivation P X * Y + X * cutDerivation P Y
  | .innerOperatorDerivation, .innerSquareProjection =>
      ∀ (n : ℕ) (P : PeirceCut n) (X : FiniteOperatorAlgebra n),
        cutDerivation P (cutDerivation P X) =
          InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade
            (P : FiniteOperatorAlgebra n) X
  | .innerOperatorDerivation, .innerCubicRelation =>
      ∀ (n : ℕ) (P : PeirceCut n) (X : FiniteOperatorAlgebra n),
        cutDerivation P (cutDerivation P (cutDerivation P X)) = cutDerivation P X
  | .peirceOddDifferential, .gradedLeibnizAction =>
      ∀ (n : ℕ) (P : PeirceCut n) (A X Y : FiniteOperatorAlgebra n),
        InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
            (P : FiniteOperatorAlgebra n) A (X * Y) =
          InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
              (P : FiniteOperatorAlgebra n) A X * Y +
            InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.parity
              (P : FiniteOperatorAlgebra n) X *
              InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
                (P : FiniteOperatorAlgebra n) A Y
  | .peirceOddDifferential, .squareZero =>
      ∀ (n : ℕ) (P : PeirceCut n) (A X : FiniteOperatorAlgebra n),
        InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
          (P : FiniteOperatorAlgebra n) A
          (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
            (P : FiniteOperatorAlgebra n) A X) = 0
  | .leibnizAction, .commutatorClosure =>
      ∀ {n : ℕ} (P Q : PeirceCut n) (X Y : FiniteOperatorAlgebra n),
        FrechetOperatorDerivation.commutator (cutDerivation P) (cutDerivation Q) (X * Y) =
          FrechetOperatorDerivation.commutator (cutDerivation P) (cutDerivation Q) X * Y +
            X * FrechetOperatorDerivation.commutator (cutDerivation P) (cutDerivation Q) Y
  | _, _ => False

theorem edge_idempotentCut_innerOperatorDerivation :
    edge .idempotentCut .innerOperatorDerivation := by
  intro n P X
  exact cutDerivation_apply P X

theorem edge_idempotentCut_yukawaDiracOperator :
    edge .idempotentCut .yukawaDiracOperator := by
  intro n P A C X
  rfl

theorem edge_yukawaDiracOperator_connesOneForm :
    edge .yukawaDiracOperator .connesOneForm := by
  intro n P A C X hEven
  rw [yukawaOneFormDerivation_apply]
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.peirce_yukawa_commutator_is_odd
    P.property A C X hEven

theorem edge_connesOneForm_leibnizAction :
    edge .connesOneForm .leibnizAction := by
  intro n P A C X Y
  exact yukawaOneFormDerivation_leibniz P A C X Y

theorem edge_idempotentCut_peirceOddDifferential :
    edge .idempotentCut .peirceOddDifferential := by
  intro n P A X
  exact cutOddDifferential_square_zero P A X

theorem edge_innerOperatorDerivation_leibnizAction :
    edge .innerOperatorDerivation .leibnizAction := by
  intro n P X Y
  exact cutDerivation_leibniz P X Y

theorem edge_innerOperatorDerivation_innerSquareProjection :
    edge .innerOperatorDerivation .innerSquareProjection := by
  intro n P X
  exact cutDerivation_square_eq_oddGrade P X

theorem edge_innerOperatorDerivation_innerCubicRelation :
    edge .innerOperatorDerivation .innerCubicRelation := by
  intro n P X
  exact cutDerivation_cube_eq_self P X

theorem edge_peirceOddDifferential_gradedLeibnizAction :
    edge .peirceOddDifferential .gradedLeibnizAction := by
  intro n P A X Y
  exact cutOddDifferential_graded_leibniz P A X Y

theorem edge_peirceOddDifferential_squareZero :
    edge .peirceOddDifferential .squareZero := edge_idempotentCut_peirceOddDifferential

theorem edge_leibnizAction_commutatorClosure :
    edge .leibnizAction .commutatorClosure := by
  intro n P Q X Y
  exact (FrechetOperatorDerivation.commutator (cutDerivation P) (cutDerivation Q)).leibniz X Y

/-- Reflexive transitive reachability in the direct-dependency graph. -/
inductive EdgeReachable : Archetype → Archetype → Prop where
  | refl (a : Archetype) : EdgeReachable a a
  | edge {a b : Archetype} : edge a b → EdgeReachable a b
  | trans {a b c : Archetype} : EdgeReachable a b → EdgeReachable b c →
      EdgeReachable a c

def causalLE : Archetype → Archetype → Prop := EdgeReachable

theorem edge_causalLE {a b : Archetype} (h : edge a b) : causalLE a b :=
  EdgeReachable.edge h

theorem edge_rank_strict {a b : Archetype} (h : edge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp_all [edge, rank]

theorem edgeReachable_rank_strict_of_ne {a b : Archetype}
    (h : EdgeReachable a b) (hne : a ≠ b) : rank a < rank b := by
  induction h with
  | @refl x => exact (hne rfl).elim
  | edge h => exact edge_rank_strict h
  | @trans x y z hxy hyz ihxy ihyz =>
      by_cases hxyEq : x = y
      · subst y
        exact ihyz hne
      · by_cases hyzEq : y = z
        · subst z
          exact ihxy hne
        · exact lt_trans (ihxy hxyEq) (ihyz hyzEq)

instance : PartialOrder Archetype where
  le := causalLE
  le_refl a := EdgeReachable.refl a
  le_trans _ _ _ hab hbc := EdgeReachable.trans hab hbc
  le_antisymm a b hab hba := by
    by_contra hne
    exact lt_asymm (edgeReachable_rank_strict_of_ne hab hne)
      (edgeReachable_rank_strict_of_ne hba (Ne.symm hne))

theorem causalLE_iff_edgeReachable {a b : Archetype} :
    causalLE a b ↔ EdgeReachable a b := Iff.rfl

theorem causalLE_rank_monotone {a b : Archetype} (h : causalLE a b) :
    rank a ≤ rank b := by
  induction h with
  | refl => exact le_rfl
  | edge h => exact Nat.le_of_lt (edge_rank_strict h)
  | trans _ _ h₁ h₂ => exact le_trans h₁ h₂

theorem idempotentCut_le_innerOperatorDerivation :
    Archetype.idempotentCut ≤ Archetype.innerOperatorDerivation := by
  change causalLE Archetype.idempotentCut Archetype.innerOperatorDerivation
  exact EdgeReachable.edge edge_idempotentCut_innerOperatorDerivation

theorem innerOperatorDerivation_le_leibnizAction :
    Archetype.innerOperatorDerivation ≤ Archetype.leibnizAction := by
  change causalLE Archetype.innerOperatorDerivation Archetype.leibnizAction
  exact EdgeReachable.edge edge_innerOperatorDerivation_leibnizAction

theorem idempotentCut_le_peirceOddDifferential :
    Archetype.idempotentCut ≤ Archetype.peirceOddDifferential := by
  change causalLE Archetype.idempotentCut Archetype.peirceOddDifferential
  exact EdgeReachable.edge edge_idempotentCut_peirceOddDifferential

theorem peirceOddDifferential_le_gradedLeibnizAction :
    Archetype.peirceOddDifferential ≤ Archetype.gradedLeibnizAction := by
  change causalLE Archetype.peirceOddDifferential Archetype.gradedLeibnizAction
  exact EdgeReachable.edge edge_peirceOddDifferential_gradedLeibnizAction

theorem peirceOddDifferential_le_squareZero :
    Archetype.peirceOddDifferential ≤ Archetype.squareZero := by
  change causalLE Archetype.peirceOddDifferential Archetype.squareZero
  exact EdgeReachable.edge edge_peirceOddDifferential_squareZero

theorem innerOperatorDerivation_le_innerSquareProjection :
    Archetype.innerOperatorDerivation ≤ Archetype.innerSquareProjection := by
  change causalLE Archetype.innerOperatorDerivation Archetype.innerSquareProjection
  exact EdgeReachable.edge edge_innerOperatorDerivation_innerSquareProjection

theorem innerOperatorDerivation_le_innerCubicRelation :
    Archetype.innerOperatorDerivation ≤ Archetype.innerCubicRelation := by
  change causalLE Archetype.innerOperatorDerivation Archetype.innerCubicRelation
  exact EdgeReachable.edge edge_innerOperatorDerivation_innerCubicRelation

theorem leibnizAction_le_commutatorClosure :
    Archetype.leibnizAction ≤ Archetype.commutatorClosure := by
  change causalLE Archetype.leibnizAction Archetype.commutatorClosure
  exact EdgeReachable.edge edge_leibnizAction_commutatorClosure

/-- The two consequences of the odd differential are parallel: nilpotence
does not depend on the inner derivation's square projection, or conversely. -/
theorem squareZero_incomparable_innerSquareProjection :
    ¬ Archetype.squareZero ≤ Archetype.innerSquareProjection ∧
    ¬ Archetype.innerSquareProjection ≤ Archetype.squareZero := by
  constructor
  · intro h
    change causalLE Archetype.squareZero Archetype.innerSquareProjection at h
    have hlt := edgeReachable_rank_strict_of_ne h (by decide)
    norm_num [rank] at hlt
  · intro h
    change causalLE Archetype.innerSquareProjection Archetype.squareZero at h
    have hlt := edgeReachable_rank_strict_of_ne h (by decide)
    norm_num [rank] at hlt

/-! ## Kernel-registered theorem claims

The registrations below package the individual proved operator laws in the
repository's proof-carrying `TypedArchetype` interface. Idempotency enters
through `PeirceCut`, not as a separate unproved law field.
-/

open InfoGeometry.MetaCompiler

def cutLeibnizArchetype (n : ℕ) :
    TypedArchetype (PeirceCut n × FiniteOperatorAlgebra n × FiniteOperatorAlgebra n) .proved where
  name := `InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutLeibnizArchetype
  phase := 63
  claim := fun input =>
    cutDerivation input.1 (input.2.1 * input.2.2) =
      (cutDerivation input.1 input.2.1) * input.2.2 +
        input.2.1 * (cutDerivation input.1 input.2.2)
  evidence := fun input => cutDerivation_leibniz input.1 input.2.1 input.2.2

def yukawaOneFormArchetype (n : ℕ) :
    TypedArchetype
      (PeirceCut n × (FiniteOperatorAlgebra n ×
        (FiniteOperatorAlgebra n ×
          (FiniteOperatorAlgebra n × FiniteOperatorAlgebra n)))) .proved where
  name := `InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.yukawaOneFormArchetype
  phase := 63
  claim := fun input =>
    yukawaOneFormDerivation input.1 input.2.1 input.2.2.1
        (input.2.2.2.1 * input.2.2.2.2) =
      yukawaOneFormDerivation input.1 input.2.1 input.2.2.1
          input.2.2.2.1 * input.2.2.2.2 +
        input.2.2.2.1 * yukawaOneFormDerivation input.1 input.2.1
          input.2.2.1 input.2.2.2.2
  evidence := fun input => yukawaOneFormDerivation_leibniz
    input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2

def cutSquareProjectionArchetype (n : ℕ) :
    TypedArchetype (PeirceCut n × FiniteOperatorAlgebra n) .proved where
  name := `InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutSquareProjectionArchetype
  phase := 63
  claim := fun input =>
    cutDerivation input.1 (cutDerivation input.1 input.2) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade
        (input.1 : FiniteOperatorAlgebra n) input.2
  evidence := fun input => cutDerivation_square_eq_oddGrade input.1 input.2

def cutCubicRelationArchetype (n : ℕ) :
    TypedArchetype (PeirceCut n × FiniteOperatorAlgebra n) .proved where
  name := `InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutCubicRelationArchetype
  phase := 63
  claim := fun input =>
    cutDerivation input.1 (cutDerivation input.1
      (cutDerivation input.1 input.2)) = cutDerivation input.1 input.2
  evidence := fun input => cutDerivation_cube_eq_self input.1 input.2

def cutSquareZeroArchetype (n : ℕ) :
    TypedArchetype (PeirceCut n × FiniteOperatorAlgebra n × FiniteOperatorAlgebra n) .proved where
  name := `InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutSquareZeroArchetype
  phase := 63
  claim := fun input =>
    InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
        (input.1 : FiniteOperatorAlgebra n) input.2.1
        (InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
          (input.1 : FiniteOperatorAlgebra n) input.2.1 input.2.2) = 0
  evidence := fun input => cutOddDifferential_square_zero input.1 input.2.1 input.2.2

def cutGradedLeibnizArchetype (n : ℕ) :
    TypedArchetype (PeirceCut n × FiniteOperatorAlgebra n ×
      (FiniteOperatorAlgebra n × FiniteOperatorAlgebra n)) .proved where
  name := `InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutGradedLeibnizArchetype
  phase := 63
  claim := fun input =>
    InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
        (input.1 : FiniteOperatorAlgebra n) input.2.1
          (input.2.2.1 * input.2.2.2) =
      InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
          (input.1 : FiniteOperatorAlgebra n) input.2.1 input.2.2.1 * input.2.2.2 +
        InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.parity
          (input.1 : FiniteOperatorAlgebra n) input.2.2.1 *
          InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPlus
            (input.1 : FiniteOperatorAlgebra n) input.2.1 input.2.2.2
  evidence := fun input => cutOddDifferential_graded_leibniz
    input.1 input.2.1 input.2.2.1 input.2.2.2

def cutCommutatorClosureArchetype (n : ℕ) :
    TypedArchetype (PeirceCut n × PeirceCut n × FiniteOperatorAlgebra n) .proved where
  name := `InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes.cutCommutatorClosureArchetype
  phase := 63
  claim := fun input =>
    FrechetOperatorDerivation.commutator (cutDerivation input.1) (cutDerivation input.2.1) input.2.2 =
      cutDerivation input.1 (cutDerivation input.2.1 input.2.2) -
        cutDerivation input.2.1 (cutDerivation input.1 input.2.2)
  evidence := fun input => cutDerivation_commutator_action input.1 input.2.1 input.2.2

#register_archetype cutLeibnizArchetype
#register_archetype yukawaOneFormArchetype
#register_archetype cutSquareProjectionArchetype
#register_archetype cutCubicRelationArchetype
#register_archetype cutSquareZeroArchetype
#register_archetype cutGradedLeibnizArchetype
#register_archetype cutCommutatorClosureArchetype

#audit_archetype cutLeibnizArchetype
#audit_archetype yukawaOneFormArchetype
#audit_archetype cutSquareProjectionArchetype
#audit_archetype cutCubicRelationArchetype
#audit_archetype cutSquareZeroArchetype
#audit_archetype cutGradedLeibnizArchetype
#audit_archetype cutCommutatorClosureArchetype

end InfoGeometry.Canonical.PeirceFrechetOperatorArchetypes
