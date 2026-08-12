import Mathlib.Tactic
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.WeylNormalizedCARCCRBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge

Theorem-safe bridge between:

* binary Cantor words as path addresses;
* tilt/switch Clifford operators on a discrete code;
* Clifford generator readout;
* canonical CAR/CCR channels on the doubled Fock lane.

This file does not assert any new analytic limit, any new infinite tensor
product theorem, or any RH-level convergence claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.TypeIIIModularCantorSystem
open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.WeylNormalizedCARCCRBridge

/-- Depth of a binary path code. -/
@[rep_depth operator]
def wordDepth (w : List Bool) : ℕ :=
  w.length

/-- A single binary refinement step increases depth by one. -/
@[rep_depth operator]
theorem binaryWord_child_length (w : List Bool) (b : Bool) :
    wordDepth (TypeIIIModularCantorSystem.child w b) = wordDepth w + 1 := by
  simp [wordDepth, TypeIIIModularCantorSystem.child]

/-- Every word lies in its own closed Cantor cylinder. -/
@[rep_depth operator]
theorem binaryWord_mem_closedCylinder_self (w : List Bool) :
    w ∈ TypeIIIModularCantorSystem.closedCylinder w := by
  simpa using (TypeIIIModularCantorSystem.mem_closedCylinder_self w)

/-- The binary Cantor cylinder splits into root, false child, and true child. -/
@[rep_depth operator]
theorem binaryWord_closedCylinder_split (w : List Bool) :
    TypeIIIModularCantorSystem.closedCylinder w =
      ({w} : Set (List Bool))
        ∪ TypeIIIModularCantorSystem.closedCylinder (TypeIIIModularCantorSystem.child w false)
        ∪ TypeIIIModularCantorSystem.closedCylinder (TypeIIIModularCantorSystem.child w true) := by
  simpa using (TypeIIIModularCantorSystem.closedCylinder_split w)

/--
Binary readout of a tilt/switch system at a given Cantor address.

The bit `false` selects the tilt operator; the bit `true` selects the switch
operator.  The word length is the scale parameter.
-/
@[rep_depth operator]
structure BinaryWordTiltReadout (Op : Type*) [Ring Op] where
  tiltSwitch : TiltSwitchSystem Op
  word : List Bool

namespace BinaryWordTiltReadout

variable {Op : Type*} [Ring Op]
variable (P : BinaryWordTiltReadout Op)

/-- Scale readout of the binary code. -/
@[rep_depth operator]
def depth : ℕ :=
  P.word.length

/-- Bit readout at the current scale. -/
@[rep_depth operator]
def bitOperator : Bool → Op :=
  fun b => if b then P.tiltSwitch.S P.word.length else P.tiltSwitch.T P.word.length

@[simp] theorem bitOperator_false :
    P.bitOperator false = P.tiltSwitch.T P.word.length := rfl

@[simp] theorem bitOperator_true :
    P.bitOperator true = P.tiltSwitch.S P.word.length := rfl

/-- The false-bit operator squares to one. -/
@[rep_depth operator]
theorem bitOperator_false_sq :
    P.bitOperator false * P.bitOperator false = 1 := by
  simp [bitOperator, TiltSwitchSystem.local_tilt_sq]

/-- The true-bit operator squares to one. -/
@[rep_depth operator]
theorem bitOperator_true_sq :
    P.bitOperator true * P.bitOperator true = 1 := by
  simp [bitOperator, TiltSwitchSystem.local_switch_sq]

/-- The false/true bit operators anticommute at the same address. -/
@[rep_depth operator]
theorem bitOperator_anticomm :
    P.bitOperator false * P.bitOperator true + P.bitOperator true * P.bitOperator false = 0 := by
  simp [bitOperator, TiltSwitchSystem.local_tilt_switch_anticomm]

end BinaryWordTiltReadout

theorem mul_sq_neg_one_of_sq_one_of_anticomm
    {Op : Type*} [Ring Op]
    {a b : Op}
    (ha : a * a = 1)
    (hb : b * b = 1)
    (hab : a * b + b * a = 0) :
    (a * b) * (a * b) = -1 := by
  have hba : b * a = -(a * b) :=
    eq_neg_of_add_eq_zero_right hab
  rw [show (a * b) * (a * b) = a * (b * a) * b by noncomm_ring]
  rw [hba]
  rw [show a * (-(a * b)) * b = -(a * a) * (b * b) by
    noncomm_ring]
  rw [ha, hb]
  noncomm_ring

@[rep_depth operator]
theorem bitOperator_product_sq_neg_one
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    (P.bitOperator false * P.bitOperator true) *
        (P.bitOperator false * P.bitOperator true) = -1 :=
  mul_sq_neg_one_of_sq_one_of_anticomm
    P.bitOperator_false_sq P.bitOperator_true_sq P.bitOperator_anticomm

def localCl11Positive
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) : Op :=
  P.bitOperator false

def localCl11Negative
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) : Op :=
  P.bitOperator false * P.bitOperator true

@[simp] theorem localCl11Positive_sq
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    localCl11Positive P * localCl11Positive P = 1 :=
  P.bitOperator_false_sq

@[simp] theorem localCl11Negative_sq
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    localCl11Negative P * localCl11Negative P = -1 :=
  bitOperator_product_sq_neg_one P

theorem localCl11Positive_negative_anticomm
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    localCl11Positive P * localCl11Negative P +
      localCl11Negative P * localCl11Positive P = 0 := by
  unfold localCl11Positive localCl11Negative
  have hanti := P.bitOperator_anticomm
  have hba :
      P.bitOperator true * P.bitOperator false =
        -(P.bitOperator false * P.bitOperator true) :=
    eq_neg_of_add_eq_zero_right hanti
  rw [show
    P.bitOperator false *
          (P.bitOperator false * P.bitOperator true) +
        (P.bitOperator false * P.bitOperator true) *
          P.bitOperator false =
      (P.bitOperator false * P.bitOperator false) *
          P.bitOperator true +
        P.bitOperator false *
          (P.bitOperator true * P.bitOperator false) by
      noncomm_ring]
  rw [P.bitOperator_false_sq, hba]
  have hassoc :
      P.bitOperator false *
          (P.bitOperator false * P.bitOperator true) =
        (P.bitOperator false * P.bitOperator false) *
          P.bitOperator true := by
    noncomm_ring
  have hneg :
      P.bitOperator false *
          -(P.bitOperator false * P.bitOperator true) =
        -(P.bitOperator false *
          (P.bitOperator false * P.bitOperator true)) := by
    noncomm_ring
  rw [hneg, hassoc, P.bitOperator_false_sq]
  simp

@[simp] theorem localCl11Positive_mul_negative
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    localCl11Positive P * localCl11Negative P =
      P.bitOperator true := by
  unfold localCl11Positive localCl11Negative
  rw [show P.bitOperator false *
      (P.bitOperator false * P.bitOperator true) =
        (P.bitOperator false * P.bitOperator false) *
          P.bitOperator true by noncomm_ring]
  rw [P.bitOperator_false_sq]
  simp

@[simp] theorem localCl11Negative_mul_positive
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    localCl11Negative P * localCl11Positive P =
      -(P.bitOperator true) := by
  unfold localCl11Negative localCl11Positive
  have hba :
      P.bitOperator true * P.bitOperator false =
        -(P.bitOperator false * P.bitOperator true) :=
    eq_neg_of_add_eq_zero_right P.bitOperator_anticomm
  rw [show
      (P.bitOperator false * P.bitOperator true) *
          P.bitOperator false =
        P.bitOperator false *
          (P.bitOperator true * P.bitOperator false) by noncomm_ring]
  rw [hba]
  rw [show P.bitOperator false *
      -(P.bitOperator false * P.bitOperator true) =
        -(P.bitOperator false *
          (P.bitOperator false * P.bitOperator true)) by noncomm_ring]
  rw [show P.bitOperator false *
      (P.bitOperator false * P.bitOperator true) =
        (P.bitOperator false * P.bitOperator false) *
          P.bitOperator true by noncomm_ring]
  rw [P.bitOperator_false_sq]
  simp

@[simp] theorem localCl11Positive_mul_switch
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    localCl11Positive P * P.bitOperator true =
      localCl11Negative P := by
  rfl

@[simp] theorem localCl11Switch_mul_positive
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    P.bitOperator true * localCl11Positive P =
      -(localCl11Negative P) := by
  unfold localCl11Positive localCl11Negative
  exact eq_neg_of_add_eq_zero_right P.bitOperator_anticomm

@[simp] theorem localCl11Negative_mul_switch
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    localCl11Negative P * P.bitOperator true =
      localCl11Positive P := by
  unfold localCl11Negative localCl11Positive
  rw [show (P.bitOperator false * P.bitOperator true) *
      P.bitOperator true = P.bitOperator false *
        (P.bitOperator true * P.bitOperator true) by noncomm_ring]
  rw [P.bitOperator_true_sq]
  simp

@[simp] theorem localCl11Switch_mul_negative
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    P.bitOperator true * localCl11Negative P =
      -(localCl11Positive P) := by
  unfold localCl11Negative localCl11Positive
  have hba :
      P.bitOperator true * P.bitOperator false =
        -(P.bitOperator false * P.bitOperator true) :=
    eq_neg_of_add_eq_zero_right P.bitOperator_anticomm
  rw [show P.bitOperator true *
      (P.bitOperator false * P.bitOperator true) =
        (P.bitOperator true * P.bitOperator false) *
          P.bitOperator true by noncomm_ring]
  rw [hba]
  rw [show -(P.bitOperator false * P.bitOperator true) *
      P.bitOperator true =
        -(P.bitOperator false *
          (P.bitOperator true * P.bitOperator true)) by noncomm_ring]
  rw [P.bitOperator_true_sq]
  simp

/- Conjugation by the switch implements the local grade reflection. -/
@[simp] theorem switch_conj_localCl11Positive
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    P.bitOperator true * localCl11Positive P * P.bitOperator true =
      -(localCl11Positive P) := by
  rw [localCl11Switch_mul_positive, neg_mul,
    localCl11Negative_mul_switch]

@[simp] theorem switch_conj_localCl11Negative
    {Op : Type*} [Ring Op]
    (P : BinaryWordTiltReadout Op) :
    P.bitOperator true * localCl11Negative P * P.bitOperator true =
      -(localCl11Negative P) := by
  rw [localCl11Switch_mul_negative, neg_mul,
    localCl11Positive_mul_switch]

def IsLocalCl11Relation
    {Op : Type*} [Ring Op]
    (positive negative : Op) : Prop :=
  positive * positive = 1 ∧
  negative * negative = -1 ∧
  positive * negative + negative * positive = 0

theorem IsLocalCl11Relation.negative_mul_positive
    {Op : Type*} [Ring Op]
    {positive negative : Op}
    (h : IsLocalCl11Relation positive negative) :
    negative * positive = -(positive * negative) := by
  exact eq_neg_of_add_eq_zero_right h.2.2

theorem binaryWordLocalCl11Relation
    {Op : Type*} [Ring Op] (P : BinaryWordTiltReadout Op) :
    IsLocalCl11Relation (localCl11Positive P) (localCl11Negative P) := by
  exact ⟨localCl11Positive_sq P, localCl11Negative_sq P,
    localCl11Positive_negative_anticomm P⟩

theorem switch_conj_preserves_localCl11Relation
    {Op : Type*} [Ring Op] (P : BinaryWordTiltReadout Op) :
    IsLocalCl11Relation
      (P.bitOperator true * localCl11Positive P * P.bitOperator true)
      (P.bitOperator true * localCl11Negative P * P.bitOperator true) := by
  rw [switch_conj_localCl11Positive P, switch_conj_localCl11Negative P]
  rcases binaryWordLocalCl11Relation P with ⟨hPositive, hNegative, hAnticomm⟩
  exact ⟨by
      calc
        (-localCl11Positive P) * (-localCl11Positive P) =
            localCl11Positive P * localCl11Positive P := by noncomm_ring
        _ = 1 := hPositive,
    by
      calc
        (-localCl11Negative P) * (-localCl11Negative P) =
            localCl11Negative P * localCl11Negative P := by noncomm_ring
        _ = -1 := hNegative,
    by
      calc
        (-localCl11Positive P) * (-localCl11Negative P) +
            (-localCl11Negative P) * (-localCl11Positive P) =
            localCl11Positive P * localCl11Negative P +
              localCl11Negative P * localCl11Positive P := by noncomm_ring
        _ = 0 := hAnticomm⟩

theorem binaryWordLocalCl11Relation_readout
    {Op : Type*} [Ring Op] (P : BinaryWordTiltReadout Op) :
    localCl11Positive P * localCl11Negative P = P.bitOperator true ∧
    localCl11Negative P * localCl11Positive P = -(P.bitOperator true) ∧
    localCl11Positive P * localCl11Negative P +
      localCl11Negative P * localCl11Positive P = 0 := by
  simp [localCl11Positive_mul_negative, localCl11Negative_mul_positive]

end InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
