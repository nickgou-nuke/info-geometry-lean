import InfoGeometry.Canonical.CantorBinaryHopCharge
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.CantorDiracSeaHopping

Finite binary-word hopping for the Cantor/Dirac-sea boundary model.

This file proves the finite `List Bool` dynamics only:

* flipping a fixed finite position is involutive;
* flipping an in-range bit changes total `ZMod 2` charge by `1`;
* flipping the same position twice restores charge;
* flipping out of range is the identity.

No current-algebra theorem.
No infinite-factor theorem.
No infinite-limit claim.
-/

namespace InfoGeometry.Canonical.CantorDiracSeaHopping

open InfoGeometry.Canonical.CantorCuntzBasis
open InfoGeometry.Canonical.CantorBinaryHopCharge

/--
Flip the bit at a finite position in a binary Cantor word.

If the position is out of range, the word is unchanged.
-/
def flipAt : Nat → BinaryWord → BinaryWord
  | _, [] => []
  | 0, b :: w => hopBit b :: w
  | i + 1, b :: w => b :: flipAt i w

@[simp]
theorem flipAt_nil (i : Nat) :
    flipAt i ([] : BinaryWord) = [] := by
  cases i <;> rfl

@[simp]
theorem flipAt_zero_cons (b : Bool) (w : BinaryWord) :
    flipAt 0 (b :: w) = hopBit b :: w := by
  rfl

@[simp]
theorem flipAt_succ_cons (i : Nat) (b : Bool) (w : BinaryWord) :
    flipAt (i + 1) (b :: w) = b :: flipAt i w := by
  rfl

/-- Flipping a fixed finite position twice is the identity. -/
@[simp]
theorem flipAt_involutive (i : Nat) (w : BinaryWord) :
    flipAt i (flipAt i w) = w := by
  induction i generalizing w with
  | zero =>
      cases w with
      | nil => rfl
      | cons b w =>
          cases b <;> rfl
  | succ i ih =>
      cases w with
      | nil => rfl
      | cons b w =>
          simp [ih]

/-- A flip beyond the word length is the identity. -/
theorem flipAt_eq_self_of_length_le
    {i : Nat} {w : BinaryWord}
    (h : w.length ≤ i) :
    flipAt i w = w := by
  induction i generalizing w with
  | zero =>
      cases w with
      | nil => rfl
      | cons b w =>
          simp at h
  | succ i ih =>
      cases w with
      | nil => rfl
      | cons b w =>
          have htail : w.length ≤ i := by
            simpa using Nat.succ_le_succ_iff.mp h
          simp [ih htail]

/--
Flipping an in-range bit changes total `ZMod 2` charge by `1`.

This is the finite Dirac-sea hopping charge law:
`Q(flip_i w) = Q(w) + 1` in `ZMod 2`.
-/
theorem charge_flipAt_of_lt
    {i : Nat} {w : BinaryWord}
    (h : i < w.length) :
    wordCharge (flipAt i w) = wordCharge w + 1 := by
  induction i generalizing w with
  | zero =>
      cases w with
      | nil =>
          simp at h
      | cons b w =>
          simp [wordCharge, bitCharge_hopBit]
          abel
  | succ i ih =>
      cases w with
      | nil =>
          simp at h
      | cons b w =>
          have htail : i < w.length := by
            simpa using Nat.succ_lt_succ_iff.mp h
          simp [wordCharge, ih htail]
          abel

/-- Flipping the same finite position twice restores total charge. -/
theorem charge_flipAt_twice (i : Nat) (w : BinaryWord) :
    wordCharge (flipAt i (flipAt i w)) = wordCharge w := by
  simp

/-- An out-of-range flip leaves total charge unchanged. -/
theorem charge_flipAt_of_length_le
    {i : Nat} {w : BinaryWord}
    (h : w.length ≤ i) :
    wordCharge (flipAt i w) = wordCharge w := by
  rw [flipAt_eq_self_of_length_le h]

end InfoGeometry.Canonical.CantorDiracSeaHopping
