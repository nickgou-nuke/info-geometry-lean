import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Canonical.SplitCliffordCantorFock
import Mathlib.Tactic

set_option linter.unnecessarySeqFocus false

/-!
# InfoGeometry.Canonical.CantorBinaryHopCharge

Concrete binary Cantor hop and charge-parity lemmas.

This file connects the Cantor binary-word carrier to the local split-Clifford
fermionic hop.

It proves:

* bit-hop is involutive;
* head-hop on binary words is involutive;
* one head-hop flips `ZMod 2` charge on nonempty words;
* two head-hops restore charge;
* the local matrix creation/annihilation operators realize the two Boolean hops;
* the creation and annihilation operators are square-zero;
* the local CAR identity holds.

No Type III theorem.
No Virasoro-origin claim.
No inductive-limit claim.
-/

namespace CantorBinaryHopCharge

open Matrix
open InfoGeometry.Canonical
open InfoGeometry.Canonical.CantorCuntzBasis
open InfoGeometry.Canonical.SplitCliffordCantorFock

/-- Bit charge in `ZMod 2`: `false ↦ 0`, `true ↦ 1`. -/
def bitCharge : Bool → ZMod 2
  | false => 0
  | true => 1

/-- Local Boolean hop: flip the bit. -/
def hopBit : Bool → Bool
  | false => true
  | true => false

@[simp]
theorem hopBit_involutive (b : Bool) :
    hopBit (hopBit b) = b := by
  cases b <;> rfl

/-- Flipping one bit changes its `ZMod 2` charge by `1`. -/
@[simp]
theorem bitCharge_hopBit (b : Bool) :
    bitCharge (hopBit b) = bitCharge b + 1 := by
  cases b <;> decide

/-- Binary words from the Cantor basis lane. -/
abbrev CBinaryWord := InfoGeometry.Canonical.CantorCuntzBasis.BinaryWord

/-- Total parity charge of a finite binary Cantor word. -/
def wordCharge : CBinaryWord → ZMod 2
  | [] => 0
  | b :: w => bitCharge b + wordCharge w

/--
Head-hop on a binary word.

The empty word is fixed. A nonempty word has its first bit flipped.
-/
def hopHead : CBinaryWord → CBinaryWord
  | [] => []
  | b :: w => hopBit b :: w

@[simp]
theorem hopHead_nil :
    hopHead ([] : CBinaryWord) = [] := by
  rfl

/-- Head-hop is involutive. -/
@[simp]
theorem hopHead_involutive (w : CBinaryWord) :
    hopHead (hopHead w) = w := by
  cases w with
  | nil => rfl
  | cons b w =>
      cases b <;> rfl

/-- On a nonempty word, one head-hop flips total `ZMod 2` charge. -/
theorem charge_flip_once_cons (b : Bool) (w : CBinaryWord) :
    wordCharge (hopHead (b :: w)) = wordCharge (b :: w) + 1 := by
  cases b <;> simp [hopHead, wordCharge, bitCharge_hopBit, add_assoc, add_left_comm, add_comm]

/-- After two head-hops, total charge returns. -/
theorem charge_flip_twice (w : CBinaryWord) :
    wordCharge (hopHead (hopHead w)) = wordCharge w := by
  simp

@[simp]
theorem charge_hopHead_nil :
    wordCharge (hopHead ([] : CBinaryWord)) = 0 := by
  rfl

/-! ## Matrix realization of the local Boolean hop -/

/-- Creation realizes the Boolean hop from `false` to `true`. -/
theorem creation_realizes_false_hop :
    aDag_op * cantorState false = cantorState (hopBit false) := by
  simpa [hopBit] using create_false_eq_true

/-- Annihilation realizes the Boolean hop from `true` to `false`. -/
theorem annihilation_realizes_true_hop :
    a_op * cantorState true = cantorState (hopBit true) := by
  simpa [hopBit] using annihilate_true_eq_false

/-- The annihilation operator is square-zero. -/
@[simp]
theorem a_op_sq_zero :
    a_op * a_op = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [a_op, Matrix.mul_apply, Fin.sum_univ_two]

/-- The creation operator is square-zero. -/
@[simp]
theorem aDag_op_sq_zero :
    aDag_op * aDag_op = (0 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

/-- Local CAR identity on the Cantor/Fock Boolean cell. -/
theorem local_car_identity :
    a_op * aDag_op + aDag_op * a_op = (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

/--
Applying creation twice to the local vacuum is zero.

This is the concrete `Op² = 0` Pauli-exclusion channel.
-/
theorem create_create_false_eq_zero :
    aDag_op * (aDag_op * cantorState false) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [aDag_op, cantorState, state_false, Matrix.mul_apply, Fin.sum_univ_two]

/--
Applying annihilation twice to the occupied state is zero.
-/
theorem annihilate_annihilate_true_eq_zero :
    a_op * (a_op * cantorState true) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [a_op, cantorState, state_true, Matrix.mul_apply, Fin.sum_univ_two]

end CantorBinaryHopCharge
