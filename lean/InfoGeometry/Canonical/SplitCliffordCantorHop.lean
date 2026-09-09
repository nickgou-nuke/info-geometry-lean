import InfoGeometry.Canonical.SplitCliffordCantorFock
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.SplitCliffordCantorHop

Finite binary/Cantor hop and local split-Clifford ladder identities.

No infinite Cantor stream theorem.
No cylinder-local indexed hop theorem.
No Cuntz representation theorem.
No Type III/predual theorem.
No Virasoro-origin theorem.
-/

namespace InfoGeometry.Canonical.SplitCliffordCantorHop

open Matrix
open SplitCliffordCantorFock

/-- Local binary hop on a Cantor bit. -/
def hopBit (b : Bool) : Bool :=
  !b

@[simp]
theorem hopBit_false :
    hopBit false = true := by
  rfl

@[simp]
theorem hopBit_true :
    hopBit true = false := by
  rfl

/-- The local binary hop is involutive. -/
@[simp]
theorem hopBit_involutive (b : Bool) :
    hopBit (hopBit b) = b := by
  cases b <;> rfl

/-- `ZMod 2` charge of a Boolean occupation bit. -/
def bitCharge (b : Bool) : ZMod 2 :=
  if b then 1 else 0

@[simp]
theorem bitCharge_false :
    bitCharge false = 0 := by
  rfl

@[simp]
theorem bitCharge_true :
    bitCharge true = 1 := by
  rfl

/-- A single local hop flips the `ZMod 2` bit charge. -/
@[simp]
theorem bitCharge_hopBit (b : Bool) :
    bitCharge (hopBit b) = bitCharge b + 1 := by
  cases b <;> rfl

/-- Finite binary word carrier. -/
def BinaryWord : Type :=
  List Bool

/-- Finite `ZMod 2` charge of a binary word. -/
def wordCharge : BinaryWord → ZMod 2
  | [] => 0
  | b :: bs => bitCharge b + wordCharge bs

/-- Hop the first site of a finite binary word. -/
def hopHead : BinaryWord → BinaryWord
  | [] => []
  | b :: bs => hopBit b :: bs

@[simp]
theorem hopHead_nil :
    hopHead [] = [] := by
  rfl

@[simp]
theorem hopHead_cons (b : Bool) (bs : List Bool) :
    hopHead (b :: bs) = hopBit b :: bs := by
  rfl

/-- The head-hop is involutive. -/
@[simp]
theorem hopHead_involutive (w : BinaryWord) :
    hopHead (hopHead w) = w := by
  cases w with
  | nil => rfl
  | cons b bs =>
      cases b <;> rfl

/-- A single nonempty head-hop flips the finite `ZMod 2` word charge. -/
theorem wordCharge_hopHead_cons
    (b : Bool) (bs : List Bool) :
    wordCharge (hopHead (b :: bs)) =
      wordCharge (b :: bs) + 1 := by
  simp [hopHead, wordCharge, bitCharge_hopBit]
  abel

/-- Two head-hops return the charge to its original value. -/
theorem wordCharge_hopHead_twice
    (w : BinaryWord) :
    wordCharge (hopHead (hopHead w)) = wordCharge w := by
  rw [hopHead_involutive]

/-- The annihilation operator is square-zero. -/
@[simp]
theorem a_op_sq_zero :
    a_op * a_op = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a_op, Matrix.mul_apply, Fin.sum_univ_two]

/-- The creation operator is square-zero. -/
@[simp]
theorem aDag_op_sq_zero :
    aDag_op * aDag_op = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

/-- Local CAR identity on the Boolean/Cantor cell. -/
theorem local_car_identity :
    a_op * aDag_op + aDag_op * a_op = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Boolean hop from `false` to `true` is realized by creation. -/
theorem cantorState_hop_false_eq_create :
    cantorState (hopBit false) = aDag_op * cantorState false := by
  simpa [hopBit] using create_false_eq_true.symm

/-- The Boolean hop from `true` to `false` is realized by annihilation. -/
theorem cantorState_hop_true_eq_annihilate :
    cantorState (hopBit true) = a_op * cantorState true := by
  simpa [hopBit] using annihilate_true_eq_false.symm

/-- Square-zero packet for the two local ladder operators. -/
theorem nilpotent_packet :
    a_op * a_op = (0 : M2R) ∧
    aDag_op * aDag_op = (0 : M2R) :=
  ⟨a_op_sq_zero, aDag_op_sq_zero⟩

/-- Finite local hop parity packet. -/
theorem cantor_hop_packet :
    (∀ b : Bool, hopBit (hopBit b) = b) ∧
    (∀ b : Bool, bitCharge (hopBit b) = bitCharge b + 1) ∧
    (∀ w : BinaryWord, hopHead (hopHead w) = w) ∧
    (∀ w : BinaryWord, wordCharge (hopHead (hopHead w)) = wordCharge w) :=
  ⟨hopBit_involutive,
    bitCharge_hopBit,
    hopHead_involutive,
    wordCharge_hopHead_twice⟩

/-- Local matrix realization packet for the two endpoint hops and CAR identity. -/
theorem local_matrix_hop_packet :
    cantorState (hopBit false) = aDag_op * cantorState false ∧
    cantorState (hopBit true) = a_op * cantorState true ∧
    a_op * aDag_op + aDag_op * a_op = (1 : M2R) :=
  ⟨cantorState_hop_false_eq_create,
    cantorState_hop_true_eq_annihilate,
    local_car_identity⟩

end InfoGeometry.Canonical.SplitCliffordCantorHop
