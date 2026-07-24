import Mathlib

/-!
# InfoGeometry.Canonical.SplitCliffordCantorFock

Boolean/Cantor local encoding of the `2×2` split-Clifford ladder block.
-/

namespace InfoGeometry.Canonical.SplitCliffordCantorFock

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev V2R := Matrix (Fin 2) (Fin 1) ℝ

/-- `false` (empty) local basis state `|0⟩`. -/
def state_false : V2R := !![1; 0]

/-- `true` (occupied) local basis state `|1⟩`. -/
def state_true : V2R := !![0; 1]

/-- Boolean-to-state map. -/
def cantorState (b : Bool) : V2R :=
  if b then state_true else state_false

/-- Local annihilation operator. -/
def a_op : M2R := !![0, 1; 0, 0]

/-- Local creation operator. -/
def aDag_op : M2R := !![0, 0; 1, 0]

/-- Local number operator. -/
def num_op : M2R := aDag_op * a_op

/-- Creation maps `false` to `true`. -/
theorem create_false_eq_true :
    aDag_op * cantorState false = cantorState true := by
  unfold cantorState state_false state_true aDag_op
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Annihilation maps `true` to `false`. -/
theorem annihilate_true_eq_false :
    a_op * cantorState true = cantorState false := by
  unfold cantorState state_false state_true a_op
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Creation annihilates `true` (Pauli exclusion). -/
theorem create_true_eq_zero :
    aDag_op * cantorState true = 0 := by
  unfold cantorState state_true aDag_op
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Annihilation annihilates `false`. -/
theorem annihilate_false_eq_zero :
    a_op * cantorState false = 0 := by
  unfold cantorState state_false a_op
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Number operator reads `true` with eigenvalue `1`. -/
theorem num_op_true_eval :
    num_op * cantorState true = cantorState true := by
  unfold num_op
  rw [Matrix.mul_assoc, annihilate_true_eq_false, create_false_eq_true]

/-- Number operator reads `false` with eigenvalue `0`. -/
theorem num_op_false_eval :
    num_op * cantorState false = 0 := by
  unfold num_op
  rw [Matrix.mul_assoc, annihilate_false_eq_zero, Matrix.mul_zero]

/-! ## Binary hop / parity charge layer -/

/--
Local binary hop on the Cantor bit.

This is the Boolean carrier version of toggling the local Dirac-sea occupation.
-/
def hopBit (b : Bool) : Bool :=
  !b

/-- The local hop is involutive. -/
@[simp]
theorem hopBit_involutive (b : Bool) :
    hopBit (hopBit b) = b := by
  cases b <;> rfl

/--
`ZMod 2` charge of one Boolean occupation bit.
-/
def bitCharge (b : Bool) : ZMod 2 :=
  if b then 1 else 0

/--
A single local hop flips the `ZMod 2` charge.
-/
@[simp]
theorem bitCharge_hopBit (b : Bool) :
    bitCharge (hopBit b) = bitCharge b + 1 := by
  cases b <;> rfl

/--
A word in the binary Cantor lattice is a finite local approximation to an
infinite Dirac-sea/Cantor configuration.
-/
abbrev BinaryWord :=
  List Bool

/--
Finite parity charge of a binary word.
-/
def wordCharge : BinaryWord → ZMod 2
  | [] => 0
  | b :: bs => bitCharge b + wordCharge bs

/--
Hop the first site of a finite binary word.

This is the finite local generator.  Infinite/Cantor versions should be added
only after the corresponding stream/cylinder owner surface is used.
-/
def hopHead : BinaryWord → BinaryWord
  | [] => []
  | b :: bs => hopBit b :: bs

/-- The head-hop is involutive. -/
@[simp]
theorem hopHead_involutive (w : BinaryWord) :
    hopHead (hopHead w) = w := by
  cases w with
  | nil => rfl
  | cons b bs =>
      cases b <;> rfl

/--
A single nonempty head-hop flips the finite `ZMod 2` charge.
-/
theorem wordCharge_hopHead_cons
    (b : Bool) (bs : List Bool) :
    wordCharge (hopHead (b :: bs)) =
      wordCharge (b :: bs) + 1 := by
  simp [hopHead, wordCharge, bitCharge_hopBit]
  abel

/--
Two head-hops return the charge to its original value.
-/
theorem wordCharge_hopHead_twice
    (w : BinaryWord) :
    wordCharge (hopHead (hopHead w)) = wordCharge w := by
  rw [hopHead_involutive]

/-! ## Matrix realization of the local hop -/

/--
The annihilation operator is square-zero.
-/
@[simp]
theorem a_op_sq_zero :
    a_op * a_op = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a_op, Matrix.mul_apply, Fin.sum_univ_two]

/--
The creation operator is square-zero.
-/
@[simp]
theorem aDag_op_sq_zero :
    aDag_op * aDag_op = (0 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

/--
Local CAR identity on the Boolean/Cantor cell.
-/
theorem local_car_identity :
    a_op * aDag_op + aDag_op * a_op = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a_op, aDag_op, Matrix.mul_apply, Fin.sum_univ_two]

/--
The Boolean hop from `false` to `true` is realized by creation.
-/
theorem cantorState_hop_false_eq_create :
    cantorState (hopBit false) = aDag_op * cantorState false := by
  simpa [hopBit] using create_false_eq_true.symm

/--
The Boolean hop from `true` to `false` is realized by annihilation.
-/
theorem cantorState_hop_true_eq_annihilate :
    cantorState (hopBit true) = a_op * cantorState true := by
  simpa [hopBit] using annihilate_true_eq_false.symm

end InfoGeometry.Canonical.SplitCliffordCantorFock

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `create_false_eq_true` : Verified mapping from empty to occupied state.
- `annihilate_true_eq_false` : Verified mapping from occupied to empty state.
- `create_true_eq_zero` : Verified Pauli exclusion constraint on state_true.
- `annihilate_false_eq_zero` : Verified annihilation constraint on state_false.
- `num_op_true_eval` : Verified number operator eigenvalue on occupied state.
- `num_op_false_eval` : Verified number operator eigenvalue on empty state.
- `hopBit_involutive` : Proves that local hop is involutive.
- `bitCharge_hopBit` : Proves that local hop flips the ZMod 2 charge.
- `hopHead_involutive` : Proves that head hop of a word is involutive.
- `wordCharge_hopHead_cons` : Proves that a single nonempty head hop flips the finite ZMod 2 word charge.
- `wordCharge_hopHead_twice` : Proves that two head hops return the charge to its original value.
- `a_op_sq_zero` : Proves that annihilation operator is square-zero.
- `aDag_op_sq_zero` : Proves that creation operator is square-zero.
- `local_car_identity` : Proves local Canonical Anticommutation Relations (CAR).
- `cantorState_hop_false_eq_create` : Connects local hop on false to matrix creation.
- `cantorState_hop_true_eq_annihilate` : Connects local hop on true to matrix annihilation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
- None.
-/
