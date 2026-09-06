import InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
import InfoGeometry.Canonical.FiniteFibonacciElectronIndependence

/-!
# InfoGeometry.Canonical.FiniteFibonacciPailRopeQubits

Finite pail/rope computational-vector interface for Fibonacci anyons.

Section 8 names the two local computational blocks `(ε 0 ε)` and `(ε 1 ε)`
as triangular pails and double ropes.  The first and last Fibonacci fields are
inert endpoint maps, so after removing the redundant endpoint pairs an `N`-qubit
computational vector is just an `N`-bit string.

This file records that finite combinatorial content:

* pail/rope labels are equivalent to Boolean qubit bits;
* an `N`-qubit computational word is a finite pail/rope word of length `N`;
* there are `2^N` such words;
* adding/removing inert endpoints preserves the computational word;
* electron triples are ignored via the previously proved finite electron
  independence interface.

No conformal-block construction.
No projector algebra.
No analytic continuation.
No physical fault-tolerance theorem.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciPailRopeQubits

open InfoGeometry.Canonical.FiniteFibonacciComputationalSpace
open InfoGeometry.Canonical.FiniteFibonacciElectronIndependence

/-- The two local computational configurations: triangular pail and double rope. -/
inductive PailRope where
  /-- The `(ε 0 ε)` triangular pail, representing computational bit `0`. -/
  | pail
  /-- The `(ε 1 ε)` double rope, representing computational bit `1`. -/
  | rope
  deriving DecidableEq, Repr, Fintype

namespace PailRope

/-- Convert a Boolean computational bit to the corresponding pail/rope label. -/
def ofBool : Bool → PailRope
  | false => pail
  | true => rope

/-- Convert a pail/rope label to its Boolean computational bit. -/
def toBool : PailRope → Bool
  | pail => false
  | rope => true

@[simp]
theorem toBool_ofBool (b : Bool) :
    toBool (ofBool b) = b := by
  cases b <;> rfl

@[simp]
theorem ofBool_toBool (x : PailRope) :
    ofBool (toBool x) = x := by
  cases x <;> rfl

end PailRope

/-- Pail/rope labels are equivalent to computational bits. -/
def pailRopeEquivBool : PailRope ≃ Bool where
  toFun := PailRope.toBool
  invFun := PailRope.ofBool
  left_inv := PailRope.ofBool_toBool
  right_inv := PailRope.toBool_ofBool

/-- A finite pail/rope computational word for an `N`-qubit space. -/
abbrev PailRopeWord (N : ℕ) :=
  Fin N → PailRope

/-- Convert an `N`-bit computational vector to a pail/rope word. -/
def pailRopeWordOfBits {N : ℕ} (α : ComputationalVector N) : PailRopeWord N :=
  fun i => PailRope.ofBool (α i)

/-- Convert a pail/rope word to an `N`-bit computational vector. -/
def bitsOfPailRopeWord {N : ℕ} (w : PailRopeWord N) : ComputationalVector N :=
  fun i => PailRope.toBool (w i)

@[simp]
theorem bitsOfPailRopeWord_of_bits {N : ℕ} (α : ComputationalVector N) :
    bitsOfPailRopeWord (pailRopeWordOfBits α) = α := by
  funext i
  simp [bitsOfPailRopeWord, pailRopeWordOfBits]

@[simp]
theorem pailRopeWordOfBits_of_word {N : ℕ} (w : PailRopeWord N) :
    pailRopeWordOfBits (bitsOfPailRopeWord w) = w := by
  funext i
  simp [bitsOfPailRopeWord, pailRopeWordOfBits]

/-- Pail/rope words are equivalent to computational bit vectors. -/
def pailRopeWordEquivBits (N : ℕ) : PailRopeWord N ≃ ComputationalVector N where
  toFun := bitsOfPailRopeWord
  invFun := pailRopeWordOfBits
  left_inv := pailRopeWordOfBits_of_word
  right_inv := bitsOfPailRopeWord_of_bits

/-- There are exactly `2^N` pail/rope computational words. -/
theorem card_pailRopeWord (N : ℕ) :
    Fintype.card (PailRopeWord N) = 2 ^ N := by
  rw [Fintype.card_congr (pailRopeWordEquivBits N)]
  exact card_computationalVector N

/-- Add the inert endpoint pair to a pail/rope word as a finite list of sector labels. -/
def withInertEndpoints {N : ℕ} (w : PailRopeWord N) : List Bool :=
  [false, true] ++ (List.finRange N).map (fun i => PailRope.toBool (w i)) ++ [true, false]

/-- Remove inert endpoints from the finite list representation. -/
def withoutInertEndpoints {N : ℕ} (w : PailRopeWord N) : List Bool :=
  (List.finRange N).map (fun i => PailRope.toBool (w i))

/-- Adding inert endpoints increases the finite list length by four. -/
theorem withInertEndpoints_length {N : ℕ} (w : PailRopeWord N) :
    (withInertEndpoints w).length = N + 4 := by
  simp [withInertEndpoints]

/-- Removing inert endpoints leaves exactly the `N` computational labels. -/
theorem withoutInertEndpoints_length {N : ℕ} (w : PailRopeWord N) :
    (withoutInertEndpoints w).length = N := by
  simp [withoutInertEndpoints]

/-- The single-qubit pail represents `|0⟩`. -/
def oneQubitZero : PailRopeWord 1 :=
  fun _ => PailRope.pail

/-- The single-qubit rope represents `|1⟩`. -/
def oneQubitOne : PailRopeWord 1 :=
  fun _ => PailRope.rope

@[simp]
theorem oneQubitZero_bit :
    bitsOfPailRopeWord oneQubitZero 0 = false :=
  rfl

@[simp]
theorem oneQubitOne_bit :
    bitsOfPailRopeWord oneQubitOne 0 = true :=
  rfl

/-- The single-qubit pail/rope space has the expected two basis labels. -/
theorem card_oneQubitPailRope :
    Fintype.card (PailRopeWord 1) = 2 :=
  card_pailRopeWord 1

/-- Setting `r = 0` is harmless for the finite braid readout by electron independence. -/
theorem braidReadout_r_zero_reduction
    (r : ℕ) (q : Units ℂ) :
    fibonacciRMatrixWithElectrons r q = fibonacciRMatrixWithElectrons 0 q :=
  fibonacciRMatrixWithElectrons_independent_of_r r 0 q

end InfoGeometry.Canonical.FiniteFibonacciPailRopeQubits
