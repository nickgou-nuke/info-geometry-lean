import Mathlib

/-!
# Odd nilpotent finite parity core

This file keeps only the finite arithmetic and algebraic facts that are proved
locally in Lean:

- parity flipping for a two-sector superspace,
- alternating parity bookkeeping for a finite block,
- direct square/readout consequences for square-zero elements.

It deliberately does not package an `osp(1|2)` embedding, a super
Jacobson--Morozov theorem, a CAR inductive-limit construction, a Cantor
homeomorphism, or an AQFT representation theorem as witness fields.  Those
claims need their own constructive owner modules.
-/

noncomputable section

namespace InfoGeometry.Algebraic.OddNilpotentOSpBridge

/-! ## 1. Finite parity vocabulary -/

/-- Two parity sectors of a finite superspace. -/
inductive SuperParity where
  | even
  | odd
  deriving DecidableEq, Repr

namespace SuperParity

/-- Flip even and odd parity. -/
def flip : SuperParity → SuperParity
  | even => odd
  | odd => even

@[simp]
theorem flip_even : flip even = odd := rfl

@[simp]
theorem flip_odd : flip odd = even := rfl

@[simp]
theorem flip_flip (p : SuperParity) : flip (flip p) = p := by
  cases p <;> rfl

end SuperParity

/-- Abstract vector superspace dimensions. -/
structure SuperDimension where
  /-- Even dimension. -/
  evenDim : ℕ
  /-- Odd dimension. -/
  oddDim : ℕ

/-- Super Jordan block descriptor. -/
structure SuperJordanBlock where
  /-- Length of the alternating-parity Jordan chain. -/
  size : ℕ
  /-- Positivity witness. -/
  size_pos : 0 < size

/-- A super Jordan block is admissible for `osp(1|2)` iff its size is odd. -/
def SuperJordanBlock.AdmissibleOdd (B : SuperJordanBlock) : Prop :=
  B.size % 2 = 1

namespace SuperJordanBlock

/--
Parity at a position in an alternating super Jordan block.

This is only the finite parity bookkeeping.  It does not construct a Jordan
normal form or a matrix representation.
-/
def parityAt (B : SuperJordanBlock) (start : SuperParity) (k : Fin B.size) :
    SuperParity :=
  if k.1 % 2 = 0 then start else start.flip

@[simp]
theorem parityAt_zero
    (B : SuperJordanBlock)
    (start : SuperParity)
    (hB : 0 < B.size) :
    B.parityAt start ⟨0, hB⟩ = start := by
  simp [parityAt]

@[simp]
theorem parityAt_zero_even
    (B : SuperJordanBlock)
    (hB : 0 < B.size) :
    B.parityAt SuperParity.even ⟨0, hB⟩ = SuperParity.even := by
  simp

/--
Admissibility is exactly the stored odd-size condition.

This readback keeps the paper's odd-block criterion as a finite arithmetic
predicate, without deriving an `osp(1|2)` embedding by itself.
-/
theorem admissibleOdd_iff
    (B : SuperJordanBlock) :
    B.AdmissibleOdd ↔ B.size % 2 = 1 :=
  Iff.rfl

end SuperJordanBlock

/-! ## 2. Odd square-zero readouts -/

/-- The square readout predicate for an operator-like element. -/
def IsSquareReadout {Op : Type*} [Mul Op] (e square : Op) : Prop :=
  e * e = square

/-- Square-zero predicate for an operator-like element. -/
def SquareZero {Op : Type*} [MulZeroClass Op] (e : Op) : Prop :=
  e * e = 0

/-- If the square readout is zero, then the element is square-zero. -/
theorem squareZero_of_squareReadout_eq_zero
    {Op : Type*} [MulZeroClass Op]
    {e square : Op}
    (hread : IsSquareReadout e square)
    (hsquare : square = 0) :
    SquareZero e := by
  simpa [SquareZero, IsSquareReadout, hsquare] using hread

/-- The square readout of a square-zero element is zero. -/
theorem squareReadout_eq_zero_of_squareZero
    {Op : Type*} [MulZeroClass Op]
    {e square : Op}
    (hread : IsSquareReadout e square)
    (hzero : SquareZero e) :
    square = 0 := by
  rw [← hread]
  exact hzero

/-- A square-zero element has zero fourth power, stated without a nilpotence packet. -/
theorem fourth_power_eq_zero_of_squareZero
    {Op : Type*} [NonUnitalNonAssocSemiring Op]
    {e : Op}
    (hzero : SquareZero e) :
    (e * e) * (e * e) = 0 := by
  simp [SquareZero] at hzero
  simp [hzero]

end InfoGeometry.Algebraic.OddNilpotentOSpBridge
