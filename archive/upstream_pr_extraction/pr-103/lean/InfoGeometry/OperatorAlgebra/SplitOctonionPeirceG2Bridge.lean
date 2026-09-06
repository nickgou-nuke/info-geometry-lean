import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.OperatorAlgebra.SplitOctonions.IntegerOrder
import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

/-!
# Peirce-Witt atoms to the finite `G₂(2)` coordinate lane

This module is the Lean twin of
`tools/sympy/split_octonion_peirce_g2_bridge.py`.

It connects the integer split-octonion Peirce-Witt/symplectic atoms to the
`F₂` Zorn coordinates used by the finite `G₂(2)` automorphism verifier.

#### BUCKET 1: CLOSED FINITE THEOREMS

* The integer atoms `oneZ`, `H`, `ePlus`, `eMinus`, `up_i`, and `down_i`
  reduce modulo two to the corresponding `F₂` split-octonion atoms.
* The integer commutator `[up_i, down_i] = H` and anticommutator
  `{up_i, down_i} = oneZ` both reduce to the same diagonal `F₂` unit.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not prove Cuntz representation closure, wallpaper symmetry
forcing, braid coherence, or a global real automorphism classification.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonionPeirceG2Bridge

abbrev IntSplitOct := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct
abbrev F2Bit := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.F2Bit
abbrev F2SplitOct := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2

abbrev intOneZ : IntSplitOct := InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation.oneZ
abbrev intH : IntSplitOct := InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation.H
abbrev intEPlus : IntSplitOct := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.ePlus
abbrev intEMinus : IntSplitOct := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.eMinus
abbrev intUp : Fin 3 → IntSplitOct := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.up
abbrev intDown : Fin 3 → IntSplitOct := InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.down
abbrev intCommZ (X Y : IntSplitOct) : IntSplitOct :=
  InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation.commZ X Y
abbrev intAntiCommZ (X Y : IntSplitOct) : IntSplitOct :=
  InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation.antiCommZ X Y

abbrev f2One : F2SplitOct := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one
abbrev f2EPlus : F2SplitOct := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.ePlus
abbrev f2EMinus : F2SplitOct := InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.eMinus

def f2Up : Fin 3 → F2SplitOct
  | 0 => InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.up0
  | 1 => InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.up1
  | 2 => InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.up2

def f2Down : Fin 3 → F2SplitOct
  | 0 => InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.down0
  | 1 => InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.down1
  | 2 => InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.down2

/-- Coordinate parity map from integer Zorn coordinates to the Boolean `F₂` carrier. -/
def parityBit (z : ℤ) : F2Bit := decide (z % 2 != 0)

/-- Reduce an integer split-octonion coordinate cell modulo two. -/
def reduceZToF2 (X : IntSplitOct) : F2SplitOct :=
  ⟨parityBit X.a, parityBit X.b, parityBit X.x0, parityBit X.x1, parityBit X.x2,
    parityBit X.y0, parityBit X.y1, parityBit X.y2⟩

/-! The coordinate reduction is parity, so its Boolean operations are the
    characteristic-two shadows of the integer operations.  These local
    lemmas are the reusable arithmetic edge for the later Zorn-product
    compatibility theorem. -/

theorem parityBit_add (m n : ℤ) :
    parityBit (m + n) = Bool.xor (parityBit m) (parityBit n) := by
  rcases Int.emod_two_eq_zero_or_one m with hm | hm <;>
    rcases Int.emod_two_eq_zero_or_one n with hn | hn <;>
    simp [parityBit, hm, hn, Int.add_emod]

theorem int_mul_emod_two (m n : ℤ) :
    (m * n) % 2 = ((m % 2) * (n % 2)) % 2 := by
  exact Int.mul_emod m n 2

theorem parityBit_mul (m n : ℤ) :
    parityBit (m * n) = (parityBit m && parityBit n) := by
  rcases Int.emod_two_eq_zero_or_one m with hm | hm <;>
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
  all_goals
    unfold parityBit
    rw [int_mul_emod_two, hm, hn]
    decide

/-! The canonical ring-valued reduction.  The Boolean readout above is useful
    for the existing finite tables, while this map is the correct carrier for
    transporting the full integer Zorn multiplication. -/

def modTwo (m : ℤ) : ZMod 2 := Int.castRingHom (ZMod 2) m

@[simp] theorem modTwo_add (m n : ℤ) :
    modTwo (m + n) = modTwo m + modTwo n := by
  exact (Int.castRingHom (ZMod 2)).map_add m n

@[simp] theorem modTwo_mul (m n : ℤ) :
    modTwo (m * n) = modTwo m * modTwo n := by
  exact (Int.castRingHom (ZMod 2)).map_mul m n

@[simp] theorem modTwo_neg (m : ℤ) :
    modTwo (-m) = -modTwo m := by
  exact (Int.castRingHom (ZMod 2)).map_neg m

@[simp] theorem modTwo_sub (m n : ℤ) :
    modTwo (m - n) = modTwo m - modTwo n := by
  exact (Int.castRingHom (ZMod 2)).map_sub m n

theorem boolToZMod_parityBit (m : ℤ) :
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.boolToZMod
        (parityBit m) = modTwo m := by
  change InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.boolToZMod
      (parityBit m) = (m : ZMod 2)
  rw [← ZMod.intCast_mod m 2]
  rcases Int.emod_two_eq_zero_or_one m with hm | hm
  · simp [parityBit,
      InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.boolToZMod, hm]
  · simp [parityBit,
      InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.boolToZMod, hm]

open InfoGeometry.Algebra.Zorn.Concrete

def intToZornCell (X : IntSplitOct) : ZornCell (ZMod 2) where
  r := modTwo X.a
  s := modTwo X.b
  x1 := modTwo X.x0
  x2 := modTwo X.x1
  x3 := modTwo X.x2
  y1 := modTwo X.y0
  y2 := modTwo X.y1
  y3 := modTwo X.y2

theorem intToZornCell_reduceZToF2 (X : IntSplitOct) :
    intToZornCell X =
      InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell
        (reduceZToF2 X) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  simp [intToZornCell, reduceZToF2,
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell,
    boolToZMod_parityBit]

theorem intToZornCell_zero :
    intToZornCell (0 : IntSplitOct) =
      (⟨0, 0, 0, 0, 0, 0, 0, 0⟩ : ZornCell (ZMod 2)) := by
  rfl

theorem intToZornCell_add (X Y : IntSplitOct) :
    intToZornCell (X + Y) =
      ZornCell.addZ (intToZornCell X) (intToZornCell Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨c, d, u0, u1, u2, v0, v1, v2⟩
  simp [intToZornCell, ZornCell.addZ,
    modTwo_add]

theorem intToZornCell_mul (X Y : IntSplitOct) :
    intToZornCell (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.mulZ X Y) =
      ZornCell.mulZ (intToZornCell X) (intToZornCell Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨c, d, u0, u1, u2, v0, v1, v2⟩
  simp [InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.mulZ,
    intToZornCell, ZornCell.mulZ, modTwo_add, modTwo_mul, modTwo_sub]
  ring_nf
  simp

theorem reduceZToF2_mul (X Y : IntSplitOct) :
    reduceZToF2 (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.mulZ X Y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        (reduceZToF2 X) (reduceZToF2 Y) := by
  apply (InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.splitOctF2ZornCellEquiv).injective
  change InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell
      (reduceZToF2
        (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.mulZ X Y)) =
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell
      (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.mul
        (reduceZToF2 X) (reduceZToF2 Y))
  rw [InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell_mul]
  rw [← intToZornCell_reduceZToF2 X,
    ← intToZornCell_reduceZToF2 Y,
    ← intToZornCell_reduceZToF2 (InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.mulZ X Y)]
  exact intToZornCell_mul X Y

theorem reduceZToF2_add (X Y : IntSplitOct) :
    reduceZToF2 (X + Y) =
      InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
        (reduceZToF2 X) (reduceZToF2 Y) := by
  apply (InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.splitOctF2ZornCellEquiv).injective
  change InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell
      (reduceZToF2 (X + Y)) =
    InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell
      (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add
        (reduceZToF2 X) (reduceZToF2 Y))
  rw [InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge.toZornCell_add]
  rw [← intToZornCell_reduceZToF2 X,
    ← intToZornCell_reduceZToF2 Y,
    ← intToZornCell_reduceZToF2 (X + Y)]
  exact intToZornCell_add X Y

theorem reduce_oneZ : reduceZToF2 intOneZ = f2One := by
  decide

theorem reduce_H : reduceZToF2 intH = f2One := by
  decide

theorem reduce_ePlus : reduceZToF2 intEPlus = f2EPlus := by
  decide

theorem reduce_eMinus : reduceZToF2 intEMinus = f2EMinus := by
  decide

theorem reduce_up (i : Fin 3) : reduceZToF2 (intUp i) = f2Up i := by
  fin_cases i <;> decide

theorem reduce_down (i : Fin 3) : reduceZToF2 (intDown i) = f2Down i := by
  fin_cases i <;> decide

theorem reduce_comm_up_down (i : Fin 3) :
    reduceZToF2 (intCommZ (intUp i) (intDown i)) = f2One := by
  fin_cases i <;> decide

theorem reduce_anticomm_up_down (i : Fin 3) :
    reduceZToF2 (intAntiCommZ (intUp i) (intDown i)) = f2One := by
  fin_cases i <;> decide

end InfoGeometry.OperatorAlgebra.SplitOctonionPeirceG2Bridge
