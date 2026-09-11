import InfoGeometry.OperatorAlgebra.SplitOctonionSymplecticFoundation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

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
