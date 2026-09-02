import Mathlib.Tactic
import InfoGeometry.Algebra.CircularChiralOperatorEightBridge
import InfoGeometry.Clifford.Cl55ZornCARComparison
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Physics.OperatorZornSoldering
import InfoGeometry.Physics.OperatorZornMatrixAlgebra

/-!
# Circular chiral rails in the native Fock / operator-Zorn carrier

This owner closes the relation-level second-quantized bridge for the six
circular null rails.  It does not identify the full non-associative Zorn
algebra with an associative operator algebra.

The source frame is the repository-owned circular chiral operator frame

`U 0, U 1, U 2, V 0, V 1, V 2`,

read through `CircularChiralOperatorEightBridge.operatorFrame`.  The target is
the native Jordan--Wigner Fock representation in `MatStage 5 = M_32(R)`, where

the three `U` / positive-root channels are represented by annihilation
operators and the three `V` / negative-root channels by creation operators.
This convention is exactly the one already used by `Cl55NambuZornPeirceBridge`:
`rootPlus` is the annihilation rail and `rootMinus` is the creation rail.

For each colour `c : Fin 3`, the selected pair is then soldered into the
existing associative `OperatorZornMatrix (MatStage 5)` Nambu--Gorkov shell.
-/

noncomputable section

namespace InfoGeometry.Physics.CircularChiralFockOperatorZornBridge

open InfoGeometry.Algebra.CircularChiralOperatorEightBridge
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Clifford.SplitClifford55ZornCARComparison
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Physics.OperatorZornMatrix

abbrev FockOp := InfoGeometry.Clifford.Cl11TensorTower.MatStage 5

/-- Index of the positive circular rail `U_i` in the named eight-frame. -/
def positiveFrameIndex (i : Fin 3) : Fin 8 :=
  ⟨i.1 + 1, by omega⟩

/-- Index of the negative circular rail `V_i` in the named eight-frame. -/
def negativeFrameIndex (i : Fin 3) : Fin 8 :=
  ⟨i.1 + 5, by omega⟩

/-- The positive circular rails in the named operator frame are exactly `U_i`. -/
@[simp] theorem operatorFrame_positiveRail (i : Fin 3) :
    operatorFrame (positiveFrameIndex i) = U i := by
  fin_cases i <;> rfl

/-- The negative circular rails in the named operator frame are exactly `V_i`. -/
@[simp] theorem operatorFrame_negativeRail (i : Fin 3) :
    operatorFrame (negativeFrameIndex i) = V i := by
  fin_cases i <;> rfl

/-- Native second-quantized readout of a positive circular/root-plus channel.
With the established Zorn/Fock CAR convention, positive roots are annihilation
operators. -/
def positiveRailFock (i : Fin 3) : FockOp :=
  f (firstThreeIndex i)

/-- Native second-quantized readout of a negative circular/root-minus channel.
With the established Zorn/Fock CAR convention, negative roots are creation
operators. -/
def negativeRailFock (i : Fin 3) : FockOp :=
  e (firstThreeIndex i)

/-- Positive Fock rails are nilpotent. -/
@[simp] theorem positiveRailFock_sq (i : Fin 3) :
    positiveRailFock i * positiveRailFock i = 0 := by
  exact f_sq (firstThreeIndex i)

/-- Negative Fock rails are nilpotent. -/
@[simp] theorem negativeRailFock_sq (i : Fin 3) :
    negativeRailFock i * negativeRailFock i = 0 := by
  exact e_sq (firstThreeIndex i)

/-- Same-polarity positive rails anticommute. -/
theorem positiveRailFock_anticomm (i j : Fin 3) :
    positiveRailFock i * positiveRailFock j +
      positiveRailFock j * positiveRailFock i = 0 := by
  exact f_anticomm (firstThreeIndex i) (firstThreeIndex j)

/-- Same-polarity negative rails anticommute. -/
theorem negativeRailFock_anticomm (i j : Fin 3) :
    negativeRailFock i * negativeRailFock j +
      negativeRailFock j * negativeRailFock i = 0 := by
  exact e_anticomm (firstThreeIndex i) (firstThreeIndex j)

/-- Mixed positive/negative rails satisfy the three-mode CAR delta law. -/
theorem positive_negativeRailFock_CAR (i j : Fin 3) :
    positiveRailFock i * negativeRailFock j +
      negativeRailFock j * positiveRailFock i =
        if i = j then (1 : FockOp) else 0 := by
  have h := ef_car (firstThreeIndex j) (firstThreeIndex i)
  rw [add_comm] at h
  by_cases hij : i = j
  · subst j
    simpa [positiveRailFock, negativeRailFock] using h
  · have hidx : firstThreeIndex j ≠ firstThreeIndex i := by
      intro hji
      exact hij (firstThreeIndex_injective hji.symm)
    simpa [positiveRailFock, negativeRailFock, hij, hidx] using h

/-- The second-quantized six-rail packet, with the two scalar pole slots left
zero because no canonical Fock representation of `E11/E22` is asserted by the
existing relation-level bridge. -/
def circularFockPacket : ChiralSigmaOperatorPacket FockOp where
  uPlus := 0
  uMinus := 0
  sigmaPlus := positiveRailFock
  sigmaMinus := negativeRailFock

/-- Colour selection is a concrete soldering map from the three circular rails
to one Nambu--Gorkov off-diagonal operator entry. -/
def colourSoldering (c : Fin 3) : ChiralSigmaSoldering FockOp FockOp where
  plus rail := rail c
  minus rail := rail c

/-- The selected circular colour pair in the associative operator-Zorn shell. -/
def circularColourOperatorZorn (c : Fin 3) : OperatorZornMatrix FockOp :=
  (colourSoldering c).toOperatorZornMatrix circularFockPacket

@[simp] theorem circularColourOperatorZorn_n_plus (c : Fin 3) :
    (circularColourOperatorZorn c).n_plus_op = 0 := rfl

@[simp] theorem circularColourOperatorZorn_n_minus (c : Fin 3) :
    (circularColourOperatorZorn c).n_minus_op = 0 := rfl

@[simp] theorem circularColourOperatorZorn_sigma_plus (c : Fin 3) :
    (circularColourOperatorZorn c).sigma_plus_op = positiveRailFock c := rfl

@[simp] theorem circularColourOperatorZorn_sigma_minus (c : Fin 3) :
    (circularColourOperatorZorn c).sigma_minus_op = negativeRailFock c := rfl

/-- Matrix readback of the selected second-quantized circular pair. -/
theorem circularColourOperatorZorn_toMatrix (c : Fin 3) :
    OperatorZornMatrix.toMatrix (circularColourOperatorZorn c) =
      !![0, positiveRailFock c; negativeRailFock c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Squaring the selected odd Nambu--Gorkov packet is purely even. -/
theorem circularColourOperatorZorn_square (c : Fin 3) :
    circularColourOperatorZorn c * circularColourOperatorZorn c =
      (⟨positiveRailFock c * negativeRailFock c,
        negativeRailFock c * positiveRailFock c, 0, 0⟩ :
        OperatorZornMatrix FockOp) := by
  apply (OperatorZornMatrix.equivMatrix (A := FockOp)).injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circularColourOperatorZorn, colourSoldering, circularFockPacket,
      OperatorZornMatrix.toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two even diagonal blocks of the square resolve the CAR identity. -/
theorem circularColourOperatorZorn_square_CAR (c : Fin 3) :
    (circularColourOperatorZorn c * circularColourOperatorZorn c).n_plus_op +
      (circularColourOperatorZorn c * circularColourOperatorZorn c).n_minus_op =
        (1 : FockOp) := by
  rw [circularColourOperatorZorn_square]
  exact positive_negativeRailFock_CAR c c

/-- Compact bridge statement: the named circular `U/V` rails and the selected
Fock operators have the same three-mode CAR routing, and the resulting pair is
an honest associative operator-Zorn/Nambu--Gorkov element. -/
theorem circular_chiral_fock_operatorZorn_packet (c : Fin 3) :
    operatorFrame (positiveFrameIndex c) = U c ∧
    operatorFrame (negativeFrameIndex c) = V c ∧
    positiveRailFock c * positiveRailFock c = 0 ∧
    negativeRailFock c * negativeRailFock c = 0 ∧
    positiveRailFock c * negativeRailFock c +
      negativeRailFock c * positiveRailFock c = (1 : FockOp) ∧
    OperatorZornMatrix.toMatrix (circularColourOperatorZorn c) =
      !![0, positiveRailFock c; negativeRailFock c, 0] := by
  exact ⟨operatorFrame_positiveRail c,
    operatorFrame_negativeRail c,
    positiveRailFock_sq c,
    negativeRailFock_sq c,
    positive_negativeRailFock_CAR c c,
    circularColourOperatorZorn_toMatrix c⟩

end InfoGeometry.Physics.CircularChiralFockOperatorZornBridge
