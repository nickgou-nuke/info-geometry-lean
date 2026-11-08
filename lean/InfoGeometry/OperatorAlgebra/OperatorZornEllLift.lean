/-
Operator-valued lift of the distinguished split direction `ell`.

The coefficient ring is arbitrary and may be noncommutative.  This owner
reuses the existing NC-Zorn carrier and product; it only replaces the scalar
coordinate `1` in the two matching colour slots by the coefficient-ring
identity.  No alternativity or global automorphism-group statement is added.
-/

import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.OperatorAlgebra.OperatorZornEllLift

open InfoGeometry.Canonical
open InfoGeometry.Physics.NCG

abbrev OperatorVector (A : Type*) [Ring A] := Fin 3 → A
abbrev OperatorZorn (A : Type*) [Ring A] := OperatorZornMatrix A

variable {A : Type*} [Ring A]

def axisZero (A : Type*) [Ring A] : OperatorVector A :=
  fun i => if i = 0 then 1 else 0

def operatorEll (A : Type*) [Ring A] : OperatorZorn A :=
  chiralOperatorZorn (axisZero A) (axisZero A)

def operatorIdentity (A : Type*) [Ring A] : OperatorZorn A :=
  operatorZornCoordinates 1 1 (fun _ => 0) (fun _ => 0)

@[simp] theorem axisZero_zero : axisZero (A := A) 0 = 1 := by
  simp [axisZero]

@[simp] theorem axisZero_one : axisZero (A := A) 1 = 0 := by
  simp [axisZero]

@[simp] theorem axisZero_two : axisZero (A := A) 2 = 0 := by
  simp [axisZero]

theorem operatorEll_mul_self :
    operatorZornMul (operatorEll (A := A)) (operatorEll (A := A)) =
      operatorIdentity (A := A) := by
  rw [operatorEll, operatorZornMul_chiralOperatorZorn]
  apply operatorZornMatrix_ext
  · simp [operatorIdentity, operatorZornCoordinates, operatorDot,
      NCZornElement.zornDot, axisZero]
  · simp [operatorIdentity, operatorZornCoordinates, operatorDot,
      NCZornElement.zornDot, axisZero]
  · funext i
    fin_cases i <;>
      simp [operatorIdentity, operatorZornCoordinates, operatorCross,
        NCZornElement.zornCross, axisZero]
  · funext i
    fin_cases i <;>
      simp [operatorIdentity, operatorZornCoordinates, operatorCross,
        NCZornElement.zornCross, axisZero]

end InfoGeometry.OperatorAlgebra.OperatorZornEllLift
