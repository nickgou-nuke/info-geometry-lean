/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.ZornCommutator
import InfoGeometry.NCG.ZornCommutatorLeibnizCounterexample
import Mathlib.Tactic

/-!
# Left regular multiplication on operator-valued Zorn matrices

For the actual `OpZornMatrix A` multiplication, the defect of composing left
multiplication operators is exactly the negative associator. The criterion is
proved for arbitrary coefficient rings; a matrix-coefficient witness shows
that the operator lift is not multiplicative on the full nonassociative
carrier.
-/

namespace InfoGeometry.NCG.ZornLeftRegularOperatorDefect

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.ZornCommutator
open InfoGeometry.NCG.ZornCommutatorLeibnizCounterexample

variable {A : Type*} [Ring A]

/-- Left multiplication as an operator on the additive carrier. -/
def leftZornOperator (X : OpZornMatrix A) : OpZornMatrix A → OpZornMatrix A :=
  fun Y => X * Y

/-- Pointwise defect between composing left multiplications and multiplying
their Zorn labels first. -/
def leftZornProductDefect (X Y Z : OpZornMatrix A) : OpZornMatrix A :=
  leftZornOperator X (leftZornOperator Y Z) - leftZornOperator (X * Y) Z

/-- The operator-composition defect is precisely the negative Zorn
associator, with the ambient multiplication order preserved. -/
theorem leftZornProductDefect_eq_neg_associator
    (X Y Z : OpZornMatrix A) :
    leftZornProductDefect X Y Z = -opAssociator X Y Z := by
  ext <;> simp [leftZornProductDefect, leftZornOperator, opAssociator]

/-- For a fixed pair, composition of left multiplication agrees with left
multiplication by the product exactly when its associator vanishes on every
right input. -/
theorem leftZornOperator_comp_eq_iff_associator_eq_zero
    (X Y : OpZornMatrix A) :
    (leftZornOperator X ∘ leftZornOperator Y) =
        leftZornOperator (X * Y) ↔
      ∀ Z, opAssociator X Y Z = 0 := by
  constructor
  · intro h Z
    have hZ := congrFun h Z
    change X * (Y * Z) = (X * Y) * Z at hZ
    change (X * Y) * Z - X * (Y * Z) = 0
    exact sub_eq_zero.mpr hZ.symm
  · intro h
    funext Z
    have hZ := h Z
    change (X * Y) * Z - X * (Y * Z) = 0 at hZ
    change X * (Y * Z) = (X * Y) * Z
    exact (sub_eq_zero.mp hZ).symm

section MatrixOperatorWitness

abbrev CoefficientOperator := Matrix (Fin 2) (Fin 2) ℤ

theorem operatorZorn_associator_component_ne_zero :
    (opAssociator diagonalOperator (upperXOperator e11)
      (upperYOperator e12)).w.z ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : CoefficientOperator => M 0 1)
    h
  norm_num [opAssociator, diagonalOperator, upperXOperator, upperYOperator,
    e11, e12, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale] at hentry

/-- Left regular multiplication is not a multiplicative representation on
the full operator-valued Zorn algebra over the genuinely noncommutative
coefficient ring `M₂(ℤ)`. -/
theorem leftZornOperator_comp_not_mul_label :
    (leftZornOperator diagonalOperator ∘ leftZornOperator (upperXOperator e11)) ≠
      leftZornOperator (diagonalOperator * upperXOperator e11) := by
  intro h
  have hZ := congrFun h (upperYOperator e12)
  change diagonalOperator * (upperXOperator e11 * upperYOperator e12) =
    (diagonalOperator * upperXOperator e11) * upperYOperator e12 at hZ
  have hassoc : opAssociator diagonalOperator (upperXOperator e11)
      (upperYOperator e12) = 0 := by
    change (diagonalOperator * upperXOperator e11) * upperYOperator e12 -
      diagonalOperator * (upperXOperator e11 * upperYOperator e12) = 0
    exact sub_eq_zero.mpr hZ.symm
  have hcoord := congrArg (fun T : OpZornMatrix CoefficientOperator => T.w.z) hassoc
  exact operatorZorn_associator_component_ne_zero hcoord

end MatrixOperatorWitness

end InfoGeometry.NCG.ZornLeftRegularOperatorDefect
