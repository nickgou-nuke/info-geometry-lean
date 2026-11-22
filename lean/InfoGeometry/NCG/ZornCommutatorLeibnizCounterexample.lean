/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.ZornCommutator
import Mathlib.Tactic

/-!
# The full noncommutative Zorn commutator is not a product derivation

The inner commutator is a derivation on associative sectors, but not on the
full Zorn carrier. A concrete witness uses noncommuting coefficient
operators in `M₂(ℤ)` and gives a nonzero component of that defect.
-/

namespace InfoGeometry.NCG.ZornCommutatorLeibnizCounterexample

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.ZornCommutator

abbrev CoefficientOperator := Matrix (Fin 2) (Fin 2) ℤ

def e11 : CoefficientOperator := !![1, 0; 0, 0]
def e12 : CoefficientOperator := !![0, 1; 0, 0]

def diagonalOperator : OpZornMatrix CoefficientOperator :=
  ⟨e11, 0, 0, 0⟩

def upperXOperator (c : CoefficientOperator) : OpZornMatrix CoefficientOperator :=
  ⟨0, ⟨c, 0, 0⟩, 0, 0⟩

def upperYOperator (c : CoefficientOperator) : OpZornMatrix CoefficientOperator :=
  ⟨0, ⟨0, c, 0⟩, 0, 0⟩

/-- The failure of `ad X` to obey the product Leibniz rule. -/
def commutatorLeibnizDefect (X Y Z : OpZornMatrix CoefficientOperator) :
    OpZornMatrix CoefficientOperator :=
  opCommutator X (Y * Z) -
    (opCommutator X Y * Z + Y * opCommutator X Z)

/-- The coefficient operators are genuinely noncommuting. -/
theorem coefficient_operators_noncommute : e11 * e12 ≠ e12 * e11 := by
  decide

/-- Exact nonzero `.w.z` component of the full-carrier Leibniz defect. -/
theorem commutatorLeibnizDefect_component :
    (commutatorLeibnizDefect diagonalOperator
      (upperXOperator e11) (upperYOperator e12)).w.z = -(e12 + e12) := by
  decide

/-- The Zorn commutator inner action is not a product derivation on the full
operator-valued Zorn algebra, even with noncommutative matrix coefficients. -/
theorem commutator_not_product_derivation_on_full_operator_zorn :
    commutatorLeibnizDefect diagonalOperator
      (upperXOperator e11) (upperYOperator e12) ≠ 0 := by
  intro h
  have hcoord := congrArg
    (fun X : OpZornMatrix CoefficientOperator => X.w.z) h
  rw [commutatorLeibnizDefect_component] at hcoord
  have hentry := congrArg (fun M : CoefficientOperator => M 0 1) hcoord
  norm_num [e12] at hentry

end InfoGeometry.NCG.ZornCommutatorLeibnizCounterexample
