/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.ZornCommutator
import Mathlib.Tactic

/-!
# A noncommutative operator witness for failure of the Zorn commutator Jacobi identity

The carrier is the repository's `OpZornMatrix` over the genuinely
noncommutative coefficient operator ring `M₂(ℤ)`. This is a concrete
counterexample to a Lie bracket structure on the full operator-valued Zorn
carrier; the sector-restricted Lie theorems are unaffected.
-/

namespace InfoGeometry.NCG.ZornCommutatorJacobiCounterexample

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.ZornCommutator

abbrev CoefficientOperator := Matrix (Fin 2) (Fin 2) ℤ

def e11 : CoefficientOperator := !![1, 0; 0, 0]
def e12 : CoefficientOperator := !![0, 1; 0, 0]
def e21 : CoefficientOperator := !![0, 0; 1, 0]

def upperX (c : CoefficientOperator) : OpZornMatrix CoefficientOperator :=
  ⟨0, ⟨c, 0, 0⟩, 0, 0⟩

def upperY (c : CoefficientOperator) : OpZornMatrix CoefficientOperator :=
  ⟨0, ⟨0, c, 0⟩, 0, 0⟩

def lowerX (c : CoefficientOperator) : OpZornMatrix CoefficientOperator :=
  ⟨0, 0, ⟨c, 0, 0⟩, 0⟩

/-- The coefficient matrix units really fail to commute. -/
theorem coefficient_units_noncommute : e11 * e21 ≠ e21 * e11 := by
  decide

/-- Exact nonzero `v.y` component of the commutator Jacobiator on three
matrix-operator-supported Zorn elements. -/
theorem jacobiator_component :
    (zornJacobiator (upperX e11) (upperY e21) (lowerX e12)).v.y =
      !![-3, 0; 0, -4] := by
  decide

/-- The full operator-valued Zorn commutator does not satisfy Jacobi on all
triples, even with genuinely noncommuting matrix coefficients. -/
theorem commutator_not_jacobi_on_full_operator_zorn :
    zornJacobiator (upperX e11) (upperY e21) (lowerX e12) ≠ 0 := by
  intro h
  have hy := congrArg (fun X : OpZornMatrix CoefficientOperator => X.v.y) h
  rw [jacobiator_component] at hy
  have h00 := congrArg (fun M : CoefficientOperator => M 0 0) hy
  norm_num at h00

/-- Consequently the commutator Jacobi identity cannot hold universally on
the full operator-valued Zorn carrier. -/
theorem not_universally_jacobi :
    ¬ ∀ X Y Z : OpZornMatrix CoefficientOperator,
      zornJacobiator X Y Z = 0 := by
  intro h
  exact commutator_not_jacobi_on_full_operator_zorn (h _ _ _)

end InfoGeometry.NCG.ZornCommutatorJacobiCounterexample
