/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes

/-!
# A concrete obstruction to universal zero curvature

The two link-spin generators can act noncommutatively on the shared middle
corner. This finite matrix witness rules out an unconditional claim that their
inner derivations commute for every operator.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornSpinCurvatureCounterexample

open InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes

abbrev Op := Matrix (Fin 4) (Fin 4) ℚ

def unit (i j : Fin 4) : Op := Matrix.single i j 1

def e1 : Op := unit 0 0
def e2 : Op := unit 1 1 + unit 2 2
def e3 : Op := unit 3 3

def a12 : Op := unit 0 1
def c12 : Op := unit 1 0
def a23 : Op := unit 1 3
def c23 : Op := unit 3 1 + unit 3 2

def n12 : Op := root12 e1 e2 a12
def n21 : Op := root21 e2 e1 c12
def n23 : Op := root23 e2 e3 a23
def n32 : Op := root32 e3 e2 c23

def sigma12 : Op := n12 * n21 - n21 * n12
def sigma23 : Op := n23 * n32 - n32 * n23
def matrixComm (x y : Op) : Op := x * y - y * x

private theorem arrows_compute :
    n12 = unit 0 1 ∧ n21 = unit 1 0 ∧
    n23 = unit 1 3 ∧ n32 = unit 3 1 + unit 3 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [n12, n21, n23, n32, root12, root21, root23, root32,
        e1, e2, e3, a12, c12, a23, c23, unit, Matrix.mul_apply,
        Matrix.single_apply, Fin.sum_univ_four]

/-- The two actual link-spin generators have nonzero commutator in the
shared middle corner. Thus universal zero curvature cannot be inferred from
the three-corner path relations alone. -/
theorem link_spin_generators_do_not_commute :
    matrixComm sigma12 sigma23 = -(unit 1 2) := by
  rcases arrows_compute with ⟨h12, h21, h23, h32⟩
  dsimp only [matrixComm, sigma12, sigma23]
  rw [h12, h21, h23, h32]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unit, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]

/-- In particular, the commutator of the generators is nonzero. -/
theorem link_spin_generators_commutator_nonzero :
    matrixComm sigma12 sigma23 ≠ 0 := by
  rw [link_spin_generators_do_not_commute]
  intro h
  have hentry := congrFun (congrFun h 1) 2
  norm_num [unit, Matrix.single_apply] at hentry

/-- Typed existential witness on `Matrix (Fin 4) (Fin 4) ℚ`. -/
theorem link_spin_mat4q_noncomm_exists :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℚ, A * B ≠ B * A := by
  refine ⟨sigma12, sigma23, fun h => link_spin_generators_commutator_nonzero ?_⟩
  simp [matrixComm, h]

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornSpinCurvatureCounterexample
