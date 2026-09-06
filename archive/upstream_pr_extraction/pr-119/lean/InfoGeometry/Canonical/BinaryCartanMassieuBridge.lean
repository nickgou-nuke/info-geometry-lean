import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import InfoGeometry.Algebraic.CartanExponentialFamily

/-!
# Binary Cartan Massieu specialization

The two-state Cartan chart with parameters `a * u` and `-(a * u)` has
partition function `2 * cosh (a * u)`.  This file is only the finite
specialization of the existing `CartanExponentialFamily` definitions; it does
not assert a derivative, a thermodynamic limit, or an operator exponential.
-/

noncomputable section

namespace InfoGeometry.Canonical.BinaryCartanMassieuBridge

open InfoGeometry.Algebraic.CartanExponentialFamily
open scoped BigOperators

abbrev BinaryIndex := Fin 2

def binaryParameters (a u : ℝ) : BinaryIndex → ℝ :=
  ![a * u, -(a * u)]

theorem binaryParameters_zero (a u : ℝ) :
    binaryParameters a u 0 = a * u := by
  rfl

theorem binaryParameters_one (a u : ℝ) :
    binaryParameters a u 1 = -(a * u) := by
  rfl

theorem binaryPartition_eq_two_mul_cosh (a u : ℝ) :
    Z (binaryParameters a u) = 2 * Real.cosh (a * u) := by
  unfold Z binaryParameters
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Real.cosh_eq]
  ring

theorem binaryPartition_pos (a u : ℝ) :
    0 < Z (binaryParameters a u) := by
  exact Z_pos (binaryParameters a u)

theorem binaryMassieu_eq_log_two_mul_cosh (a u : ℝ) :
    Phi (binaryParameters a u) = Real.log (2 * Real.cosh (a * u)) := by
  rw [Phi, binaryPartition_eq_two_mul_cosh]

theorem binaryPartition_neg_eq (a u : ℝ) :
    Z (binaryParameters a (-u)) = Z (binaryParameters a u) := by
  rw [binaryPartition_eq_two_mul_cosh, binaryPartition_eq_two_mul_cosh]
  have h : a * -u = -(a * u) := by ring
  rw [h, Real.cosh_neg]

theorem binaryMassieu_neg_eq (a u : ℝ) :
    Phi (binaryParameters a (-u)) = Phi (binaryParameters a u) := by
  rw [binaryMassieu_eq_log_two_mul_cosh,
    binaryMassieu_eq_log_two_mul_cosh]
  have h : a * -u = -(a * u) := by ring
  rw [h, Real.cosh_neg]

end InfoGeometry.Canonical.BinaryCartanMassieuBridge
