import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace SarsSU5Cl55Supertrace

open Matrix

abbrev M16R := InfoGeometry.Algebra.FiniteSpin.Mat16R
abbrev M32SplitR := InfoGeometry.Algebra.FiniteSpin.Mat32SplitR

def Gamma32 : M32SplitR := !![(1 : M16R), 0; 0, -(1 : M16R)]

def blockTrace32 (A : M32SplitR) : ℝ := Matrix.trace (A 0 0) + Matrix.trace (A 1 1)

def superTrace32 (A : M32SplitR) : ℝ := blockTrace32 (Gamma32 * A)

def comm2 (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := A * B - B * A

inductive Z2Parity where
  | even | odd
  deriving DecidableEq, Repr

def superBracketTarget : Z2Parity → Z2Parity → Z2Parity
  | Z2Parity.even, Z2Parity.even => Z2Parity.even
  | Z2Parity.even, Z2Parity.odd => Z2Parity.odd
  | Z2Parity.odd, Z2Parity.even => Z2Parity.odd
  | Z2Parity.odd, Z2Parity.odd => Z2Parity.even

@[simp] theorem Gamma32_sq : Gamma32 * Gamma32 = (1 : M32SplitR) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gamma32, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem blockTrace32_one : blockTrace32 (1 : M32SplitR) = 32 := by
  norm_num [blockTrace32, Matrix.trace]

@[simp] theorem blockTrace32_Gamma32 : blockTrace32 Gamma32 = 0 := by
  norm_num [blockTrace32, Gamma32, Matrix.trace]

@[simp] theorem superTrace32_one : superTrace32 (1 : M32SplitR) = 0 := by
  simp [superTrace32]

theorem cl55_volume_square_sign :
    (-1 : ℤ) ^ (10 * 9 / 2) * (-1 : ℤ) ^ 5 = 1 := by
  norm_num

theorem su5_exterior_square_dimension : Nat.choose 5 2 = 10 := by
  norm_num [Nat.choose]

theorem su5_adjoint_dimension : 5^2 - 1 = 24 := by
  norm_num

theorem so10_adjoint_dimension : 10 * (10 - 1) / 2 = 45 := by
  norm_num

theorem sm_subalgebra_dimension : (3^2 - 1) + (2^2 - 1) + 1 = 12 := by
  norm_num

theorem su5_broken_dimension : (5^2 - 1) - ((3^2 - 1) + (2^2 - 1) + 1) = 12 := by
  norm_num

theorem spinor_16_16_supertrace_balance : (16 : ℤ) - 16 = 0 := by
  norm_num

theorem exterior_algebra_C5_dimension :
    (Finset.univ.sum (fun k : Fin 6 => Nat.choose 5 k)) = 32 := by
  norm_num [Fin.sum_univ_six, Nat.choose]

theorem sars_scalar_five_fundamentals_dimension : 5 * 5 = 25 := by
  norm_num

theorem sars_scalar_not_su5_adjoint_dimension : 5 * 5 ≠ 5^2 - 1 := by
  norm_num

theorem sars_scalar_adjoint_dimension_gap : 5 * 5 - (5^2 - 1) = 1 := by
  norm_num

theorem su5_adjoint_not_sars_scalar_dimension : 5^2 - 1 ≠ 5 * 5 := by
  norm_num

theorem su5_adjoint_breaks_to_sm_dimension_gap :
    (5^2 - 1) - ((3^2 - 1) + (2^2 - 1) + 1) = 12 := by
  norm_num

theorem cl55_matrix_algebra_dimension : 32 * 32 = 2^10 := by
  norm_num

theorem cl55_even_odd_spinor_balance : 2^4 = 16 ∧ 2^4 + 2^4 = 32 := by
  norm_num

theorem odd_odd_superbracket_lands_even :
    superBracketTarget Z2Parity.odd Z2Parity.odd = Z2Parity.even := by
  rfl

theorem trace_commutator_M2_zero (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (comm2 A B) = 0 := by
  unfold comm2
  rw [Matrix.trace_sub, Matrix.trace_mul_comm A B]
  simp

end SarsSU5Cl55Supertrace

end noncomputable section
