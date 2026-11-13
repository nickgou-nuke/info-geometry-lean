/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.LinearAlgebra.FiniteRealAnticommutation
import Mathlib.Data.Matrix.Composition
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Reversing symmetries and the external-index boundary

The real matrices `S = diag(2,-2,0)` and the coordinate swap `J` satisfy
`J² = 1` and `J S = -S J`, while `S³ ≠ S`. Odd-dimensional reversal therefore
does not normalize the nonzero spectrum to `±1`.

An odd external matrix index is a different issue: `M₃(M₂(ℝ))` contains an
invertible anticommuting pair. Its actual native block-flattening equivalence
acts on a six-dimensional real space. The coefficient matrices and the
flattening map retain their complete noncommutative multiplication.
-/

noncomputable section

namespace InfoGeometry.Clifford.GradedUnrollingCounterexamples

open InfoGeometry.LinearAlgebra.FiniteRealAnticommutation
open InfoGeometry.Clifford.Cl11Matrix

section Reversal

/-- An unnormalized singular spectrum with a nontrivial reversed pair. -/
def reversedSpectrum : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 0, 0; 0, -2, 0; 0, 0, 0]

/-- Swap the two nonzero spectral coordinates and fix the zero coordinate. -/
def reversingSwap : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem reversingSwap_square : reversingSwap * reversingSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reversingSwap, Matrix.mul_apply, Fin.sum_univ_succ]

theorem reversingSwap_isUnit : IsUnit reversingSwap :=
  ⟨⟨reversingSwap, reversingSwap, reversingSwap_square, reversingSwap_square⟩, rfl⟩

theorem reversingSwap_anticommutes :
    reversingSwap * reversedSpectrum = -(reversedSpectrum * reversingSwap) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reversingSwap, reversedSpectrum, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The general odd-dimensional obstruction applies to the actual reversed matrix. -/
theorem reversedSpectrum_det_zero : reversedSpectrum.det = 0 :=
  det_eq_zero_of_odd_of_isUnit reversingSwap_anticommutes (by norm_num) reversingSwap_isUnit

/-- Reversal leaves the nonzero scale free, so it does not imply tripotence. -/
theorem reversedSpectrum_not_tripotent : reversedSpectrum ^ 3 ≠ reversedSpectrum := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  norm_num [reversedSpectrum, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] at h00

/-- The nonzero reversed spectral pair yields genuinely noncommuting operators. -/
theorem reversingSwap_noncommuting :
    reversingSwap * reversedSpectrum ≠ reversedSpectrum * reversingSwap := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  norm_num [reversingSwap, reversedSpectrum, Matrix.mul_apply, Fin.sum_univ_succ] at h01

end Reversal

section CoefficientAlgebra

abbrev Block3 := Matrix (Fin 3) (Fin 3) Mat2
abbrev Real6 := Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ

/-- Native flattening, with both external and coefficient indices retained. -/
def blockFlatten : Block3 ≃ₐ[ℝ] Real6 :=
  Matrix.compAlgEquiv (Fin 3) (Fin 2) ℝ ℝ

@[simp] theorem blockFlatten_apply (M : Block3) (i j : Fin 3) (a b : Fin 2) :
    blockFlatten M (i, a) (j, b) = M i j a b := rfl

/-- Repeat the positive split-Clifford generator in all three coefficient blocks. -/
def blockPositive : Block3 := Matrix.diagonal fun _ => Eplus

/-- Repeat the independent split-Clifford volume in the same coefficient blocks. -/
def blockSwap : Block3 := Matrix.diagonal fun _ => J1

theorem blockPositive_square : blockPositive * blockPositive = 1 := by
  simp [blockPositive, Matrix.diagonal_mul_diagonal, Eplus_sq]

theorem blockSwap_square : blockSwap * blockSwap = 1 := by
  simp [blockSwap, Matrix.diagonal_mul_diagonal, J1_sq]

theorem blockPositive_isUnit : IsUnit blockPositive :=
  ⟨⟨blockPositive, blockPositive, blockPositive_square, blockPositive_square⟩, rfl⟩

theorem blockSwap_isUnit : IsUnit blockSwap :=
  ⟨⟨blockSwap, blockSwap, blockSwap_square, blockSwap_square⟩, rfl⟩

private theorem positive_swap_anticommutes : Eplus * J1 = -(J1 * Eplus) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Eplus, J1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The external index is odd, yet the coefficient-valued matrices anticommute. -/
theorem blockPositive_blockSwap_anticommutes :
    blockPositive * blockSwap = -(blockSwap * blockPositive) := by
  calc
    blockPositive * blockSwap = Matrix.diagonal (fun _ : Fin 3 => Eplus * J1) :=
      Matrix.diagonal_mul_diagonal _ _
    _ = Matrix.diagonal (fun _ : Fin 3 => -(J1 * Eplus)) := by
      simp only [positive_swap_anticommutes]
    _ = -(Matrix.diagonal (fun _ : Fin 3 => J1 * Eplus)) := Matrix.diagonal_neg _
    _ = -(blockSwap * blockPositive) := by
      rw [blockSwap, blockPositive, Matrix.diagonal_mul_diagonal]

/-- Noncommutativity is witnessed by a concrete entry of a coefficient block. -/
theorem blockPositive_blockSwap_noncommuting :
    blockPositive * blockSwap ≠ blockSwap * blockPositive := by
  intro h
  have h01 := congrArg (fun M : Block3 => M 0 0 0 1) h
  norm_num [blockPositive, blockSwap, Matrix.diagonal_mul_diagonal,
    Eplus, J1, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Flattening transports the ordered anticommutation identity. -/
theorem flattened_anticommutes :
    blockFlatten blockPositive * blockFlatten blockSwap =
      -(blockFlatten blockSwap * blockFlatten blockPositive) := by
  simpa only [map_mul, map_neg] using
    congrArg blockFlatten blockPositive_blockSwap_anticommutes

theorem flattened_positive_isUnit : IsUnit (blockFlatten blockPositive) :=
  IsUnit.map blockFlatten blockPositive_isUnit

theorem flattened_swap_isUnit : IsUnit (blockFlatten blockSwap) :=
  IsUnit.map blockFlatten blockSwap_isUnit

/-- The represented real space has six coordinates, not three. -/
theorem flattened_index_card : Fintype.card (Fin 3 × Fin 2) = 6 := by
  norm_num

end CoefficientAlgebra

end InfoGeometry.Clifford.GradedUnrollingCounterexamples
