/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SplitAtomDoubling.Basic
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.BottPeriodicity

/-! Split block doubling and the existing real matrix-model dimensions. -/

namespace InfoGeometry.Clifford.SplitAtomDoubling

/-- Size of a proposed matrix realization, not a new definition of Cl(n,n). -/
abbrev MatrixModel (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ

theorem matrixModel_finrank (n : ℕ) : Module.finrank ℝ (MatrixModel n) = 4 ^ n := by
  calc
    Module.finrank ℝ (MatrixModel n) = 2 ^ n * 2 ^ n := by
      simp [MatrixModel, Module.finrank_matrix]
    _ = (2 * 2) ^ n := (mul_pow 2 2 n).symm
    _ = 4 ^ n := by norm_num

theorem matrixModel_three_finrank : Module.finrank ℝ (MatrixModel 3) = 64 := by
  rw [matrixModel_finrank]; norm_num

theorem matrixModel_four_finrank : Module.finrank ℝ (MatrixModel 4) = 256 := by
  rw [matrixModel_finrank]; norm_num

end InfoGeometry.Clifford.SplitAtomDoubling
