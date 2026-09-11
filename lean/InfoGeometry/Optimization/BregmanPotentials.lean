/- Bregman Potentials and Matrix Itakura-Saito Divergence -/
/- Implements the Matrix Burg Potential (-log det) and its Bregman 
   divergence (Matrix Itakura-Saito / Stein Loss). -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith

open Matrix
open scoped Matrix

namespace InfoGeometry.Optimization

variable {n : Type*} [Fintype n] [DecidableEq n]

/- 
  The Matrix Burg Potential: Ψ(X) = -log det(X). 
  This acts as the self-concordant log-barrier on the positive-definite cone.
-/
noncomputable def MatrixBurgPotential (X : Matrix n n ℝ) : ℝ :=
  -Real.log (det X)

/- 
  The Matrix Itakura-Saito Divergence (Stein Loss) generated as the 
  Bregman divergence of the Matrix Burg Potential.
-/
noncomputable def MatrixItakuraSaitoDivergence (X Y : Matrix n n ℝ) (hY : Matrix.det Y ≠ 0) : ℝ :=
  let Y_inv := Y⁻¹
  let n_card := (Fintype.card n : ℝ)
  trace (X * Y_inv) - Real.log (det (X * Y_inv)) - n_card

/-- The Matrix Itakura-Saito divergence vanishes on the diagonal of its
invertible domain. -/
theorem itakura_saito_self_eq_zero (X : Matrix n n ℝ) (hX : det X ≠ 0) :
    MatrixItakuraSaitoDivergence X X hX = 0 := by
  have hunit : IsUnit X.det := isUnit_iff_ne_zero.mpr hX
  simp [MatrixItakuraSaitoDivergence, Matrix.mul_nonsing_inv X hunit]

/-- The self-divergence is nonnegative because it is exactly zero. -/
theorem itakura_saito_self_nonneg (X : Matrix n n ℝ) (hX : det X ≠ 0) :
    0 ≤ MatrixItakuraSaitoDivergence X X hX := by
  rw [itakura_saito_self_eq_zero X hX]

end InfoGeometry.Optimization
