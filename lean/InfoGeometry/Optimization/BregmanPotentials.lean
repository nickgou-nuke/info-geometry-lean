/- Bregman Potentials and Matrix Itakura-Saito Divergence -/
/- Implements the Matrix Burg Potential (-log det) and its Bregman 
   divergence (Matrix Itakura-Saito / Stein Loss). -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

/-- 
  The non-negativity of the Matrix Itakura-Saito divergence (Stein Loss)
  for strictly positive-definite matrices.
  This represents the information-geometric stability of the metric.
-/
theorem itakura_saito_nonneg (X Y : Matrix n n ℝ) 
    (hX : 0 < det X) (hY : 0 < det Y) :    0 ≤ MatrixItakuraSaitoDivergence X Y (by linarith) := by
  sorry

/--
  The identity of indiscernibles for the Matrix Itakura-Saito divergence.
  The divergence vanishes if and only if the matrices coincide.
-/
theorem itakura_saito_eq_zero_iff (X Y : Matrix n n ℝ)     (hX : 0 < det X) (hY : 0 < det Y) :    MatrixItakuraSaitoDivergence X Y (by linarith) = 0 ↔ X = Y := by
  sorry

end InfoGeometry.Optimization