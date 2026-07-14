import InfoGeometry.Canonical.MatrixExponentialTraceDet

/-!
# Diagonal determinant/exponential trace cocycle

This is the first no-cheat determinant-volume layer:

`det (exp (diagonal v)) = exp (trace (diagonal v))`.

It uses only the already-proved diagonal matrix facts from
`InfoGeometry.Canonical.MatrixExponentialTraceDet`, which are rooted in
mathlib's `Matrix.exp_diagonal`, `Matrix.det_diagonal`, `Matrix.trace_diagonal`,
and finite exponential product/sum laws.

This module is intentionally separate from
`InfoGeometry.Algebraic.CartanExponentialFamily`: the theorem here is a Weyl
volume cocycle statement, not a Fisher/Souriau partition statement.
-/

noncomputable section

namespace Diagonal

open scoped Matrix

/-- Finite product/sum form of the scalar exponential law over `ℂ`. -/
theorem complex_exp_sum
    {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (∏ i, NormedSpace.exp (v i)) =
      NormedSpace.exp (∑ i, v i) := by
  simpa [Pi.coe_exp] using (NormedSpace.exp_sum (s := Finset.univ) (f := v)).symm

/-- Real diagonal determinant/exponential trace law. -/
theorem det_exp_diagonal_eq_exp_trace {n : ℕ} (v : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  InfoGeometry.Canonical.MatrixExponentialTraceDet.det_exp_diagonal_eq_exp_trace v

/-- Complex diagonal determinant/exponential trace law over any finite index type. -/
theorem det_exp_diagonal_eq_exp_trace_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  InfoGeometry.Canonical.MatrixExponentialTraceDet.det_exp_diagonal_eq_exp_trace_complex_fintype v

/-- Short PR-style name for the complex diagonal determinant/exponential trace law. -/
theorem det_exp_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  det_exp_diagonal_eq_exp_trace_complex v

/-- H¹ cocycle-lane name for the complex diagonal determinant/log-volume theorem. -/
theorem h1_det_exp_diagonal_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  det_exp_diagonal v

end Diagonal
