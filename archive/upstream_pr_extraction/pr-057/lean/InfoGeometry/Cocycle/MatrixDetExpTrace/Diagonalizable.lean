import InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal
import InfoGeometry.Canonical.MatrixExponentialTraceDet

/-!
# Diagonalizable determinant/exponential trace cocycle

This is the second no-cheat determinant-volume layer:

if a complex matrix is explicitly conjugate to a diagonal matrix, then

`det (exp A) = exp (trace A)`.

The proof is delegated to the canonical owner theorem already proved from
mathlib's matrix exponential conjugation, determinant conjugation, trace
conjugation, and the diagonal theorem.

This remains a determinant/Weyl volume result.  It is deliberately not used as
the Cartan Fisher partition function; Fisher/Souriau geometry is owned by
`InfoGeometry.Algebraic.CartanExponentialFamily`.
-/

noncomputable section

namespace InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonalizable

open scoped Matrix

/-- Complex determinant/exponential trace law for matrices explicitly diagonalized by a unit. -/
theorem det_exp_eq_exp_trace_of_units_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ) :
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ))) =
      NormedSpace.exp
        (Matrix.trace
          ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ))) :=
  InfoGeometry.Canonical.MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_units_diagonal U v

/--
Short PR-style name for the explicit unit-diagonalizable
determinant/exponential trace law.
-/
theorem det_exp_diagonalizable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ)
    (hA : A = (U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  InfoGeometry.Canonical.MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_is_units_diagonalizable
    A U v hA

/-- Complex determinant/exponential trace law from an explicit diagonalization equality. -/
theorem det_exp_eq_exp_trace_of_is_units_diagonalizable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ)
    (hA : A = (U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  InfoGeometry.Canonical.MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_is_units_diagonalizable
    A U v hA

/-- H¹ cocycle-lane name for the explicit diagonalization theorem. -/
theorem h1_det_exp_trace_of_is_units_diagonalizable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ)
    (hA : A = (U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  det_exp_eq_exp_trace_of_is_units_diagonalizable A U v hA

end InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonalizable
