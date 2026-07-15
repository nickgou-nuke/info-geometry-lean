import InfoGeometry.Canonical.MatrixDetExpTraceJacobi
import InfoGeometry.Canonical.MatrixExponentialTraceDet
import InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal
import InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonalizable

/-!
# Matrix determinant exponential trace bridge

This module places the proved finite-dimensional determinant/log-volume
identities in the cocycle namespace.  The unrestricted complex theorem is
proved in `InfoGeometry.Canonical.MatrixDetExpTraceJacobi` by the
Liouville/Jacobi flow route:

`Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`.

The proved owner surfaces are:

* arbitrary complex matrices;
* arbitrary real matrices, by real-to-complex transfer;
* diagonal real matrices;
* diagonal complex matrices over an arbitrary finite index type;
* complex matrices supplied with an explicit diagonalization by a unit;
* complex upper-triangular matrices and matrices explicitly conjugate to them;
* complex Hermitian matrices, via the mathlib spectral theorem.
-/

noncomputable section

namespace MatrixDetExpTrace

open scoped Matrix

/-- Finite product/sum form of the scalar exponential law over `ℂ`. -/
theorem complex_exp_sum
    {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (∏ i, NormedSpace.exp (v i)) =
      NormedSpace.exp (∑ i, v i) := by
  simpa [Pi.coe_exp] using (NormedSpace.exp_sum (s := Finset.univ) (f := v)).symm

/-- Unrestricted complex determinant/exponential trace law. -/
theorem det_exp_eq_exp_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  Matrix.det_exp_eq_exp_trace A

/-- Unrestricted real determinant/exponential trace law. -/
theorem det_exp_eq_exp_trace_real
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  Matrix.det_exp_eq_exp_trace_real A

/-- Real diagonal determinant/exponential trace law. -/
theorem det_exp_diagonal_eq_exp_trace {n : ℕ} (v : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  MatrixExponentialTraceDet.det_exp_diagonal_eq_exp_trace v

/-- Complex diagonal determinant/exponential trace law over any finite index type. -/
theorem det_exp_diagonal_eq_exp_trace_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  MatrixExponentialTraceDet.det_exp_diagonal_eq_exp_trace_complex_fintype v

/-- Short PR-style name for the complex diagonal determinant/exponential trace law. -/
theorem det_exp_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  det_exp_diagonal_eq_exp_trace_complex v

/--
Complex determinant/exponential trace law for matrices explicitly diagonalized
by an invertible matrix.
-/
theorem det_exp_eq_exp_trace_of_units_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ) :
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ))) =
      NormedSpace.exp
        (Matrix.trace
          ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ))) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_units_diagonal U v

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
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_is_units_diagonalizable
    A U v hA

/-- Complex determinant/exponential trace law from an explicit diagonalization equality. -/
theorem det_exp_eq_exp_trace_of_is_units_diagonalizable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ)
    (hA : A = (U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_is_units_diagonalizable
    A U v hA

/-- Complex determinant/exponential trace law for upper-triangular matrices. -/
theorem det_exp_eq_exp_trace_of_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.BlockTriangular id) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_upperTriangular A hA

/--
Complex determinant/exponential trace law for matrices explicitly conjugate to
an upper-triangular matrix.
-/
theorem det_exp_eq_exp_trace_of_units_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (U : (Matrix ι ι ℂ)ˣ) (T : Matrix ι ι ℂ) (hT : T.BlockTriangular id) :
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ))) =
      NormedSpace.exp
        (Matrix.trace
          ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ))) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_units_upperTriangular
    U T hT

/--
Complex determinant/exponential trace law from an explicit
upper-triangularization equality.
-/
theorem det_exp_eq_exp_trace_of_is_units_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (T : Matrix ι ι ℂ)
    (hT : T.BlockTriangular id)
    (hA : A = (U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_is_units_upperTriangular
    A U T hT hA

/--
Complex Hermitian determinant/exponential trace law.

This is the current non-diagonal owner theorem in the repo: it uses mathlib's
Hermitian spectral theorem, conjugation invariance of the matrix exponential,
unitary determinant cancellation, and the diagonal law above.
-/
theorem det_exp_eq_exp_trace_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_isHermitian A hA

/-- H¹ cocycle-lane name for the unrestricted complex determinant/log-volume theorem. -/
theorem h1_det_exp_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  det_exp_eq_exp_trace A

/-- H¹ cocycle-lane name for the unrestricted real determinant/log-volume theorem. -/
theorem h1_det_exp_trace_real
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  det_exp_eq_exp_trace_real A

/-- H¹ cocycle-lane name for the complex Hermitian determinant/log-volume theorem. -/
theorem h1_det_exp_trace_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  det_exp_eq_exp_trace_of_isHermitian A hA

/-- H¹ cocycle-lane name for the explicit diagonalization theorem. -/
theorem h1_det_exp_trace_of_is_units_diagonalizable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ)
    (hA : A = (U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  det_exp_eq_exp_trace_of_is_units_diagonalizable A U v hA

/-- H¹ cocycle-lane name for the upper-triangular theorem. -/
theorem h1_det_exp_trace_of_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.BlockTriangular id) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  det_exp_eq_exp_trace_of_upperTriangular A hA

/-- H¹ cocycle-lane name for the explicit upper-triangular conjugation theorem. -/
theorem h1_det_exp_trace_of_units_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (U : (Matrix ι ι ℂ)ˣ) (T : Matrix ι ι ℂ) (hT : T.BlockTriangular id) :
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ))) =
      NormedSpace.exp
      (Matrix.trace
          ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ))) :=
  det_exp_eq_exp_trace_of_units_upperTriangular U T hT

/-- H¹ cocycle-lane name for the explicit upper-triangularization theorem. -/
theorem h1_det_exp_trace_of_is_units_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (T : Matrix ι ι ℂ)
    (hT : T.BlockTriangular id)
    (hA : A = (U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  det_exp_eq_exp_trace_of_is_units_upperTriangular A U T hT hA

end MatrixDetExpTrace
