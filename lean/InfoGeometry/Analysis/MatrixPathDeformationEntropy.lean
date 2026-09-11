import InfoGeometry.Analysis.LogVolumeEntropyRate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LinearAlgebra.FiniteJacobianLogDet

noncomputable section

namespace InfoGeometry.Analysis.MatrixPathDeformationEntropy

open InfoGeometry.Analysis.LogVolumeEntropyRate
open InfoGeometry.Cocycle

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Determinant-volume path induced by a finite real matrix path. -/
def determinantVolumePath
    (J : ℝ → Matrix n n ℝ) :
    ℝ → ℝ :=
  fun t => (J t).det

/-- Pointwise negative log-absolute-determinant potential of a matrix path. -/
def matrixPathCompressionPotential
    (J : ℝ → Matrix n n ℝ) :
    ℝ → ℝ :=
  fun t => matrixLogdetBarrier (J t)

/--
On a positive-determinant path, the matrix log-determinant barrier is exactly
the scalar negative-log potential of the determinant-volume path.
-/
theorem matrixPathCompressionPotential_eq
    (J : ℝ → Matrix n n ℝ)
    (hJ : ∀ t : ℝ, 0 < (J t).det) :
    matrixPathCompressionPotential J =
      compressionPotential (determinantVolumePath J) := by
  funext t
  unfold matrixPathCompressionPotential compressionPotential
  rw [matrixLogdetBarrier, logdetBarrier, abs_of_pos (hJ t)]
  rfl

/--
The derivative of a positive-determinant matrix-path potential is the negative
logarithmic derivative of its determinant.
-/
theorem hasDerivAt_matrixPathCompressionPotential
    {J : ℝ → Matrix n n ℝ}
    {t det' : ℝ}
    (hdet : HasDerivAt (determinantVolumePath J) det' t)
    (hpos : ∀ u : ℝ, 0 < (J u).det) :
    HasDerivAt
      (matrixPathCompressionPotential J)
      (-det' / (J t).det)
      t := by
  rw [matrixPathCompressionPotential_eq J hpos]
  exact hasDerivAt_compressionPotential hdet (ne_of_gt (hpos t))

/--
If the determinant derivative has Jacobi form
`det' = det(J(t)) * generatorTrace`, then the deformation-entropy rate is the
negative generator trace.
-/
theorem hasDerivAt_matrixPathCompressionPotential_of_jacobi
    {J : ℝ → Matrix n n ℝ}
    {t det' generatorTrace : ℝ}
    (hdet : HasDerivAt (determinantVolumePath J) det' t)
    (hpos : ∀ u : ℝ, 0 < (J u).det)
    (hJacobi : det' = (J t).det * generatorTrace) :
    HasDerivAt
      (matrixPathCompressionPotential J)
      (-generatorTrace)
      t := by
  have h :=
    hasDerivAt_matrixPathCompressionPotential hdet hpos
  convert h using 1
  rw [hJacobi]
  field_simp [ne_of_gt (hpos t)]

/-- Derivative-level form of the conditional Jacobi entropy-rate theorem. -/
theorem deriv_matrixPathCompressionPotential_of_jacobi
    {J : ℝ → Matrix n n ℝ}
    {t det' generatorTrace : ℝ}
    (hdet : HasDerivAt (determinantVolumePath J) det' t)
    (hpos : ∀ u : ℝ, 0 < (J u).det)
    (hJacobi : det' = (J t).det * generatorTrace) :
    deriv (matrixPathCompressionPotential J) t =
      -generatorTrace :=
  (hasDerivAt_matrixPathCompressionPotential_of_jacobi
    hdet hpos hJacobi).deriv

end InfoGeometry.Analysis.MatrixPathDeformationEntropy
