import InfoGeometry.Analysis.LogVolumeEntropyRate
import InfoGeometry.Analysis.LieExponentialTraceDeterminant
import InfoGeometry.LinearAlgebra.FiniteJacobianLogDet

noncomputable section

namespace InfoGeometry.Analysis.MatrixPathDeformationEntropy

open InfoGeometry.Analysis.LogVolumeEntropyRate
open InfoGeometry.Analysis.LieExponentialTraceDeterminant
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

/-!
The Lie-exponential specialization is the concrete Jacobian redline: the
negative log-volume potential is affine with slope minus the generator trace.
This is still a finite matrix theorem; no measure-theoretic Radon--Nikodym
identification is asserted here.
-/

theorem matrixPathCompressionPotential_lieExponentialPath
    (A : Matrix n n ℝ) (t : ℝ) :
    matrixPathCompressionPotential (lieExponentialPath A) t =
      -(t * Matrix.trace A) := by
  change matrixLogdetBarrier (lieExponentialPath A t) =
    -(t * Matrix.trace A)
  unfold matrixLogdetBarrier logdetBarrier
  rw [det_lieExponentialPath, abs_of_pos (Real.exp_pos _)]
  simp

theorem deriv_matrixPathCompressionPotential_lieExponentialPath
    (A : Matrix n n ℝ) (t : ℝ) :
    deriv (matrixPathCompressionPotential (lieExponentialPath A)) t =
      -Matrix.trace A := by
  have hfun :
      matrixPathCompressionPotential (lieExponentialPath A) =
        (fun u : ℝ => -(u * Matrix.trace A)) := by
    funext u
    exact matrixPathCompressionPotential_lieExponentialPath A u
  rw [hfun]
  simpa using ((hasDerivAt_id t).mul_const (Matrix.trace A)).neg.deriv

end InfoGeometry.Analysis.MatrixPathDeformationEntropy
