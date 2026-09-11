import InfoGeometry.Analysis.MatrixPathDeformationEntropy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LinearAlgebra.FiniteGramDeformationEntropy

noncomputable section

namespace InfoGeometry.Analysis.GramPathDeformationEntropy

open InfoGeometry.Analysis.MatrixPathDeformationEntropy
open InfoGeometry.Analysis.LogVolumeEntropyRate
open InfoGeometry.LinearAlgebra.FiniteGramDeformationEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Gram-determinant compression potential along a finite real matrix path. -/
def gramPathCompressionPotential
    (J : ℝ → Matrix n n ℝ) :
    ℝ → ℝ :=
  fun t => gramCompressionPotential (J t)

/--
Along a pointwise nonsingular matrix path, the Gram-determinant potential is
the existing negative log-absolute-determinant path potential.
-/
theorem gramPathCompressionPotential_eq_matrixPathCompressionPotential
    (J : ℝ → Matrix n n ℝ)
    (hJ : ∀ t : ℝ, (J t).det ≠ 0) :
    gramPathCompressionPotential J =
      matrixPathCompressionPotential J := by
  funext t
  exact gramCompressionPotential_eq_matrixLogdetBarrier (J t) (hJ t)

/--
The matrix-path compression potential is the scalar determinant-volume
compression potential on every pointwise nonsingular path.
-/
theorem matrixPathCompressionPotential_eq_compressionPotential
    (J : ℝ → Matrix n n ℝ) :
    matrixPathCompressionPotential J =
      compressionPotential (determinantVolumePath J) := by
  funext t
  simp [matrixPathCompressionPotential, compressionPotential,
    determinantVolumePath, InfoGeometry.Cocycle.matrixLogdetBarrier,
    InfoGeometry.Cocycle.logdetBarrier, Real.log_abs]

/--
The derivative of the Gram-path potential is the negative logarithmic
derivative of the determinant.
-/
theorem hasDerivAt_gramPathCompressionPotential
    {J : ℝ → Matrix n n ℝ}
    {t det' : ℝ}
    (hdet : HasDerivAt (determinantVolumePath J) det' t)
    (hJ : ∀ u : ℝ, (J u).det ≠ 0) :
    HasDerivAt
      (gramPathCompressionPotential J)
      (-det' / (J t).det)
      t := by
  rw [gramPathCompressionPotential_eq_matrixPathCompressionPotential J hJ,
    matrixPathCompressionPotential_eq_compressionPotential J]
  exact hasDerivAt_compressionPotential hdet (hJ t)

/--
Under Jacobi's determinant-rate identity, the Gram-path compression rate is
the negative generator trace.
-/
theorem hasDerivAt_gramPathCompressionPotential_of_jacobi
    {J : ℝ → Matrix n n ℝ}
    {t det' generatorTrace : ℝ}
    (hdet : HasDerivAt (determinantVolumePath J) det' t)
    (hJ : ∀ u : ℝ, (J u).det ≠ 0)
    (hJacobi : det' = (J t).det * generatorTrace) :
    HasDerivAt
      (gramPathCompressionPotential J)
      (-generatorTrace)
      t := by
  have h := hasDerivAt_gramPathCompressionPotential hdet hJ
  convert h using 1
  rw [hJacobi]
  field_simp [hJ t]

/-- Derivative-level form of the Gram-path Jacobi entropy-rate theorem. -/
theorem deriv_gramPathCompressionPotential_of_jacobi
    {J : ℝ → Matrix n n ℝ}
    {t det' generatorTrace : ℝ}
    (hdet : HasDerivAt (determinantVolumePath J) det' t)
    (hJ : ∀ u : ℝ, (J u).det ≠ 0)
    (hJacobi : det' = (J t).det * generatorTrace) :
    deriv (gramPathCompressionPotential J) t =
      -generatorTrace :=
  (hasDerivAt_gramPathCompressionPotential_of_jacobi
    hdet hJ hJacobi).deriv

end InfoGeometry.Analysis.GramPathDeformationEntropy
