import InfoGeometry.Analysis.GramPathDeformationEntropy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.LieExponentialTraceDeterminant
import InfoGeometry.LinearAlgebra.FiniteExponentialDeformationEntropy

noncomputable section

namespace InfoGeometry.Analysis.GramLieFlowCompression

open InfoGeometry.Analysis.GramPathDeformationEntropy
open InfoGeometry.Analysis.LieExponentialTraceDeterminant
open InfoGeometry.LinearAlgebra.FiniteExponentialDeformationEntropy
open InfoGeometry.LinearAlgebra.FiniteGramDeformationEntropy
open InfoGeometry.Cocycle

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Gram compression potential agrees with the native finite exponential entropy.

This is a composition bridge: the determinant/exponential trace law is owned by
`InfoGeometry.Cocycle.MatrixDetExpTrace`, while the Gram reduction is owned by
`FiniteGramDeformationEntropy` and `GramPathDeformationEntropy`. -/
theorem gramPathCompressionPotential_lieExponential_eq_exponentialDeformationEntropy
    (A : Matrix n n ℝ) :
    gramPathCompressionPotential (lieExponentialPath A) =
      exponentialDeformationEntropy A := by
  funext t
  change gramCompressionPotential (NormedSpace.exp (t • A)) =
    matrixLogdetBarrier (NormedSpace.exp (t • A))
  exact gramCompressionPotential_eq_matrixLogdetBarrier
    (NormedSpace.exp (t • A))
    (by
      rw [InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace_real]
      simpa [Real.exp_eq_exp_ℝ] using
        (Real.exp_ne_zero (Matrix.trace (t • A))) )

/-- On a constant exponential flow, Gram compression is the negative trace rate. -/
theorem gramPathCompressionPotential_lieExponential_eq_trace
    (A : Matrix n n ℝ) :
    gramPathCompressionPotential (lieExponentialPath A) =
      fun t => -t * Matrix.trace A := by
  rw [gramPathCompressionPotential_lieExponential_eq_exponentialDeformationEntropy]
  funext t
  exact exponentialDeformationEntropy_eq A t

/-- The infinitesimal Gram compression rate is the negative generator trace. -/
theorem hasDerivAt_gramPathCompressionPotential_lieExponential
    (A : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt
      (gramPathCompressionPotential (lieExponentialPath A))
      (-Matrix.trace A)
      t := by
  rw [gramPathCompressionPotential_lieExponential_eq_trace]
  simpa using (hasDerivAt_id t).neg.mul_const (Matrix.trace A)

/-- Derivative readout for the constant-generator Gram flow. -/
theorem deriv_gramPathCompressionPotential_lieExponential
    (A : Matrix n n ℝ) (t : ℝ) :
    deriv (gramPathCompressionPotential (lieExponentialPath A)) t =
      -Matrix.trace A :=
  (hasDerivAt_gramPathCompressionPotential_lieExponential A t).deriv

/-- Trace-free generators preserve the Gram compression potential identically. -/
theorem gramPathCompressionPotential_lieExponential_eq_zero_of_trace_eq_zero
    (A : Matrix n n ℝ) (hA : Matrix.trace A = 0) :
    gramPathCompressionPotential (lieExponentialPath A) = 0 := by
  rw [gramPathCompressionPotential_lieExponential_eq_trace, hA]
  funext t
  simp

end InfoGeometry.Analysis.GramLieFlowCompression
