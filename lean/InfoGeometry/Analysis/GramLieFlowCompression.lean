/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.GramPathDeformationEntropy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.LieExponentialTraceDeterminant
import InfoGeometry.LinearAlgebra.FiniteExponentialDeformationEntropy
import InfoGeometry.Analysis.LieFlowLogJacobianBridge
import InfoGeometry.Arithmetic.MajoranaPolyaHilbert.BerryKeating

noncomputable section

namespace InfoGeometry.Analysis.GramLieFlowCompression

open InfoGeometry.Analysis.GramPathDeformationEntropy
open InfoGeometry.Analysis.LieExponentialTraceDeterminant
open InfoGeometry.LinearAlgebra.FiniteExponentialDeformationEntropy
open InfoGeometry.LinearAlgebra.FiniteGramDeformationEntropy
open InfoGeometry.Cocycle
open InfoGeometry.Algebra.NoncommutativeTetraktysFlows
open InfoGeometry.Analysis.LieFlowLogJacobianBridge

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

/-- The Gram compression potential of the real Tetraktys flow with a central
dilaton is exactly the negative dilaton trace contribution.  The Tetraktys
component contributes no trace, by the finite-matrix Tetraktys bridge. -/
theorem gramPathCompressionPotential_tetraktys_dilaton
    (cGamma cSigma cOmega d : ℝ) :
    gramPathCompressionPotential
      (lieExponentialPath (fiberEmbed d + flowGen cGamma cSigma cOmega)) =
      fun t => -(t * (2 * d)) := by
  rw [gramPathCompressionPotential_lieExponential_eq_trace]
  have hD : Matrix.trace (fiberEmbed d) = 2 * d := by
    simp [fiberEmbed, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    ring
  have hTrace : Matrix.trace (fiberEmbed d + flowGen cGamma cSigma cOmega) = 2 * d := by
    rw [Matrix.trace_add, hD, tetraktys_flowGen_trace_zero]
    ring
  rw [hTrace]
  funext t
  ring

section XPDilatonGramCompression

open InfoGeometry.Arithmetic.MajoranaPolyaHilbert

/-- The antisymmetric commutator `[x, p] = x * p - p * x` has identically zero Gram compression
potential on `Matrix n n ℝ` for arbitrary `[Fintype n] [DecidableEq n]`. -/
theorem gramPathCompressionPotential_commutator_eq_zero (x p : Matrix n n ℝ) :
    gramPathCompressionPotential (lieExponentialPath (x * p - p * x)) = 0 := by
  apply gramPathCompressionPotential_lieExponential_eq_zero_of_trace_eq_zero
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- The symmetric `xp` dilaton carries the full Gram compression potential `-(t * Tr(x * p))`. -/
theorem gramPathCompressionPotential_finiteSymmetrizedDilation (x p : Matrix n n ℝ) :
    gramPathCompressionPotential (lieExponentialPath (finiteSymmetrizedDilation x p)) =
      fun t => -(t * Matrix.trace (x * p)) := by
  rw [gramPathCompressionPotential_lieExponential_eq_trace]
  have htr : Matrix.trace (finiteSymmetrizedDilation x p) = Matrix.trace (x * p) := by
    dsimp [finiteSymmetrizedDilation]
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_mul_comm p x, smul_eq_mul]
    ring
  rw [htr]
  funext t
  ring

/-- `HasDerivAt` for the Gram compression potential along `finiteSymmetrizedDilation x p`. -/
theorem hasDerivAt_gramPathCompressionPotential_finiteSymmetrizedDilation
    (x p : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt
      (gramPathCompressionPotential (lieExponentialPath (finiteSymmetrizedDilation x p)))
      (-Matrix.trace (x * p)) t := by
  have htr : Matrix.trace (finiteSymmetrizedDilation x p) = Matrix.trace (x * p) := by
    dsimp [finiteSymmetrizedDilation]
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_mul_comm p x, smul_eq_mul]
    ring
  simpa [htr] using
    hasDerivAt_gramPathCompressionPotential_lieExponential (finiteSymmetrizedDilation x p) t

/-- The Gram compression derivative along `finiteSymmetrizedDilation x p` is `-Matrix.trace (x * p)`. -/
theorem deriv_gramPathCompressionPotential_finiteSymmetrizedDilation
    (x p : Matrix n n ℝ) (t : ℝ) :
    deriv (gramPathCompressionPotential (lieExponentialPath (finiteSymmetrizedDilation x p))) t =
      -Matrix.trace (x * p) := by
  rw [(hasDerivAt_gramPathCompressionPotential_finiteSymmetrizedDilation x p t).deriv]

/-- The Gram compression derivative along `[x, p]` vanishes identically. -/
theorem deriv_gramPathCompressionPotential_commutator_eq_zero
    (x p : Matrix n n ℝ) (t : ℝ) :
    deriv (gramPathCompressionPotential (lieExponentialPath (x * p - p * x))) t = 0 := by
  rw [gramPathCompressionPotential_commutator_eq_zero]
  simp

/-- The Gram compression potential of `x * p` coincides with that of `finiteSymmetrizedDilation x p`. -/
theorem gramPathCompressionPotential_xp_eq_finiteSymmetrizedDilation
    (x p : Matrix n n ℝ) :
    gramPathCompressionPotential (lieExponentialPath (x * p)) =
      gramPathCompressionPotential (lieExponentialPath (finiteSymmetrizedDilation x p)) := by
  rw [gramPathCompressionPotential_lieExponential_eq_trace,
    gramPathCompressionPotential_finiteSymmetrizedDilation]
  funext t
  ring

end XPDilatonGramCompression

end InfoGeometry.Analysis.GramLieFlowCompression
