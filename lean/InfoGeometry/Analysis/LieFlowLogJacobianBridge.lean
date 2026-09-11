import InfoGeometry.Analysis.LieExponentialTraceDeterminant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RelativeSurprisalJacobianCocycleBridge

/-!
# Log-Jacobian readout of a finite Lie-exponential flow

This owner connects the native matrix exponential path to the existing
finite log-volume/surprisal cocycle.  It is a finite-dimensional statement:
no nonlinear flow, change-of-variables theorem, divergence field, or
continuum measure is introduced here.
-/

noncomputable section

namespace InfoGeometry.Analysis.LieFlowLogJacobianBridge

open InfoGeometry.Analysis.LieExponentialTraceDeterminant
open InfoGeometry.Canonical.RelativeSurprisalJacobianCocycleBridge

variable {n : ℕ}

/-- Logarithmic volume readout along the constant-generator matrix flow. -/
def lieFlowLogJacobian (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  logJacobian (lieExponentialPath A t)

/-- Negative log-volume, read as the finite flow surprisal. -/
def lieFlowJacobianSurprisal (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  jacobianSurprisal (lieExponentialPath A t)

theorem lieFlowLogJacobian_eq_trace
    (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    lieFlowLogJacobian A t = t * Matrix.trace A := by
  unfold lieFlowLogJacobian logJacobian
  rw [det_lieExponentialPath]
  rw [abs_of_pos (Real.exp_pos _), Real.log_exp]

theorem lieFlowJacobianSurprisal_eq_neg_trace
    (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    lieFlowJacobianSurprisal A t = -(t * Matrix.trace A) := by
  change -lieFlowLogJacobian A t = -(t * Matrix.trace A)
  rw [lieFlowLogJacobian_eq_trace]

theorem lieFlowLogJacobian_add
    (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    lieFlowLogJacobian A (s + t) =
      lieFlowLogJacobian A s + lieFlowLogJacobian A t := by
  rw [lieFlowLogJacobian_eq_trace,
    lieFlowLogJacobian_eq_trace,
    lieFlowLogJacobian_eq_trace]
  rw [add_mul]

theorem lieFlowLogJacobian_eq_zero_of_trace_zero
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.trace A = 0) (t : ℝ) :
    lieFlowLogJacobian A t = 0 := by
  rw [lieFlowLogJacobian_eq_trace, hA, mul_zero]

theorem lieFlowJacobianSurprisal_add
    (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    lieFlowJacobianSurprisal A (s + t) =
      lieFlowJacobianSurprisal A s + lieFlowJacobianSurprisal A t := by
  rw [lieFlowJacobianSurprisal_eq_neg_trace,
    lieFlowJacobianSurprisal_eq_neg_trace,
    lieFlowJacobianSurprisal_eq_neg_trace]
  rw [add_mul]
  ring

theorem lieFlowJacobianSurprisal_eq_zero_of_trace_zero
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.trace A = 0) (t : ℝ) :
    lieFlowJacobianSurprisal A t = 0 := by
  rw [lieFlowJacobianSurprisal_eq_neg_trace, hA, mul_zero, neg_zero]

end InfoGeometry.Analysis.LieFlowLogJacobianBridge
