import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Relative surprisal and finite log-Jacobian cocycles

This owner uses the existing finite Connes/Radon--Nikodym density ratio and
the native matrix determinant.  It does not introduce a surrogate
metriplecic bracket.

The two kernel-checked readouts are:

* `-log (exp (-t * ΔK)) = t * ΔK`, the relative surprisal potential;
* `-log |det (A * B)| = -log |det A| - log |det B|`, the additive
  log-volume cocycle of finite linear changes of variables.

No claim about a general Radon--Nikodym derivative, differentiable nonlinear
flow, or Tomita--Takesaki modular operator is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.RelativeSurprisalJacobianCocycleBridge

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Logarithmic absolute determinant of a finite linear map. -/
def logJacobian (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.log |Matrix.det A|

/-- Negative log-volume cocycle (the sign convention for a surprisal). -/
def jacobianSurprisal (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -logJacobian A

theorem logJacobian_mul
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) :
    logJacobian (A * B) = logJacobian A + logJacobian B := by
  unfold logJacobian
  rw [Matrix.det_mul, abs_mul]
  rw [Real.log_mul (abs_ne_zero.mpr hA) (abs_ne_zero.mpr hB)]

theorem jacobianSurprisal_mul
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) :
    jacobianSurprisal (A * B) =
      jacobianSurprisal A + jacobianSurprisal B := by
  unfold jacobianSurprisal
  rw [logJacobian_mul A B hA hB]
  ring

theorem jacobianSurprisal_eq_zero_of_det_eq_one
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Matrix.det A = 1) :
    jacobianSurprisal A = 0 := by
  unfold jacobianSurprisal logJacobian
  rw [hA, abs_one, Real.log_one, neg_zero]

theorem logJacobian_identity :
    logJacobian (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  unfold logJacobian
  rw [Matrix.det_one, abs_one, Real.log_one]

theorem jacobianSurprisal_identity :
    jacobianSurprisal (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  unfold jacobianSurprisal
  rw [logJacobian_identity, neg_zero]

end InfoGeometry.Canonical.RelativeSurprisalJacobianCocycleBridge
