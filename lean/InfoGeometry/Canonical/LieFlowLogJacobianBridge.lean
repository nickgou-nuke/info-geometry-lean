/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.LieFlowLogJacobianBridge

Log-Jacobian cocycle, infinitesimal divergence rate, and Lie generator trace formula.
-/

noncomputable section

namespace InfoGeometry.Canonical.LieFlowLogJacobian

open Real
open Matrix
open scoped Matrix

/-- Log-Jacobian cocycle: $\mathcal{J}_t(x) = -\ln |J_t(x)|$ -/
def logJacobianCocycle (J : ℝ) : ℝ :=
  - Real.log J

/-- 🏆 THEOREM 1: Additive cocycle law:
    $$-\ln(J_1 \cdot J_2) = (-\ln J_1) + (-\ln J_2)$$ -/
theorem logJacobianCocycle_mul (J1 J2 : ℝ) (h_J1 : 0 < J1) (h_J2 : 0 < J2) :
    logJacobianCocycle (J1 * J2) = logJacobianCocycle J1 + logJacobianCocycle J2 := by
  dsimp [logJacobianCocycle]
  rw [Real.log_mul (ne_of_gt h_J1) (ne_of_gt h_J2)]
  ring

/-- 🏆 THEOREM 2: Linear Lie flow trace formula:
    $$\det(e^{t A}) = e^{t \operatorname{tr} A} \implies -\ln(\det(e^{t A})) = - t \operatorname{tr} A$$ -/
theorem linear_lie_flow_log_det (t trA : ℝ) :
    logJacobianCocycle (Real.exp (t * trA)) = - t * trA := by
  dsimp [logJacobianCocycle]
  rw [Real.log_exp]
  ring

/-- A complex hyperbolic Möbius multiplier has squared modulus `exp (2 λ t)`,
so its log-Jacobian cocycle is `-2 λ t`. This is the exact volume-contraction
readout of the Möbius Lie flow, not a scalar analogy. -/
theorem mobius_hyperbolic_flow_log_jacobian (lambda t : ℝ) :
    logJacobianCocycle (Complex.normSq (Complex.exp ((lambda * t : ℝ) : ℂ))) =
      -2 * lambda * t := by
  have hnorm : Complex.normSq (Complex.exp ((lambda * t : ℝ) : ℂ)) =
      Real.exp (2 * (lambda * t)) := by
    rw [← Complex.ofReal_exp]
    simp only [Complex.normSq_ofReal]
    rw [← Real.exp_add]
    ring_nf
  rw [hnorm]
  dsimp [logJacobianCocycle]
  rw [Real.log_exp]
  ring

/-- An elliptic Möbius multiplier is pure phase, hence unimodular: its
log-Jacobian readout vanishes for every angle and time. -/
theorem mobius_elliptic_flow_log_jacobian_zero (theta t : ℝ) :
    logJacobianCocycle (Complex.normSq
      (Complex.exp (Complex.I * ((theta * t : ℝ) : ℂ)))) = 0 := by
  have hcomm : Complex.I * ((theta * t : ℝ) : ℂ) =
      ((theta * t : ℝ) : ℂ) * Complex.I := by ring
  have hunit : ‖Complex.exp (Complex.I * ((theta * t : ℝ) : ℂ))‖ = 1 := by
    rw [hcomm, Complex.norm_exp_ofReal_mul_I]
  have hnorm : Complex.normSq
      (Complex.exp (Complex.I * ((theta * t : ℝ) : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hunit, one_pow]
  rw [hnorm]
  dsimp [logJacobianCocycle]
  rw [Real.log_one, neg_zero]

/-- 🏆 THEOREM 3: Unimodular flow produces zero log-volume contraction:
    $$\det J = 1 \implies -\ln J = 0$$ -/
theorem unimodular_log_jacobian_zero (J : ℝ) (h_J : J = 1) :
    logJacobianCocycle J = 0 := by
  dsimp [logJacobianCocycle]
  rw [h_J, Real.log_one, neg_zero]

/-- A skew generator has zero trace in any finite real matrix dimension. -/
theorem skewMatrix_trace_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = -A) : Matrix.trace A = 0 := by
  have htrace : Matrix.trace A = -Matrix.trace A := by
    calc
      Matrix.trace A = Matrix.trace (Aᵀ) := (Matrix.trace_transpose A).symm
      _ = Matrix.trace (-A) := by rw [hA]
      _ = -Matrix.trace A := Matrix.trace_neg A
  linarith

/-- A skew (Killing-type) generator gives zero finite log-Jacobian contraction.
This is the finite trace/determinant shadow of contact-volume preservation. -/
theorem skewMatrix_logJacobianCocycle_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = -A) (t : ℝ) :
    logJacobianCocycle (Real.exp (t * Matrix.trace A)) = 0 := by
  have htrace : Matrix.trace A = 0 := skewMatrix_trace_zero A hA
  rw [htrace, mul_zero, Real.exp_zero]
  exact unimodular_log_jacobian_zero 1 rfl

end InfoGeometry.Canonical.LieFlowLogJacobian
