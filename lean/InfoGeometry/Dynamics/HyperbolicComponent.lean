import InfoGeometry.OptimalTransport.LogDetBarrier
import Mathlib.Tactic

noncomputable section

/-!
# HyperbolicComponent

Real `A`-lane companion to the parabolic log-det bridge.

The parabolic `N` sector is determinant-one and trace-flat, so its
trace-logdet readout from the identity vanishes.  The hyperbolic `A` sector is
also determinant-one, but its trace changes as
`exp t + exp (-t)`, producing the curved profile
`exp t + exp (-t) - 2`.

This is the finite `2 × 2` real matrix shadow of the modular/dilation lane in
the KAN compass.
-/

namespace HyperbolicComponent

open Matrix

/-- Real `2 × 2` matrix carrier for the hyperbolic lane. -/
abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Traceless diagonal infinitesimal boost generator `diag(1, -1)`. -/
def hyperbolicGenerator : Mat2R :=
  !![1, 0; 0, -1]

/--
Hyperbolic `A` component: diagonal modular boost
`diag(exp t, exp (-t))`.
-/
def componentAReal (t : ℝ) : Mat2R :=
  !![Real.exp t, 0; 0, Real.exp (-t)]

/--
Trace-logdet divergence from the identity:
`tr X - log(det X) - 2`.

This is the real positive-determinant readout used for the exact `A`-lane
calculation below.
-/
def logDetDivergenceFromIdentityReal (X : Mat2R) : ℝ :=
  Matrix.trace X - Real.log X.det - 2

/-! ## Determinant and trace of the hyperbolic lane -/

/-- The hyperbolic `A` component lies in the determinant-one sector. -/
theorem componentAReal_det_eq_one (t : ℝ) :
    (componentAReal t).det = 1 := by
  simp [componentAReal, Matrix.det_fin_two, ← Real.exp_add]

/-- The hyperbolic `A` component has positive determinant. -/
theorem componentAReal_det_pos (t : ℝ) :
    0 < (componentAReal t).det := by
  simp [componentAReal_det_eq_one]

/-- The trace of `A(t)` is `exp t + exp (-t)`. -/
theorem componentAReal_trace (t : ℝ) :
    Matrix.trace (componentAReal t) = Real.exp t + Real.exp (-t) := by
  simp [componentAReal, Matrix.trace_fin_two]

/--
Exact log-det divergence profile for the hyperbolic boost.

The determinant contribution is zero, while the trace contribution records the
curved dilation profile.
-/
theorem componentAReal_logDetDivergenceFromIdentity (t : ℝ) :
    logDetDivergenceFromIdentityReal (componentAReal t) =
      Real.exp t + Real.exp (-t) - 2 := by
  simp [logDetDivergenceFromIdentityReal, componentAReal_trace,
    componentAReal_det_eq_one]

/-- At zero time the hyperbolic component is the identity matrix. -/
theorem componentAReal_zero :
    componentAReal 0 = (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [componentAReal]

/-- The hyperbolic log-det profile vanishes at the identity. -/
theorem componentAReal_logDetDivergence_zero :
    logDetDivergenceFromIdentityReal (componentAReal 0) = 0 := by
  simp [componentAReal_logDetDivergenceFromIdentity]
  ring_nf

/-! ## Infinitesimal metric readout -/

/-- Tangent boost vector `t * diag(1, -1)`. -/
def tangentBoost (t : ℝ) : Mat2R :=
  !![t, 0; 0, -t]

/-- The tangent boost is the scalar multiple of the boost generator. -/
theorem tangentBoost_eq_smul_generator (t : ℝ) :
    tangentBoost t = t • hyperbolicGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tangentBoost, hyperbolicGenerator]

/-- Trace-inner product on real `2 × 2` matrices. -/
def traceInner (X Y : Mat2R) : ℝ :=
  Matrix.trace (X * Yᵀ)

/-- Explicit product of two diagonal boost tangent vectors. -/
theorem tangentBoost_mul_transpose (s t : ℝ) :
    tangentBoost s * (tangentBoost t)ᵀ = !![s * t, 0; 0, s * t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tangentBoost, Matrix.mul_apply]

/-- The tangent boost has squared trace norm `2 * t^2`. -/
theorem tangentBoost_traceInner_self (t : ℝ) :
    traceInner (tangentBoost t) (tangentBoost t) = 2 * t ^ 2 := by
  rw [traceInner, tangentBoost_mul_transpose]
  simp [Matrix.trace_fin_two]
  ring

/--
The diagonal boost tangent pairs by the expected `2 * s * t` rule.
-/
theorem tangentBoost_traceInner (s t : ℝ) :
    traceInner (tangentBoost s) (tangentBoost t) = 2 * s * t := by
  rw [traceInner, tangentBoost_mul_transpose]
  simp [Matrix.trace_fin_two]
  ring

end HyperbolicComponent
