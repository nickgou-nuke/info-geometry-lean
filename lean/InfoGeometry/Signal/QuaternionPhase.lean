import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Quaternion coordinate phase readouts

This module defines three coordinate exponentials and their finite product in
`Quaternion ℝ`, together with one coordinate expansion theorem. It does not
prove a polar decomposition theorem for arbitrary quaternions.
-/

noncomputable section

namespace InfoGeometry.Signal.QuaternionPhase

/-- The standard two-argument arctangent function `arctan2 y x`. -/
def arctan2 (y x : ℝ) : ℝ :=
  if x > 0 then Real.arctan (y / x)
  else if x < 0 then
    if y >= 0 then Real.arctan (y / x) + Real.pi
    else Real.arctan (y / x) - Real.pi
  else -- x = 0
    if y > 0 then Real.pi / 2
    else if y < 0 then -Real.pi / 2
    else 0

/-- Exponentials of the imaginary quaternionic directions i, j, k. -/
def exp_i (phi : ℝ) : Quaternion ℝ := ⟨Real.cos phi, Real.sin phi, 0, 0⟩
def exp_j (theta : ℝ) : Quaternion ℝ := ⟨Real.cos theta, 0, Real.sin theta, 0⟩
def exp_k (psi : ℝ) : Quaternion ℝ := ⟨Real.cos psi, 0, 0, Real.sin psi⟩

/-- Scalar multiple of the three coordinate exponentials. -/
def polarQuaternion (norm : ℝ) (phi theta psi : ℝ) : Quaternion ℝ :=
  norm • (exp_i phi * exp_j theta * exp_k psi)

/-- Coordinate equation for the numerator of the first phase component φ. -/
def n_phi (q : Quaternion ℝ) : ℝ := -2 * (q.imJ * q.imK + q.re * q.imI)

/-- Coordinate equation for the denominator of the first phase component φ. -/
def d_phi (q : Quaternion ℝ) : ℝ := q.re^2 - q.imI^2 + q.imJ^2 - q.imK^2

/-- Coordinate equation for the numerator of the second phase component θ. -/
def n_theta (q : Quaternion ℝ) : ℝ := -2 * (q.imI * q.imK + q.re * q.imJ)

/-- Coordinate equation for the denominator of the second phase component θ. -/
def d_theta (q : Quaternion ℝ) : ℝ := q.re^2 + q.imI^2 - q.imJ^2 - q.imK^2

/-- Coordinate equation for the numerator of the third phase component ψ. -/
def n_psi (q : Quaternion ℝ) : ℝ := 2 * (q.imI * q.imJ + q.re * q.imK)

/-- Explicit expansion of the polar quaternion components. -/
theorem polarQuaternion_components (phi theta psi : ℝ) :
    polarQuaternion 1 phi theta psi =
      ⟨Real.cos phi * Real.cos theta * Real.cos psi - Real.sin phi * Real.sin theta * Real.sin psi,
       Real.sin phi * Real.cos theta * Real.cos psi + Real.cos phi * Real.sin theta * Real.sin psi,
       Real.cos phi * Real.sin theta * Real.cos psi - Real.sin phi * Real.cos theta * Real.sin psi,
       Real.sin phi * Real.sin theta * Real.cos psi + Real.cos phi * Real.cos theta * Real.sin psi⟩ := by
  dsimp [polarQuaternion, exp_i, exp_j, exp_k]
  ext <;> simp <;> ring

end InfoGeometry.Signal.QuaternionPhase
