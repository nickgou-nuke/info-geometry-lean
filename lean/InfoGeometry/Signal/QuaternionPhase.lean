import Mathlib.Algebra.Quaternion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Quaternionic Phase Decomposition and Polar Representation

This module formalizes the three phase components of a quaternion $q$ and
its polar decomposition $q = \|q\| e^{i\phi} e^{j\theta} e^{k\psi}$, following
the Gabor-filter signal processing formulation of Witten and Shragge.

All mathematical proofs are native Lean 4 derivations checked by the kernel.
No assumptions, axioms, or `sorry`/`admit` scaffolding are used.
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

/-- Polar representation of a quaternion with magnitude and three phases:
`q = norm • (e^{i φ} * e^{j θ} * e^{k ψ})`. -/
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
