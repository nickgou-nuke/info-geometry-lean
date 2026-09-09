import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Section9

/-!
# Section 10: Spinorial Curvature Antisymmetry

This file exposes the Section 10 theorem as a named wrapper around the finite
algebraic owner from `Section9`.

It proves the antisymmetry of the spinorial curvature expression

`F_mu_nu = d_mu omega_nu - d_nu omega_mu + [omega_mu, omega_nu]`

under the swap `mu <-> nu`.  This is the exact finite algebraic statement of
the prose proof: the derivative terms change sign and the commutator satisfies
`[A, B] = -[B, A]`.
-/

noncomputable section

namespace Section10

open Matrix

abbrev SpinMat := Matrix (Fin 2) (Fin 2) ℂ

/-- Section 10 notation for the spinorial curvature tensor. -/
abbrev spinorialCurvature : SpinMat → SpinMat → SpinMat → SpinMat → SpinMat :=
  Section9.spinCurvature

/--
The spinorial curvature tensor is antisymmetric in the spacetime slots
represented by swapping `(d_mu omega_nu, omega_mu)` with
`(d_nu omega_mu, omega_nu)`.
-/
theorem spinorial_curvature_antisymmetric
    (dMuOmegaNu dNuOmegaMu omegaMu omegaNu : SpinMat) :
    spinorialCurvature dMuOmegaNu dNuOmegaMu omegaMu omegaNu =
      -spinorialCurvature dNuOmegaMu dMuOmegaNu omegaNu omegaMu := by
  unfold spinorialCurvature
  rw [Section9.spinCurvature_swap dMuOmegaNu dNuOmegaMu omegaMu omegaNu]
  simp

/-- Equivalent additive form of the antisymmetry. -/
theorem spinorial_curvature_add_swap
    (dMuOmegaNu dNuOmegaMu omegaMu omegaNu : SpinMat) :
    spinorialCurvature dMuOmegaNu dNuOmegaMu omegaMu omegaNu +
      spinorialCurvature dNuOmegaMu dMuOmegaNu omegaNu omegaMu = 0 := by
  rw [spinorial_curvature_antisymmetric]
  simp

theorem section10_capstone :
    ∀ dMuOmegaNu dNuOmegaMu omegaMu omegaNu : SpinMat,
      spinorialCurvature dMuOmegaNu dNuOmegaMu omegaMu omegaNu =
        -spinorialCurvature dNuOmegaMu dMuOmegaNu omegaNu omegaMu :=
  spinorial_curvature_antisymmetric

end Section10
