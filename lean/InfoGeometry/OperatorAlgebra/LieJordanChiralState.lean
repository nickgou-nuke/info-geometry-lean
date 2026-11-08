/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceSandwichDuality
import Mathlib.Tactic.Linarith

/-!
# Sheet exchange and odd state readouts

An algebra automorphism and a real linear functional are explicit. Invariance
of that functional is not asserted merely from a vector's parity. These are
algebraic state tests, not a construction of a thermodynamic broken phase.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanChiralState

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Coefficient exchange fixes the quadratic sum. -/
theorem exchange_quadratic (theta : A ≃ₐ[ℝ] A) (u v : A)
    (hu : theta u = v) (hv : theta v = u) :
    theta (u * v + v * u) = u * v + v * u := by
  rw [map_add, map_mul, map_mul, hu, hv, add_comm]

/-- The same exchange reverses the quadratic difference. -/
theorem exchange_spin (theta : A ≃ₐ[ℝ] A) (u v : A)
    (hu : theta u = v) (hv : theta v = u) :
    theta (u * v - v * u) = -(u * v - v * u) := by
  rw [map_sub, map_mul, map_mul, hu, hv]
  abel

/-- Invariance forces the expectation of a symmetry-odd operator to vanish. -/
theorem invariant_odd_zero (theta : A ≃ₐ[ℝ] A) (omega : A →ₗ[ℝ] ℝ)
    (hinv : omega.comp theta.toLinearMap = omega)
    (m : A) (hm : theta m = -m) : omega m = 0 := by
  have h := congrArg (fun f : A →ₗ[ℝ] ℝ => f m) hinv
  change omega (theta m) = omega m at h
  rw [hm, map_neg] at h
  linarith

/-- A nonzero odd readout certifies non-invariance, without assuming equilibrium. -/
theorem odd_nonzero_not_invariant (theta : A ≃ₐ[ℝ] A) (omega : A →ₗ[ℝ] ℝ)
    (m : A) (hm : theta m = -m) (hn : omega m ≠ 0) :
    omega.comp theta.toLinearMap ≠ omega := by
  intro h
  exact hn (invariant_odd_zero theta omega h m hm)

/-- Averaging gives an invariant functional but does not prove extremality or restoration. -/
theorem symmetrized_invariant (theta : A ≃ₐ[ℝ] A)
    (htheta : Function.Involutive theta) (omega : A →ₗ[ℝ] ℝ) :
    (((1 / 2 : ℝ) • (omega + omega.comp theta.toLinearMap)).comp theta.toLinearMap) =
      (1 / 2 : ℝ) • (omega + omega.comp theta.toLinearMap) := by
  ext x
  change (1 / 2 : ℝ) * (omega (theta x) + omega (theta (theta x))) =
    (1 / 2 : ℝ) * (omega x + omega (theta x))
  rw [htheta x, add_comm]

end InfoGeometry.OperatorAlgebra.LieJordanChiralState
