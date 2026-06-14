import Mathlib
import InfoGeometry.Algebra.QCCRSupergradingBridge

/-!
# Cuntz thermal q-bridge

Connects the q-CCR thermal dial to the Cuntz algebra core.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzThermalQBridge

open InfoGeometry.Algebra.QCCRSupergradingBridge

/--
At q = tanh θ, the q-superbracket rewrites in terms of hyperbolic
functions, connecting the algebraic deformation to the geometric boost.
-/
theorem q_tanh_theta_interpolation {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (θ : ℝ) (X Y : Op) :
    qSuperbracket (Real.tanh θ) X Y = ((Real.cosh θ) ^ 2)⁻¹ •
      (((Real.cosh θ) ^ 2) • (X * Y) - (Real.sinh θ * Real.cosh θ) • (Y * X)) := by
  have hcosh_ne_zero : Real.cosh θ ≠ 0 := by exact ne_of_gt (Real.cosh_pos θ)
  have hcosh_sq_ne_zero : (Real.cosh θ) ^ 2 ≠ 0 := pow_ne_zero 2 hcosh_ne_zero
  have h_scalar : (Real.cosh θ) ^ 2 * (Real.sinh θ / Real.cosh θ) = Real.cosh θ * Real.sinh θ := by
    field_simp [hcosh_ne_zero]; ring
  calc
    qSuperbracket (Real.tanh θ) X Y
        = X * Y - (Real.tanh θ) • (Y * X) := rfl
    _ = X * Y - ((Real.sinh θ / Real.cosh θ) • (Y * X)) := by rw [Real.tanh_eq_sinh_div_cosh θ]
    _ = ((Real.cosh θ) ^ 2)⁻¹ • (((Real.cosh θ) ^ 2) • (X * Y) - (Real.cosh θ * Real.sinh θ) • (Y * X)) := by
      field_simp [hcosh_ne_zero]
      ring

end InfoGeometry.Canonical.CuntzThermalQBridge
