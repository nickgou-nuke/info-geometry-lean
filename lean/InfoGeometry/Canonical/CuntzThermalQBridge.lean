import Mathlib
import InfoGeometry.Algebra.QCCRSupergradingBridge

/-!
# Cuntz thermal q-bridge

Connects the q-CCR thermal dial to the Cuntz algebra core.
-/

noncomputable section

namespace CuntzThermalQBridge

open InfoGeometry.Algebra.QCCRSupergradingBridge

/--
At q = tanh θ, the q-superbracket rewrites in terms of hyperbolic
functions, connecting the algebraic deformation to the geometric boost.
-/
theorem q_tanh_theta_interpolation {Op : Type*} [Ring Op] [Algebra ℝ Op]
    (θ : ℝ) (X Y : Op) :
    qSuperbracket (Real.tanh θ) X Y = ((Real.cosh θ) ^ 2)⁻¹ •
      (((Real.cosh θ) ^ 2) • (X * Y) - (Real.sinh θ * Real.cosh θ) • (Y * X)) := by
  have hcosh_ne_zero : Real.cosh θ ≠ 0 := by
    have hpos : 0 < Real.cosh θ := Real.cosh_pos θ; linarith
  have hsq_ne_zero : (Real.cosh θ) ^ 2 ≠ 0 := pow_ne_zero 2 hcosh_ne_zero
  calc
    qSuperbracket (Real.tanh θ) X Y
        = X * Y - ((Real.sinh θ / Real.cosh θ) • (Y * X)) := by
      rw [Real.tanh_eq_sinh_div_cosh θ, qSuperbracket]
    _ = X * Y - ((((Real.cosh θ) ^ 2)⁻¹ * (Real.sinh θ * Real.cosh θ)) • (Y * X)) := by
      field_simp [hcosh_ne_zero]
    _ = (((Real.cosh θ) ^ 2)⁻¹ * (Real.cosh θ) ^ 2) • (X * Y)
        - (((Real.cosh θ) ^ 2)⁻¹ * (Real.sinh θ * Real.cosh θ)) • (Y * X) := by
      simp [hsq_ne_zero]
    _ = ((Real.cosh θ) ^ 2)⁻¹ • ((Real.cosh θ) ^ 2 • (X * Y))
        - ((Real.cosh θ) ^ 2)⁻¹ • ((Real.sinh θ * Real.cosh θ) • (Y * X)) := by
      simp [smul_smul]
    _ = ((Real.cosh θ) ^ 2)⁻¹ •
        (((Real.cosh θ) ^ 2) • (X * Y) - (Real.sinh θ * Real.cosh θ) • (Y * X)) := by rw [smul_sub]

end CuntzThermalQBridge
