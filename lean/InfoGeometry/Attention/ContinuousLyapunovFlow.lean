import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Attention.ContinuousLyapunovFlow

open Matrix

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vec2R := Fin 2 → ℝ

/-- The Euclidean squared norm of a 2D state vector. -/
def norm_sq (x : Vec2R) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2

/-- The Euclidean dot product on ℝ². -/
def dot_product (u v : Vec2R) : ℝ :=
  u 0 * v 0 + u 1 * v 1

/-- Trajectory x : ℝ → Vec2R satisfies the linear ODE ẋ(t) = M *ᵥ x(t) at time t. -/
def IsTrajectoryOf (x : ℝ → Vec2R) (M : Mat2R) (t : ℝ) : Prop :=
  (HasDerivAt (fun s => x s 0) ((M *ᵥ x t) 0) t) ∧
  (HasDerivAt (fun s => x s 1) ((M *ᵥ x t) 1) t)

/-!
# Continuous-Time Lyapunov Energy Derivative
For V(t) = ‖x(t)‖² = x₀(t)² + x₁(t)², we compute:
  d/dt V(t) = 2 x₀(t) ẋ₀(t) + 2 x₁(t) ẋ₁(t) = 2 ⟨x(t), ẋ(t)⟩ = 2 ⟨x(t), M x(t)⟩.
-/

/-- Master Theorem 1: The time derivative of the squared norm along a trajectory. -/
theorem deriv_norm_sq_eq_two_dot (x : ℝ → Vec2R) (M : Mat2R) (t : ℝ)
    (h_traj0 : HasDerivAt (fun s => x s 0) ((M *ᵥ x t) 0) t)
    (h_traj1 : HasDerivAt (fun s => x s 1) ((M *ᵥ x t) 1) t) :
    HasDerivAt (fun s => norm_sq (x s)) (2 * dot_product (x t) (M *ᵥ x t)) t := by
  dsimp [norm_sq, dot_product]
  have h0 : HasDerivAt (fun s => (x s 0) ^ 2) (2 * x t 0 * (M *ᵥ x t) 0) t := by
    have h_pow := h_traj0.pow 2
    convert h_pow using 1
    ring
  have h1 : HasDerivAt (fun s => (x s 1) ^ 2) (2 * x t 1 * (M *ᵥ x t) 1) t := by
    have h_pow := h_traj1.pow 2
    convert h_pow using 1
    ring
  have h_sum := h0.add h1
  convert h_sum using 1
  ring

/-!
# Master Theorem 2: Instantaneous Energy Dissipation Flux
When the chiral coupling is skew-symmetric (M₀₁ = -M₁₀), the total energy flux
is purely determined by the diagonal dissipative core:
  ⟨x, M x⟩ = M₀₀ x₀² + M₁₁ x₁².
-/
theorem dot_product_mulVec_skew (M : Mat2R) (v : Vec2R)
    (h_skew : M 0 1 = - M 1 0) :
    dot_product v (M *ᵥ v) = M 0 0 * (v 0 ^ 2) + M 1 1 * (v 1 ^ 2) := by
  dsimp [dot_product, mulVec, dotProduct]
  simp only [Fin.sum_univ_two]
  have h_alg : v 0 * (M 0 0 * v 0 + M 0 1 * v 1) + v 1 * (M 1 0 * v 0 + M 1 1 * v 1) =
               M 0 0 * (v 0 ^ 2) + M 1 1 * (v 1 ^ 2) + (M 0 1 + M 1 0) * (v 0 * v 1) := by
    ring
  rw [h_alg, h_skew]
  ring

/-!
# Master Theorem 3: The Continuous-Time Lyapunov Derivative Inequality
If M₀₀ ≤ -α and M₁₁ ≤ -α with skew-symmetric chiral coupling (M₀₁ = -M₁₀),
the time derivative of the squared norm satisfies:
  d/dt ‖x(t)‖² ≤ -2 * α * ‖x(t)‖².
-/
theorem continuous_lyapunov_derivative_le (x : ℝ → Vec2R) (M : Mat2R) (t α : ℝ)
    (h_traj0 : HasDerivAt (fun s => x s 0) ((M *ᵥ x t) 0) t)
    (h_traj1 : HasDerivAt (fun s => x s 1) ((M *ᵥ x t) 1) t)
    (h_skew : M 0 1 = - M 1 0)
    (h_diss00 : M 0 0 ≤ -α)
    (h_diss11 : M 1 1 ≤ -α) :
    ∃ dV : ℝ, HasDerivAt (fun s => norm_sq (x s)) dV t ∧
              dV ≤ -2 * α * norm_sq (x t) := by
  let dV := 2 * dot_product (x t) (M *ᵥ x t)
  use dV
  constructor
  · exact deriv_norm_sq_eq_two_dot x M t h_traj0 h_traj1
  · dsimp [dV]
    rw [dot_product_mulVec_skew M (x t) h_skew]
    dsimp [norm_sq]
    have h_sq0 : 0 ≤ x t 0 ^ 2 := sq_nonneg (x t 0)
    have h_sq1 : 0 ≤ x t 1 ^ 2 := sq_nonneg (x t 1)
    have h_bound0 : M 0 0 * (x t 0 ^ 2) ≤ (-α) * (x t 0 ^ 2) :=
      mul_le_mul_of_nonneg_right h_diss00 h_sq0
    have h_bound1 : M 1 1 * (x t 1 ^ 2) ≤ (-α) * (x t 1 ^ 2) :=
      mul_le_mul_of_nonneg_right h_diss11 h_sq1
    have h_sum_le : M 0 0 * (x t 0 ^ 2) + M 1 1 * (x t 1 ^ 2) ≤
                    (-α) * (x t 0 ^ 2) + (-α) * (x t 1 ^ 2) :=
      add_le_add h_bound0 h_bound1
    calc 2 * (M 0 0 * (x t 0 ^ 2) + M 1 1 * (x t 1 ^ 2))
        ≤ 2 * ((-α) * (x t 0 ^ 2) + (-α) * (x t 1 ^ 2)) := by linarith [h_sum_le]
      _ = -2 * α * (x t 0 ^ 2 + x t 1 ^ 2) := by ring

/-- Master Theorem 4: Strict Asymptotic Decay for Positive α and Non-Zero State.
    If α > 0 and ‖x(t)‖² > 0, the Lyapunov derivative is strictly negative: dV < 0. -/
theorem continuous_lyapunov_strictly_negative (dV : ℝ) (norm_val α : ℝ)
    (h_bound : dV ≤ -2 * α * norm_val)
    (h_alpha_pos : 0 < α)
    (h_norm_pos : 0 < norm_val) :
    dV < 0 := by
  have h_prod : 0 < 2 * α * norm_val := by positivity
  linarith

end InfoGeometry.Attention.ContinuousLyapunovFlow
