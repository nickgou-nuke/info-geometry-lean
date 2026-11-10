import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The chapter-local cubic used to model collision-pressure branch formation. -/
def real_input_40_collision_branch_radius_cubic (u x : ℚ) : ℚ :=
  x ^ (3 : ℕ) - 3 * x + (u - 5 / 2)

/-- The derivative of the cubic with respect to the spectral variable. -/
def real_input_40_collision_branch_radius_cubic_deriv (x : ℚ) : ℚ :=
  3 * x ^ (2 : ℕ) - 3

/-- The explicit cubic discriminant factorization. -/
def real_input_40_collision_branch_radius_discriminant (u : ℚ) : ℚ :=
  -27 * (u - 1 / 2) * (u - 9 / 2)

/-- The real logarithm of the left branch point `u = 1 / 2`. -/
def real_input_40_collision_branch_radius_theta_left : ℝ :=
  -Real.log 2

/-- The real logarithm of the right branch point `u = 9 / 2`. -/
def real_input_40_collision_branch_radius_theta_right : ℝ :=
  Real.log (9 / 2 : ℝ)

/-- The smaller of the distances from zero to the two displayed real logarithmic endpoints.
This finite minimum is not asserted to be the analytic Taylor radius of a function. -/
def real_input_40_collision_branch_radius_nearest_real_endpoint_distance : ℝ :=
  min |real_input_40_collision_branch_radius_theta_left|
    |real_input_40_collision_branch_radius_theta_right|

/-! The checked conclusions below concern the two specified endpoint roots, their real logarithms,
and the minimum of the two real endpoint distances. They do not classify all roots or prove a
complex-analytic Taylor-radius statement. -/

/-- The factorized quadratic in `u` agrees with the centered discriminant expression. -/
lemma real_input_40_collision_branch_radius_discriminant_identity (u : ℚ) :
    108 - 27 * (u - 5 / 2) ^ 2 =
      real_input_40_collision_branch_radius_discriminant u := by
  unfold real_input_40_collision_branch_radius_discriminant
  ring

/-- Paper label: `cor:real-input-40-collision-branch-radius`. Verifies the two displayed repeated-root
examples, the centered quadratic factorization, their real logarithmic preimages, and the minimum
of those two endpoint distances. This statement does not assert these are all branch points. -/
theorem paper_real_input_40_collision_branch_radius
    : real_input_40_collision_branch_radius_cubic (1 / 2) (-1) = 0 ∧
        real_input_40_collision_branch_radius_cubic_deriv (-1) = 0 ∧
        real_input_40_collision_branch_radius_discriminant (1 / 2) = 0 ∧
        real_input_40_collision_branch_radius_cubic (9 / 2) 1 = 0 ∧
        real_input_40_collision_branch_radius_cubic_deriv 1 = 0 ∧
        real_input_40_collision_branch_radius_discriminant (9 / 2) = 0 ∧
        (∀ u : ℚ,
          108 - 27 * (u - 5 / 2) ^ 2 =
            real_input_40_collision_branch_radius_discriminant u) ∧
        Real.exp real_input_40_collision_branch_radius_theta_left = (1 / 2 : ℝ) ∧
        Real.exp real_input_40_collision_branch_radius_theta_right = (9 / 2 : ℝ) ∧
        real_input_40_collision_branch_radius_nearest_real_endpoint_distance = Real.log 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold real_input_40_collision_branch_radius_cubic
    norm_num
  · unfold real_input_40_collision_branch_radius_cubic_deriv
    norm_num
  · unfold real_input_40_collision_branch_radius_discriminant
    norm_num
  · unfold real_input_40_collision_branch_radius_cubic
    norm_num
  · unfold real_input_40_collision_branch_radius_cubic_deriv
    norm_num
  · unfold real_input_40_collision_branch_radius_discriminant
    norm_num
  · intro u
    exact real_input_40_collision_branch_radius_discriminant_identity u
  · unfold real_input_40_collision_branch_radius_theta_left
    have htwo : (0 : ℝ) < 2 := by norm_num
    calc
      Real.exp (-Real.log 2) = (Real.exp (Real.log 2))⁻¹ := by rw [Real.exp_neg]
      _ = (2 : ℝ)⁻¹ := by rw [Real.exp_log htwo]
      _ = (1 / 2 : ℝ) := by norm_num
  · unfold real_input_40_collision_branch_radius_theta_right
    have hpos : (0 : ℝ) < 9 / 2 := by norm_num
    rw [Real.exp_log hpos]
  · unfold real_input_40_collision_branch_radius_nearest_real_endpoint_distance
      real_input_40_collision_branch_radius_theta_left
      real_input_40_collision_branch_radius_theta_right
    have hlog2_nonneg : 0 ≤ Real.log 2 := by
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hlog92_nonneg : 0 ≤ Real.log (9 / 2 : ℝ) := by
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ (9 / 2 : ℝ))
    have hlog_le : Real.log 2 ≤ Real.log (9 / 2 : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn (by simp) (by norm_num) (by norm_num)
    have hneg : -Real.log 2 ≤ 0 := by linarith
    simpa [abs_of_nonpos hneg, abs_of_nonneg hlog92_nonneg] using min_eq_left hlog_le

end

end Omega.SyncKernelRealInput
