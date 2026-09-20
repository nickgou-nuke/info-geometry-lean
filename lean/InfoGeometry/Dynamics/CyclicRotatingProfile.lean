import Mathlib

namespace InfoGeometry.Dynamics.CyclicRotatingProfile

noncomputable section

def rotatingProfile (profile : ℝ → ℝ) (speed time angle : ℝ) : ℝ :=
  profile (angle - speed * time)

theorem stationary_in_rotating_frame (profile : ℝ → ℝ) (speed time angle : ℝ) :
    rotatingProfile profile speed time (angle + speed * time) = profile angle := by
  simp [rotatingProfile]

theorem periodic_at_each_time (profile : ℝ → ℝ) (period speed time : ℝ)
    (periodic : Function.Periodic profile period) :
    Function.Periodic (rotatingProfile profile speed time) period := by
  intro angle
  change profile (angle + period - speed * time) = profile (angle - speed * time)
  convert periodic (angle - speed * time) using 1 <;> congr 1 <;> ring

theorem time_shift (profile : ℝ → ℝ) (speed time delay angle : ℝ) :
    rotatingProfile profile speed (time + delay) angle =
      rotatingProfile profile speed time (angle - speed * delay) := by
  unfold rotatingProfile
  congr 1
  ring

theorem time_derivative (profile : ℝ → ℝ) (speed time angle slope : ℝ)
    (differentiable : HasDerivAt profile slope (angle - speed * time)) :
    HasDerivAt (fun instant => rotatingProfile profile speed instant angle)
      (slope * (-speed)) time := by
  simpa [rotatingProfile] using differentiable.comp time
    ((hasDerivAt_const time angle).sub ((hasDerivAt_id time).const_mul speed))

def harmonicProfile (lobes : ℕ) (radius amplitude angle : ℝ) : ℝ :=
  radius + amplitude * Real.cos ((lobes : ℝ) * angle)

theorem harmonicProfile_periodic (lobes : ℕ) (positive : 0 < lobes)
    (radius amplitude : ℝ) :
    Function.Periodic (harmonicProfile lobes radius amplitude)
      (2 * Real.pi / (lobes : ℝ)) := by
  have nonzero : (lobes : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  intro angle
  unfold harmonicProfile
  have phase : (lobes : ℝ) * (angle + 2 * Real.pi / (lobes : ℝ)) =
      (lobes : ℝ) * angle + 2 * Real.pi := by
    field_simp [nonzero] <;> ring
  rw [phase, Real.cos_add_two_pi]

theorem harmonicProfile_bounds (lobes : ℕ) (radius amplitude angle : ℝ) :
    radius - |amplitude| ≤ harmonicProfile lobes radius amplitude angle ∧
      harmonicProfile lobes radius amplitude angle ≤ radius + |amplitude| := by
  have bounded : |amplitude * Real.cos ((lobes : ℝ) * angle)| ≤ |amplitude| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg amplitude) (Real.abs_cos_le_one _)
  have sides := abs_le.mp bounded
  unfold harmonicProfile
  constructor <;> linarith [sides.1, sides.2]

theorem harmonicProfile_positive (lobes : ℕ) (radius amplitude angle : ℝ)
    (smallAmplitude : |amplitude| < radius) :
    0 < harmonicProfile lobes radius amplitude angle := by
  have lower := (harmonicProfile_bounds lobes radius amplitude angle).1
  linarith

theorem primitive_phases_distinct {lobes : ℕ} {root : ℂ}
    (primitive : IsPrimitiveRoot root lobes) :
    Function.Injective (fun vertex : Fin lobes => root ^ vertex.val) := by
  intro first second equality
  exact Fin.ext (primitive.pow_inj first.isLt second.isLt equality)

theorem primitive_phase_cycle {lobes : ℕ} {root : ℂ}
    (primitive : IsPrimitiveRoot root lobes) (index : ℕ) :
    root ^ (index + lobes) = root ^ index := by
  rw [pow_add, primitive.pow_eq_one, mul_one]

theorem triangular_phase_equation {root : ℂ} (primitive : IsPrimitiveRoot root 3) :
    root ^ 2 + root + 1 = 0 := by
  have factored : (root - 1) * (root ^ 2 + root + 1) = 0 := by
    calc
      _ = root ^ 3 - 1 := by ring
      _ = 0 := by rw [primitive.pow_eq_one, sub_self]
  exact (mul_eq_zero.mp factored).resolve_left
    (sub_ne_zero.mpr (primitive.ne_one (by norm_num)))

end

end InfoGeometry.Dynamics.CyclicRotatingProfile
