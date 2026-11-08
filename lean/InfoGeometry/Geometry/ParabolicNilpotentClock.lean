import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import InfoGeometry.Clifford.NilpotentBinomial

/-!
# A finite parabolic clock

This owner records the exact algebraic content of a square-zero unipotent
flow.  It is independent of any Wasserstein minimization or continuum limit.
-/

namespace InfoGeometry.Geometry.ParabolicNilpotentClock

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R

structure Clock where
  generator : Mat2
  square_zero : generator * generator = 0

def step (c : Clock) (t : ℝ) : Mat2 :=
  (1 : Mat2) + t • c.generator

def act (c : Clock) (t : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (step c t).mulVec x

theorem step_add (c : Clock) (s t : ℝ) :
    step c s * step c t = step c (s + t) := by
  unfold step
  calc
    ((1 : Mat2) + s • c.generator) * ((1 : Mat2) + t • c.generator) =
        (1 : Mat2) + s • c.generator + t • c.generator +
          (s * t) • (c.generator * c.generator) := by
      simp [add_mul, mul_add, c.square_zero, add_assoc]
    _ = (1 : Mat2) + (s + t) • c.generator := by
      rw [c.square_zero, smul_zero, add_zero, add_smul]
      simp [add_assoc]

@[simp] theorem step_zero (c : Clock) : step c 0 = 1 := by
  simp [step]

theorem step_mul_step_neg (c : Clock) (t : ℝ) :
    step c t * step c (-t) = 1 := by
  calc
    step c t * step c (-t) = step c (t + -t) := step_add c t (-t)
    _ = 1 := by simp

theorem step_neg_mul_step (c : Clock) (t : ℝ) :
    step c (-t) * step c t = 1 := by
  calc
    step c (-t) * step c t = step c (-t + t) := step_add c (-t) t
    _ = 1 := by simp

theorem step_pow (c : Clock) (t : ℝ) (n : ℕ) :
    step c t ^ n = 1 + n • (t • c.generator) := by
  unfold step
  apply InfoGeometry.Clifford.NilpotentBinomial.one_add_pow_of_sq_zero
  simp [c.square_zero]

theorem step_pow_eq_step_nat_mul (c : Clock) (t : ℝ) (n : ℕ) :
    step c t ^ n = step c ((n : ℝ) * t) := by
  rw [step_pow]
  unfold step
  rw [← Nat.cast_smul_eq_nsmul ℝ n]
  simp [smul_smul, mul_comm]

theorem act_add (c : Clock) (s t : ℝ) (x : Fin 2 → ℝ) :
    act c s (act c t x) = act c (s + t) x := by
  unfold act
  rw [Matrix.mulVec_mulVec, step_add]

end InfoGeometry.Geometry.ParabolicNilpotentClock
