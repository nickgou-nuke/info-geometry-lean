import Mathlib

variable {A : Type*} [Ring A] [Algebra ℂ A]

lemma test_two : (1 / 2 : ℂ) • (2 : A) = (1 : A) := by
  have h1 : (2 : A) = algebraMap ℂ A (2 : ℂ) := by simp
  have h2 : (1 : A) = algebraMap ℂ A (1 : ℂ) := by simp
  rw [h1, h2, ← map_mul]
  have h3 : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  rw [h3]
  -- wait, (1/2:ℂ) • algebraMap ℂ A (2:ℂ)
  -- = algebraMap ℂ A (1/2 * 2)
  -- This is true by Algebra.smul_def!
