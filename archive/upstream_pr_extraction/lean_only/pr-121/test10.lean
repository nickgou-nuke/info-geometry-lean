import Mathlib

variable {A : Type*} [Ring A] [Algebra ℂ A]

lemma test_two : (1 / 2 : ℂ) • (2 : A) = (1 : A) := by
  have : (2 : A) = (2 : ℂ) • (1 : A) := by
    rw [Algebra.smul_def]
    simp
  rw [this]
  rw [← smul_smul]
  have : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  rw [this]
  exact one_smul ℂ (1 : A)
