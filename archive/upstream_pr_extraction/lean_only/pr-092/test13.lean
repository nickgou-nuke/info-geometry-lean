import Mathlib

variable {A : Type*} [Ring A] [Algebra ℂ A]

lemma test_two : (1 / 2 : ℂ) • (2 : A) = (1 : A) := by
  have h1 : (1 / 2 : ℂ) • (2 : A) = (1 / 2 : ℂ) • algebraMap ℂ A (2 : ℂ) := by
    congr 1
    exact (map_ofNat (algebraMap ℂ A) 2).symm
  rw [h1]
  rw [Algebra.smul_def]
  rw [← map_mul]
  have h3 : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  rw [h3]
  exact map_one (algebraMap ℂ A)
