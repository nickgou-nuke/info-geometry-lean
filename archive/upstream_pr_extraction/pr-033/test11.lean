import Mathlib

variable {A : Type*} [Ring A] [Algebra ℂ A]

lemma test_two : (1 / 2 : ℂ) • (2 : A) = (1 : A) := by
  have : (2 : A) = (2 : ℂ) • (1 : A) := by
    exact (map_ofNat (algebraMap ℂ A) 2).symm ▸ (Algebra.smul_def 2 (1:A)).symm ▸ mul_one _
