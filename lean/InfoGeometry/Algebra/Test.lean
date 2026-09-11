import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

lemma test1 (H : A) (H2 : H*H = 1) : ((1:A) + H)^2 = (1+1:A) + (H+H) := by
  have H2' : H * H = 1 := H2
  calc
    ((1:A) + H)^2 = (1 + H) * (1 + H) := by rw [sq]
    _ = (1+1:A) + (H+H) := by
      simp only [add_mul, mul_add, one_mul, mul_one, H2']
      abel

lemma test2 (H : A) (H2 : H*H = 1) : ((1:A) - H)^2 = (1+1:A) - (H+H) := by
  have H2' : H * H = 1 := H2
  calc
    ((1:A) - H)^2 = (1 - H) * (1 - H) := by rw [sq]
    _ = (1+1:A) - (H+H) := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, H2']
      abel
