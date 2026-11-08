import Mathlib

variable {Op : Type*} [Ring Op]
variable (a b : Op)

example (h : a * a = 0) : a * a * b * a = 0 := by
  rw [mul_assoc]
  rw [h]
  simp

example (h : a * a = 0) : a * a * b * a + a * b * a * a = 0 := by
  have h1 : a * a * b * a = 0 := by
    rw [mul_assoc]
    rw [h]
    simp
  have h2 : a * b * a * a = 0 := by
    rw [mul_assoc]
    rw [h]
    simp
  rw [h1, h2]
  simp
