import Mathlib.Tactic

variable {A : Type*} [AddCommGroup A]
theorem test (a b c d : A) : a - b + c - d = a + c - b - d := by
  abel
