import Mathlib.Tactic

theorem my_add_comm (a b : ℕ) : a + b = b + a := by
  exact Nat.add_comm a b

theorem my_add_zero (a : ℕ) : a + 0 = a := by
  exact Nat.add_zero a
