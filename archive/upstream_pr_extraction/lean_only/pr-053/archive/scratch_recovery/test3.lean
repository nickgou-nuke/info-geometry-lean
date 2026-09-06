import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

example (a b c d x y pos : ℝ) (hpos : (c * x + d) ^ 2 + (c * y) ^ 2 > 0) (hdet : a * d - b * c = 1) :
    y / ((c * x + d) ^ 2 + (c * y) ^ 2) =
    (-(a * x + b) * (c * y) + (a * y) * (c * x + d)) / ((c * x + d) ^ 2 + (c * y) ^ 2) := by
  have : (-(a * x + b) * (c * y) + (a * y) * (c * x + d)) = y * (a * d - b * c) := by ring
  rw [this, hdet, mul_one]
