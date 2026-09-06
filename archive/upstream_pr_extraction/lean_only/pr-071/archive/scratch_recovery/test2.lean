import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

example (a b c d x y pos hdet : ℝ) (hdet_eq : a * d - b * c = 1) :
    ((a * x + b) * (c * x + d) + a * c * y ^ 2) / ((c * x + d) ^ 2 + (c * y) ^ 2) =
    (a * c * x ^ 2 + b * c * x + a * d * x + b * d + a * c * y ^ 2) /
      (c ^ 2 * x ^ 2 + 2 * c * d * x + d ^ 2 + c ^ 2 * y ^ 2) := by
  ring
