import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

lemma test_5 : (2 : ℝ)⁻¹ * (-1 + -1) = -1 := by
  linarith
