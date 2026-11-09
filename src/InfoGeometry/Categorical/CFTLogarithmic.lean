import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

theorem logarithmic_l0_nilpotent {R : Type} [Ring R] (h N : R) (hN : N^2 = 0) : (h + N - h)^2 = 0 := by
  have h1 : h + N - h = N := by abel
  rw [h1]
  exact hN
