import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Ring

theorem gogberashvili_norm_eq_circular (ω t : ℝ) (c : ℝ) (λ x : Fin 3 → ℝ) :
  ω^2 - (∑ i, λ i * λ i) + (∑ i, x i * x i) - c^2 * t^2 =
    (ω + c * t) * (ω - c * t) - ∑ i, (λ i - x i) * (λ i + x i) := by
  calc
    ω^2 - (∑ i, λ i * λ i) + (∑ i, x i * x i) - c^2 * t^2
      = ω^2 - c^2 * t^2 - ((∑ i, λ i * λ i) - (∑ i, x i * x i)) := by ring
    _ = (ω + c * t) * (ω - c * t) - ∑ i, (λ i - x i) * (λ i + x i) := by
      congr 1
      · ring
      · rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring

