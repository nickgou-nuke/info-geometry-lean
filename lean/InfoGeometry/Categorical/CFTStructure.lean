import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring

theorem conformal_spin_single_valued {S : ℝ} (h : ∃ n : ℤ, S = (n : ℝ) / 2) : ∃ m : ℤ, 2 * S = m := by
  obtain ⟨n, hn⟩ := h
  use n
  calc 2 * S = 2 * ((n : ℝ) / 2) := by rw [hn]
       _     = n := by ring
