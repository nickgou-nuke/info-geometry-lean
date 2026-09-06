import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Quantum.Projective

open scoped InnerProductSpace

/-- A normalized state representative in the Hilbert space H with ⟪ψ, ψ⟫_ℂ = 1. -/
structure NormalizedState (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  vec : H
  norm_sq : ⟪vec, vec⟫_ℂ = (1 : ℂ)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem NormalizedState.norm_vec_eq_one (ψ : NormalizedState H) : ‖ψ.vec‖ = 1 := by
  have h := ψ.norm_sq
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : (‖ψ.vec‖ : ℂ) ^ 2 = (1 : ℂ) := h
  have h3 : (‖ψ.vec‖ ^ 2 : ℝ) = 1 := by
    exact_mod_cast h2
  have _h4 : 0 ≤ ‖ψ.vec‖ := norm_nonneg _
  nlinarith

end InfoGeometry.Quantum.Projective

end noncomputable section
