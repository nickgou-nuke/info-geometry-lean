import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Quantum.Projective

variable (H : Type*)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

open scoped InnerProductSpace

/-- A normalized state representative in the Hilbert space H with ⟪ψ, ψ⟫_ℂ = 1. -/
structure NormalizedState where
  vec : H
  norm_sq : ⟪vec, vec⟫_ℂ = (1 : ℂ)

theorem NormalizedState.norm_vec_eq_one (ψ : NormalizedState) : ‖ψ.vec‖ = 1 := by
  have h : ‖ψ.vec‖ ^ 2 = re ⟪ψ.vec, ψ.vec⟫_ℂ := inner_self_eq_norm_sq ψ.vec
  rw [h, ψ.norm_sq]
  simp

end InfoGeometry.Quantum.Projective

end noncomputable section
