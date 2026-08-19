import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Quantum.Projective

/-- A normalized state representative in the Hilbert space H with ⟪ψ, ψ⟫_ℂ = 1. -/
structure NormalizedState (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  vec : H
  norm_sq : ⟪vec, vec⟫_ℂ = (1 : ℂ)

local notation "EndH" (H := ?_) [inst : _] => H →L[ℂ] H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem NormalizedState.norm_vec_eq_one (ψ : NormalizedState H) : ‖ψ.vec‖ = 1 :=
  ψ.norm_eq_one

end InfoGeometry.Quantum.Projective

end noncomputable section
