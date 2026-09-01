import Mathlib.Analysis.Convex.Birkhoff
import InfoGeometry.MassSpectrometry.PeakFragmentMatching

/-!
# Birkhoff assignment bridge

Soft peak-fragment assignments are not redefined locally: they are exactly
Mathlib doubly-stochastic matrices.  The Birkhoff-von Neumann decomposition is
re-exported in mass-spectrometry language.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open Matrix
open scoped BigOperators

/-- Soft assignment = membership in Mathlib's doubly-stochastic polytope. -/
def IsSoftAssignment {n : ℕ} (A : AssignmentMatrix n) : Prop :=
  A ∈ doublyStochastic ℝ (Fin n)

/-- Every hard permutation assignment is a valid soft assignment. -/
theorem hardAssignment_isSoftAssignment {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : IsSoftAssignment (hardAssignment σ) := by
  exact permMatrix_mem_doublyStochastic (R := ℝ) (n := Fin n) (σ := σ)

/-- Every soft assignment is a convex combination of hard assignments. -/
theorem softAssignment_birkhoff_decomposition {n : ℕ}
    (A : AssignmentMatrix n) (hA : IsSoftAssignment A) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • hardAssignment σ = A := by
  simpa [IsSoftAssignment, hardAssignment] using
    (exists_eq_sum_perm_of_mem_doublyStochastic (M := A) hA)

end InfoGeometry.MassSpectrometry
