import Mathlib.Analysis.Convex.Birkhoff
import InfoGeometry.MassSpectrometry.PeakFragmentMatching

/-!
# Birkhoff assignment bridge

Soft peak-fragment assignments are not redefined locally: they are exactly
Mathlib doubly-stochastic matrices. The Birkhoff-von Neumann decomposition is
re-exported in mass-spectrometry language and tied back to the repository's
perfect-matching support theorem.
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

/-- Every hard assignment has perfect-matching support. -/
theorem hardAssignment_isPerfectMatching {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    InfoGeometry.Routing.PermutationPerfectMatching.IsPerfectMatching
      (InfoGeometry.Routing.PermutationPerfectMatching.matrixSupport
        (hardAssignment σ)) :=
  hardAssignment_support_isPerfectMatching σ

/-- Every soft assignment is a convex combination of hard assignments. -/
theorem softAssignment_birkhoff_decomposition {n : ℕ}
    (A : AssignmentMatrix n) (hA : IsSoftAssignment A) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • hardAssignment σ = A := by
  simpa [IsSoftAssignment, hardAssignment] using
    (exists_eq_sum_perm_of_mem_doublyStochastic (M := A) hA)

/--
A soft assignment is therefore a simplex mixture of matrices whose supports
are all genuine perfect matchings.  This is the precise theorem-safe form of
"soft assignment as a distribution over hard matchings"; no uniqueness of the
Birkhoff weights is asserted.
-/
theorem softAssignment_decomposes_over_perfectMatchings {n : ℕ}
    (A : AssignmentMatrix n) (hA : IsSoftAssignment A) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • hardAssignment σ = A ∧
      ∀ σ,
        InfoGeometry.Routing.PermutationPerfectMatching.IsPerfectMatching
          (InfoGeometry.Routing.PermutationPerfectMatching.matrixSupport
            (hardAssignment σ)) := by
  rcases softAssignment_birkhoff_decomposition A hA with
    ⟨w, hw, hsum, hmatrix⟩
  exact ⟨w, hw, hsum, hmatrix, hardAssignment_isPerfectMatching⟩

end InfoGeometry.MassSpectrometry
