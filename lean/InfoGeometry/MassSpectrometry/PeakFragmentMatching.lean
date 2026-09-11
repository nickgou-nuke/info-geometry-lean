import InfoGeometry.Routing.PermutationPerfectMatching
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Hard peak-fragment matching

Hard one-to-one assignments reuse the repository's canonical permutation
routing owner.  No second perfect-matching implementation is introduced.
-/

namespace InfoGeometry.MassSpectrometry

abbrev AssignmentMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Hard one-to-one peak/fragment assignment. -/
def hardAssignment {n : ℕ} (σ : Equiv.Perm (Fin n)) : AssignmentMatrix n :=
  σ.permMatrix ℝ

/-- The support of every hard assignment is a perfect matching. -/
theorem hardAssignment_support_isPerfectMatching {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    InfoGeometry.Routing.PermutationPerfectMatching.IsPerfectMatching
      (InfoGeometry.Routing.PermutationPerfectMatching.matrixSupport
        (hardAssignment σ)) := by
  simpa [hardAssignment] using
    (InfoGeometry.Routing.PermutationPerfectMatching.permMatrix_support_isPerfectMatching σ)

end InfoGeometry.MassSpectrometry
