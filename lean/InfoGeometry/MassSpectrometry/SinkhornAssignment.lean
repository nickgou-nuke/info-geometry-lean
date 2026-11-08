import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.MassSpectrometry.BirkhoffAssignment

/-!
# Sinkhorn assignment bridge

The numerical normalization primitives are owned by
`InfoGeometry.Canonical.MoE` in `SinkhornFoundation`. This module only gives
those constructions peak-fragment assignment names, re-exports their exact
normalization identities, and provides a proof-carrying handoff from diagonal
balancing to Mathlib's Birkhoff polytope.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open Matrix
open scoped BigOperators

namespace SinkhornAssignment

open InfoGeometry.Canonical.MoE

abbrev SinkhornMatrix (n : ℕ) := InfoGeometry.Canonical.MoE.SinkhornMatrix n

abbrev HasPositiveRowSums (n : ℕ) (M : SinkhornMatrix n) : Prop :=
  InfoGeometry.Canonical.MoE.HasPositiveRowSums n M

abbrev HasPositiveColSums (n : ℕ) (M : SinkhornMatrix n) : Prop :=
  InfoGeometry.Canonical.MoE.HasPositiveColSums n M

/-- One repository-owned row normalization step. -/
def rowNormalize {n : ℕ} (M : SinkhornMatrix n) (h : HasPositiveRowSums n M) :
    SinkhornMatrix n :=
  InfoGeometry.Canonical.MoE.rowNormalize n M h

/-- One repository-owned column normalization step. -/
def colNormalize {n : ℕ} (M : SinkhornMatrix n) (h : HasPositiveColSums n M) :
    SinkhornMatrix n :=
  InfoGeometry.Canonical.MoE.colNormalize n M h

/-- Row normalization gives unit row sums exactly. -/
theorem rowNormalize_row_sum_one {n : ℕ}
    (M : SinkhornMatrix n) (h : HasPositiveRowSums n M) (i : Fin n) :
    ∑ j, rowNormalize M h i j = 1 := by
  exact InfoGeometry.Canonical.MoE.rowSum_rowNormalize (n := n) M h i

/-- Column normalization gives unit column sums exactly. -/
theorem colNormalize_col_sum_one {n : ℕ}
    (M : SinkhornMatrix n) (h : HasPositiveColSums n M) (j : Fin n) :
    ∑ i, colNormalize M h i j = 1 := by
  exact InfoGeometry.Canonical.MoE.colSum_colNormalize (n := n) M h j

/--
Certificate that positive left/right diagonal scaling has produced a genuine
soft assignment.  No convergence statement is hidden in this structure.
-/
structure BalanceCertificate {n : ℕ} (M : SinkhornMatrix n) where
  leftScale : Fin n → ℝ
  rightScale : Fin n → ℝ
  leftScale_pos : ∀ i, 0 < leftScale i
  rightScale_pos : ∀ j, 0 < rightScale j
  balanced_soft :
    IsSoftAssignment
      (Matrix.diagonal leftScale * M * Matrix.diagonal rightScale)

/-- Matrix certified by a two-sided diagonal balance. -/
def balancedMatrix {n : ℕ} {M : SinkhornMatrix n}
    (cert : BalanceCertificate M) : AssignmentMatrix n :=
  Matrix.diagonal cert.leftScale * M * Matrix.diagonal cert.rightScale

/-- A certified balanced matrix lies in Mathlib's Birkhoff polytope. -/
theorem balancedMatrix_isSoftAssignment {n : ℕ} {M : SinkhornMatrix n}
    (cert : BalanceCertificate M) :
    IsSoftAssignment (balancedMatrix cert) := by
  exact cert.balanced_soft

/-- A certified Sinkhorn balance therefore admits a Birkhoff-von Neumann decomposition. -/
theorem balancedMatrix_birkhoff_decomposition {n : ℕ} {M : SinkhornMatrix n}
    (cert : BalanceCertificate M) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • hardAssignment σ = balancedMatrix cert := by
  exact softAssignment_birkhoff_decomposition
    (balancedMatrix cert) (balancedMatrix_isSoftAssignment cert)

end SinkhornAssignment

end InfoGeometry.MassSpectrometry
