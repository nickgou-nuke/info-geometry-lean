import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.MassSpectrometry.BirkhoffAssignment

/-!
# Sinkhorn assignment bridge

The numerical normalization primitives are owned by
`InfoGeometry.Canonical.MoE` in `SinkhornFoundation`.  This module only gives
those constructions peak-fragment assignment names and re-exports their exact
normalization identities.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

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

end SinkhornAssignment

end InfoGeometry.MassSpectrometry
