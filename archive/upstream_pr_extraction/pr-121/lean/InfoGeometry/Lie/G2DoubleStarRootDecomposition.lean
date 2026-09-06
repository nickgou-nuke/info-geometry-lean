import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-!
# The two six-element sectors of the native `G₂` root readback

This file records the finite, kernel-checkable content of the “double star”
picture.  The two sectors are the already computed short- and long-index
sets; no Euclidean drawing or unproved angular identification is introduced.
-/

namespace InfoGeometry.Lie.G2DoubleStarRootDecomposition

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

def doubleStarIndices : Finset (Fin 14) :=
  shortRootIndices ∪ longRootIndices

theorem short_long_disjoint :
    Disjoint shortRootIndices longRootIndices := by
  decide

theorem doubleStarIndices_card : doubleStarIndices.card = 12 := by
  decide

theorem doubleStarIndices_eq_nonzero_root_indices :
    doubleStarIndices = {j | rootWeight j ≠ 0} := by
  ext j
  change j ∈ doubleStarIndices ↔ rootWeight j ≠ 0
  simp only [ne_eq, rootWeight_eq_zero_iff]
  fin_cases j <;>
    simp [doubleStarIndices, shortRootIndices, longRootIndices]

end InfoGeometry.Lie.G2DoubleStarRootDecomposition
