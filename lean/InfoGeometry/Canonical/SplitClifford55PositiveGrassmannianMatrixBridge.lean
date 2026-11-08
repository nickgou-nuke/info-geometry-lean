import InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering
import InfoGeometry.Clifford.Cl55PositiveGrassmannianSplitBridge

/-!
# Positive `Gr(2,4)` blades in the symmetric `Cl(5,5)` matrix stage

The positive Grassmannian owner maps its exterior two-blade into the native
`Cl(5,5)` algebra and then into the recursive symmetric split presentation.
This bridge records how that same element sits in the matrix realization:
it is fixed by the even projection and killed by the odd projection. The
claim is a parity statement about the represented Clifford element; it does
not identify the Grassmannian itself with a parity subspace.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitClifford55PositiveGrassmannianMatrixBridge

open InfoGeometry.Canonical.SplitCliffordMatrixLimitSoldering
open InfoGeometry.Clifford.Cl55PositiveGrassmannianSplitBridge
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Algebra.SuperGrassmannianClifford
open InfoGeometry.CliffordTower

/-- A positive-chart blade's `Cl(5,5)` image has even matrix parity. The
positive-Grassmannian owner proves native Clifford-even membership, and the
matrix projection theorem transports that membership to the representation.
-/
theorem positiveGrassmannianBlade_matrix_even_odd
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    splitEven 5 (stageMap 5 (positiveGrassmannianBladeSplitImage C)) =
        stageMap 5 (positiveGrassmannianBladeSplitImage C) ∧
      splitOdd 5 (stageMap 5 (positiveGrassmannianBladeSplitImage C)) = 0 := by
  exact splitProjections_stageMap_even 5
    (positiveGrassmannianBladeSplitImage C)
    (positiveGrassmannianBladeSplitImage_mem_even C)

end InfoGeometry.Canonical.SplitClifford55PositiveGrassmannianMatrixBridge

end noncomputable section
