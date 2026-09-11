import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ResidualCoordinateReadback

namespace InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellTwo

open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

abbrev ResidualPair :=
  InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent ×
    InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent

def residualPair (k : Fin 12) (i : Fin 189) : ResidualPair :=
  (factorWordExponent (gapLeftWitness k i),
    factorWordExponent (gapRightWitness k i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem residualPair_injective_on_cell_two :
    ∀ i j : Fin 189,
      i ∈ orbitCells 2 → j ∈ orbitCells 2 →
      residualPair 2 i = residualPair 2 j → i = j := by
  intro i j hi hj h
  simp [orbitCells, flagCells] at hi hj
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | (exfalso; revert h; decide)

theorem residualPair_cell_two_coordinate_separation :
    ∀ i j : Fin 189,
      i ∈ orbitCells 2 → j ∈ orbitCells 2 → i ≠ j →
      residualPair 2 i ≠ residualPair 2 j := by
  intro i j hi hj hne heq
  exact hne (residualPair_injective_on_cell_two i j hi hj heq)

end InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellTwo
