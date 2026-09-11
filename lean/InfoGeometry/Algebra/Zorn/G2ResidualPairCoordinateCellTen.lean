import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity

namespace InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellTen

open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

abbrev ResidualPair :=
  InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent ×
    InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent

def residualPair (i : Fin 189) : ResidualPair :=
  (factorWordExponent (gapLeftWitness 10 i),
    factorWordExponent (gapRightWitness 10 i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem residualPair_injective_on_cell_ten :
    ∀ i j : Fin 189,
      i ∈ orbitCells 10 → j ∈ orbitCells 10 →
      residualPair i = residualPair j → i = j := by
  intro i j hi hj h
  simp [orbitCells, flagCells] at hi hj
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals first | rfl | (exfalso; revert h; decide)

theorem residualPair_cell_ten_coordinate_separation :
    ∀ i j : Fin 189,
      i ∈ orbitCells 10 → j ∈ orbitCells 10 → i ≠ j →
      residualPair i ≠ residualPair j := by
  intro i j hi hj hne heq
  exact hne (residualPair_injective_on_cell_ten i j hi hj heq)

end InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellTen
