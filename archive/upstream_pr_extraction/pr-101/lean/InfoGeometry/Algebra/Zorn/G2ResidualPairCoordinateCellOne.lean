import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
import InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity

namespace InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellOne

open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

abbrev ResidualPair :=
  InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent ×
    InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent

def residualPair (i : Fin 189) : ResidualPair :=
  (factorWordExponent (gapLeftWitness 1 i),
    factorWordExponent (gapRightWitness 1 i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem residualPair_injective_on_cell_one :
    ∀ i j : Fin 189,
      i ∈ orbitCells 1 → j ∈ orbitCells 1 →
      residualPair i = residualPair j → i = j := by
  intro i j hi hj h
  simp [orbitCells, flagCells] at hi hj
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl
  all_goals first | rfl | (exfalso; revert h; decide)

theorem residualPair_cell_one_coordinate_separation :
    ∀ i j : Fin 189,
      i ∈ orbitCells 1 → j ∈ orbitCells 1 → i ≠ j →
      residualPair i ≠ residualPair j := by
  intro i j hi hj hne heq
  exact hne (residualPair_injective_on_cell_one i j hi hj heq)

end InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellOne
