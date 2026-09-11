import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity

namespace InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellSix

open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

abbrev ResidualPair :=
  InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent ×
    InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent

def residualPair (i : Fin 189) : ResidualPair :=
  (factorWordExponent (gapLeftWitness 6 i),
    factorWordExponent (gapRightWitness 6 i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem residualPair_injective_on_cell_six :
    ∀ i j : Fin 189,
      i ∈ orbitCells 6 → j ∈ orbitCells 6 →
      residualPair i = residualPair j → i = j := by
  intro i j hi hj h
  simp [orbitCells, flagCells] at hi hj
  rcases hi with rfl | rfl <;>
    rcases hj with rfl | rfl
  all_goals first | rfl | (exfalso; revert h; decide)

theorem residualPair_cell_six_coordinate_separation :
    ∀ i j : Fin 189,
      i ∈ orbitCells 6 → j ∈ orbitCells 6 → i ≠ j →
      residualPair i ≠ residualPair j := by
  intro i j hi hj hne heq
  exact hne (residualPair_injective_on_cell_six i j hi hj heq)

end InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellSix
