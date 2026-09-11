import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity

namespace InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellZero

open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

abbrev ResidualPair :=
  InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent ×
    InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent

def residualPair (i : Fin 189) : ResidualPair :=
  (factorWordExponent (gapLeftWitness 0 i),
    factorWordExponent (gapRightWitness 0 i))

theorem residualPair_injective_on_cell_zero :
    ∀ i j : Fin 189,
      i ∈ orbitCells 0 → j ∈ orbitCells 0 →
      residualPair i = residualPair j → i = j := by
  intro i j hi hj h
  have hi0 : i = 0 := by
    simpa [orbitCells, flagCells] using hi
  have hj0 : j = 0 := by
    simpa [orbitCells, flagCells] using hj
  exact hi0.trans hj0.symm

theorem residualPair_cell_zero_coordinate_separation :
    ∀ i j : Fin 189,
      i ∈ orbitCells 0 → j ∈ orbitCells 0 → i ≠ j →
      residualPair i ≠ residualPair j := by
  intro i j hi hj hne heq
  exact hne (residualPair_injective_on_cell_zero i j hi hj heq)

end InfoGeometry.Algebra.Zorn.G2ResidualPairCoordinateCellZero
