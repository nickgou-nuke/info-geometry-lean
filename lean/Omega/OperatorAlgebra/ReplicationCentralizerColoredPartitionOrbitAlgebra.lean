import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Admissible colored partitions, orbit classification, and the stated derivation laws yield the
equivariance, commutant basis, diagram composition, loop compatibility, and centralizer
isomorphism conclusions. -/
theorem paper_op_algebra_replication_centralizer_colored_partition_orbit_algebra
    (admissibleColoredPartitionOperators qTupleOrbitClassification : Prop)
    (gmEquivariance commutantBasis compositionMatchesDiagramConcatenation
      loopWeightCompatibility orbitAlgebraIsomorphicToCentralizer : Prop)
    (admissibleColoredPartitionOperators_h : admissibleColoredPartitionOperators)
    (qTupleOrbitClassification_h : qTupleOrbitClassification)
    (deriveGmEquivariance :
      admissibleColoredPartitionOperators → gmEquivariance)
    (deriveCommutantBasis :
      gmEquivariance → qTupleOrbitClassification → commutantBasis)
    (deriveCompositionMatchesDiagramConcatenation :
      admissibleColoredPartitionOperators → compositionMatchesDiagramConcatenation)
    (deriveLoopWeightCompatibility :
      admissibleColoredPartitionOperators → loopWeightCompatibility)
    (deriveOrbitAlgebraIsomorphism :
      commutantBasis → compositionMatchesDiagramConcatenation →
        loopWeightCompatibility → orbitAlgebraIsomorphicToCentralizer) :
    gmEquivariance ∧ commutantBasis ∧ compositionMatchesDiagramConcatenation ∧
      loopWeightCompatibility ∧ orbitAlgebraIsomorphicToCentralizer := by
  have hEquivariance : gmEquivariance :=
    deriveGmEquivariance admissibleColoredPartitionOperators_h
  have hBasis : commutantBasis :=
    deriveCommutantBasis hEquivariance qTupleOrbitClassification_h
  have hComposition : compositionMatchesDiagramConcatenation :=
    deriveCompositionMatchesDiagramConcatenation admissibleColoredPartitionOperators_h
  have hLoops : loopWeightCompatibility :=
    deriveLoopWeightCompatibility admissibleColoredPartitionOperators_h
  exact ⟨hEquivariance, hBasis, hComposition, hLoops,
    deriveOrbitAlgebraIsomorphism hBasis hComposition hLoops⟩

end Omega.OperatorAlgebra
