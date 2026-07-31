namespace Omega.OperatorAlgebra

/-- Paper-facing wrapper for the fold-invariant subalgebra package: the folded projections are
pairwise orthogonal, sum to the identity, generate the invariant commutative subalgebra, and
exactly capture the observables that are constant on each `Fold`-fiber.
    prop:fold-invariant-subalgebra -/
theorem paper_op_algebra_fold_invariant_subalgebra
    (foldedProjectionConstruction foldFiberPartition foldConditionalExpectationPackage : Prop)
    (hConstruction : foldedProjectionConstruction)
    (hPartitionInput : foldFiberPartition)
    (hConditional : foldConditionalExpectationPackage)
    (orthogonalProjectionFamily partitionOfUnity invariantSubalgebraIso
      fiberwiseConstantCharacterization : Prop)
    (deriveOrthogonalProjectionFamily :
      foldedProjectionConstruction → orthogonalProjectionFamily)
    (derivePartitionOfUnity : foldFiberPartition → partitionOfUnity)
    (deriveInvariantSubalgebraIso :
      orthogonalProjectionFamily → partitionOfUnity → invariantSubalgebraIso)
    (deriveFiberwiseConstantCharacterization :
      invariantSubalgebraIso → foldConditionalExpectationPackage →
        fiberwiseConstantCharacterization) :
    orthogonalProjectionFamily ∧ partitionOfUnity ∧ invariantSubalgebraIso ∧
      fiberwiseConstantCharacterization := by
  have hOrthogonal : orthogonalProjectionFamily :=
    deriveOrthogonalProjectionFamily hConstruction
  have hPartition : partitionOfUnity := derivePartitionOfUnity hPartitionInput
  have hIso : invariantSubalgebraIso :=
    deriveInvariantSubalgebraIso hOrthogonal hPartition
  exact ⟨hOrthogonal, hPartition, hIso,
    deriveFiberwiseConstantCharacterization hIso hConditional⟩

end Omega.OperatorAlgebra
