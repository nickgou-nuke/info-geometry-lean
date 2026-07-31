import Mathlib.Tactic

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the strict inverse Schur tomography statement in the
POM chapter.
    thm:pom-schur-tomography-inverse-partition-monomials -/
theorem paper_pom_schur_tomography_inverse_partition_monomials
    {forwardSchurTomography characterWeightedSummation columnOrthogonality
        partitionMonomialRecovered : Prop}
    (hForwardSchurTomography : forwardSchurTomography)
    (hCharacterWeightedSummation : characterWeightedSummation)
    (hColumnOrthogonality : columnOrthogonality)
    (derivePartitionMonomialRecovered :
      forwardSchurTomography → characterWeightedSummation →
        columnOrthogonality → partitionMonomialRecovered) :
    forwardSchurTomography ∧ columnOrthogonality ∧ partitionMonomialRecovered := by
  have hRecovered : partitionMonomialRecovered :=
    derivePartitionMonomialRecovered hForwardSchurTomography
      hCharacterWeightedSummation hColumnOrthogonality
  exact ⟨hForwardSchurTomography, hColumnOrthogonality, hRecovered⟩

end Omega.POM
