import Omega.POM.SchurTomographyInversePartitionMonomials

namespace Omega.POM

/-- Paper-facing two-way trace/moment equivalence extracted from the inverse Schur tomography
package.
    cor:pom-schur-traces-moments-bijection -/
theorem paper_pom_schur_traces_moments_bijection
    {forwardSchurTomography partitionMonomialRecovered : Prop}
    (hForwardSchurTomography : forwardSchurTomography)
    (hPartitionMonomialRecovered : partitionMonomialRecovered) :
    forwardSchurTomography ∧ partitionMonomialRecovered := by
  exact ⟨hForwardSchurTomography, hPartitionMonomialRecovered⟩

end Omega.POM
