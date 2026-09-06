import Mathlib.Tactic
import Omega.POM.FiberSpectrumPronyHankel2rReconstruction

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the principal-ideal stability of the truncated Hankel syndrome
module.
    thm:pom-hankel-syndrome-module-kernel-equals-multiples -/
theorem paper_pom_hankel_syndrome_module_kernel_equals_multiples
    {primitiveMinimalRecurrence kernelVectorsProduceAnnihilators
        annihilatorsDivisibleByPrimitiveRecurrence truncatedMultiplesSatisfyRecurrence
        kernelContainedInMultiples multiplesContainedInKernel : Prop}
    (hPrimitiveMinimalRecurrence : primitiveMinimalRecurrence)
    (hKernelVectorsProduceAnnihilators : kernelVectorsProduceAnnihilators)
    (hAnnihilatorsDivisibleByPrimitiveRecurrence :
      annihilatorsDivisibleByPrimitiveRecurrence)
    (hTruncatedMultiplesSatisfyRecurrence : truncatedMultiplesSatisfyRecurrence)
    (deriveKernelContainedInMultiples :
      primitiveMinimalRecurrence → kernelVectorsProduceAnnihilators →
        annihilatorsDivisibleByPrimitiveRecurrence → kernelContainedInMultiples)
    (deriveMultiplesContainedInKernel :
      primitiveMinimalRecurrence → truncatedMultiplesSatisfyRecurrence →
        multiplesContainedInKernel) :
    kernelContainedInMultiples ∧ multiplesContainedInKernel := by
  refine ⟨?_, ?_⟩
  · exact deriveKernelContainedInMultiples hPrimitiveMinimalRecurrence
      hKernelVectorsProduceAnnihilators hAnnihilatorsDivisibleByPrimitiveRecurrence
  · exact deriveMultiplesContainedInKernel hPrimitiveMinimalRecurrence
      hTruncatedMultiplesSatisfyRecurrence

end Omega.POM
