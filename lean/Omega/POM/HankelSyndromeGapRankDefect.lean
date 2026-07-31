import Mathlib.Tactic
import Omega.POM.HankelSyndromeModuleKernelEqualsMultiples

namespace Omega.POM

/-- Paper-facing wrapper for the Hankel-syndrome gap quotient: after identifying the kernel with
the multiples for the minimal annihilator, divisibility reversal places the larger-recurrence
module inside it, and monic division by the residual factor gives unique remainder
representatives. Hence the quotient is free abelian and its rank equals the degree defect.
    thm:pom-hankel-syndrome-gap-rank-defect -/
theorem paper_pom_hankel_syndrome_gap_rank_defect
    (kernelEqualsMultiplesData : HankelSyndromeKernelEqualsMultiplesData)
    (minimalKernelIdentified divisibilityReversalEmbedding quotientByMonicFactor
      remainderNormalForm quotientFreeAbelian rankEqDefect : Prop)
    (deriveMinimalKernelIdentified :
      kernelEqualsMultiplesData.kernelContainedInMultiples →
        kernelEqualsMultiplesData.multiplesContainedInKernel → minimalKernelIdentified)
    (deriveDivisibilityReversalEmbedding :
      minimalKernelIdentified → divisibilityReversalEmbedding)
    (deriveQuotientByMonicFactor :
      minimalKernelIdentified → divisibilityReversalEmbedding → quotientByMonicFactor)
    (deriveRemainderNormalForm : quotientByMonicFactor → remainderNormalForm)
    (deriveQuotientFreeAbelian :
      quotientByMonicFactor → remainderNormalForm → quotientFreeAbelian)
    (deriveRankEqDefect :
      quotientByMonicFactor → remainderNormalForm → rankEqDefect) :
    quotientFreeAbelian ∧ rankEqDefect := by
  rcases
      paper_pom_hankel_syndrome_module_kernel_equals_multiples kernelEqualsMultiplesData with
    ⟨hKernelContainedInMultiples, hMultiplesContainedInKernel⟩
  have hMinimalKernelIdentified : minimalKernelIdentified :=
    deriveMinimalKernelIdentified hKernelContainedInMultiples hMultiplesContainedInKernel
  have hDivisibilityReversalEmbedding : divisibilityReversalEmbedding :=
    deriveDivisibilityReversalEmbedding hMinimalKernelIdentified
  have hQuotientByMonicFactor : quotientByMonicFactor :=
    deriveQuotientByMonicFactor hMinimalKernelIdentified hDivisibilityReversalEmbedding
  have hRemainderNormalForm : remainderNormalForm :=
    deriveRemainderNormalForm hQuotientByMonicFactor
  exact ⟨deriveQuotientFreeAbelian hQuotientByMonicFactor hRemainderNormalForm,
    deriveRankEqDefect hQuotientByMonicFactor hRemainderNormalForm⟩

end Omega.POM
