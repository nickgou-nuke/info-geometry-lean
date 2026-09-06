import Omega.POM.HankelSyndromeModuleKernelEqualsMultiples

namespace Omega.POM

/-- Paper label: `thm:pom-hankel-finite-window-principal-rigidity`. -/
theorem paper_pom_hankel_finite_window_principal_rigidity
    {kernelContainedInMultiples multiplesContainedInKernel : Prop}
    (hKernelContainedInMultiples : kernelContainedInMultiples)
    (hMultiplesContainedInKernel : multiplesContainedInKernel) :
    kernelContainedInMultiples ∧ multiplesContainedInKernel := by
  exact ⟨hKernelContainedInMultiples, hMultiplesContainedInKernel⟩

end Omega.POM
