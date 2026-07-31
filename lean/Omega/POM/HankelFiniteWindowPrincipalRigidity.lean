import Omega.POM.HankelSyndromeModuleKernelEqualsMultiples

namespace Omega.POM

/-- Paper label: `thm:pom-hankel-finite-window-principal-rigidity`. -/
theorem paper_pom_hankel_finite_window_principal_rigidity
    (kernelData : HankelSyndromeKernelEqualsMultiplesData) :
    kernelData.kernelContainedInMultiples ∧ kernelData.multiplesContainedInKernel := by
  exact paper_pom_hankel_syndrome_module_kernel_equals_multiples kernelData

end Omega.POM
