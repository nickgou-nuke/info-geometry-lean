import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55RealSplitPinKernelScalarCase

namespace InfoGeometry.Clifford.Clifford55

noncomputable section

theorem realSplitPin_kernel_pm_one_or_uniform_anticommutation
    (g : realSplitPin55)
    (hg : g ∈ (realSplitPinOrthogonalAction).ker) :
    ((g : Cl55ˣ) = 1 ∨ (g : Cl55ˣ) = -1) ∨
      ∀ v : V55,
        ((g : Cl55ˣ) : Cl55) * ι55 v =
          -(ι55 v * ((g : Cl55ˣ) : Cl55)) := by
  rcases realSplitPin_kernel_center_or_uniform_anticommutation g hg with
    hcenter | hanti
  · left
    exact realSplitPin_kernel_pm_one_of_native_center g hcenter
  · right
    exact hanti

end

end InfoGeometry.Clifford.Clifford55
