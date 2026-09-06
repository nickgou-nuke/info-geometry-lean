import InfoGeometry.Clifford.SplitClifford55SpinOrthogonalTransportBridge
import InfoGeometry.Canonical.Spin55NativeOrthogonalGroupKernelExact

/-!
# Transported Chevalley Spin orthogonal kernel

This owner transports the already proved native `±1` kernel along the
Chevalley/neutral Spin equivalence.  It does not assert surjectivity onto the
full orthogonal group or construct a new Pin/Spin covering theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitClifford55SpinOrthogonalKernelTransportBridge

open InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
open InfoGeometry.Clifford.SplitClifford55SpinOrthogonalTransportBridge
open InfoGeometry.Clifford.Clifford55

def ChevalleySpin55 :=
  InfoGeometry.Clifford.SplitClifford55SpinOrthogonalTransportBridge.ChevalleySpin55

theorem transportedSpinActionOrthogonal_mem_kernel_iff_pm_one
    (g : ChevalleySpin55) :
    g ∈ (transportedSpinActionOrthogonal).ker ↔
      spinGroupTransportEquiv g = 1 ∨
        spinGroupTransportEquiv g = negOneSpin := by
  change spinActionOrthogonalHom (spinGroupTransportEquiv g) = 1 ↔ _
  exact spinActionOrthogonalHom_mem_kernel_iff_pm_one
    (spinGroupTransportEquiv g)

end InfoGeometry.Canonical.SplitClifford55SpinOrthogonalKernelTransportBridge
