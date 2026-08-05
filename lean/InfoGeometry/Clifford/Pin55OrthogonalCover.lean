import InfoGeometry.Clifford.Cl55RealSplitPinKernelExact
import InfoGeometry.Clifford.Cl55RealSplitPinImage

namespace InfoGeometry.Clifford.Clifford55

/-!
# Kernel-certified native split-Pin orthogonal action

This owner packages the native corrected split-Pin action together with its
exact sign kernel.  It deliberately does not promote the explicit image
subgroup to the whole orthogonal group: that would be a separate
surjectivity theorem.
-/

noncomputable def realSplitPinOrthogonalCover :
    realSplitPin55 →* orthogonalGroup55 :=
  realSplitPinOrthogonalAction

theorem realSplitPinOrthogonalCover_kernel_eq_signSubgroup :
    (realSplitPinOrthogonalCover).ker = realSplitPinSignSubgroup := by
  exact realSplitPinOrthogonalAction_kernel_eq_signSubgroup

theorem coordinateReflectionSubgroup_le_realSplitPinOrthogonalCover_range :
    coordinateReflectionSubgroup ≤ (realSplitPinOrthogonalCover).range := by
  exact coordinateReflectionSubgroup_le_realSplitPinOrthogonalImage

theorem globalSheetReflectionGenerator_mem_realSplitPinOrthogonalCover_range :
    globalSheetReflectionGenerator ∈ (realSplitPinOrthogonalCover).range := by
  exact globalSheetReflectionGenerator_mem_realSplitPinOrthogonalImage

theorem realSplitPinOrthogonalCover_negOne_mem_kernel :
    realSplitNegOne ∈ (realSplitPinOrthogonalCover).ker := by
  exact realSplitNegOne_mem_kernel

end InfoGeometry.Clifford.Clifford55
