import InfoGeometry.Clifford.Cl55WittFullOrthogonalSurjectivity
import InfoGeometry.Clifford.Cl55RealSplitPinKernelExact

namespace InfoGeometry.Clifford.Clifford55

/-!
# Projective quotient of the corrected split-Pin action

The explicit real split-Pin action is already surjective onto the native
orthogonal group.  Quotienting by its actual action kernel therefore gives a
canonical projective group model of `O(5,5)`, without presupposing that the
kernel has been classified as the scalar signs.
-/

abbrev realSplitPinOrthogonalQuotient :=
  realSplitPin55 ⧸ (realSplitPinOrthogonalAction).ker

noncomputable def realSplitPinOrthogonalQuotientEquiv :
    realSplitPinOrthogonalQuotient ≃* orthogonalGroup55 :=
  QuotientGroup.quotientKerEquivOfSurjective
    realSplitPinOrthogonalAction
    realSplitPinOrthogonalAction_surjective

theorem realSplitPinOrthogonalQuotientEquiv_mk
    (g : realSplitPin55) :
    realSplitPinOrthogonalQuotientEquiv (QuotientGroup.mk g) =
      realSplitPinOrthogonalAction g := by
  rfl

noncomputable def realSplitPinSignQuotientEquiv :
    (realSplitPin55 ⧸
      (realSplitPinSignSubgroup : Subgroup realSplitPin55)) ≃*
      orthogonalGroup55 := by
  exact
    (QuotientGroup.quotientMulEquivOfEq
      realSplitPinOrthogonalAction_kernel_eq_signSubgroup).symm.trans
      realSplitPinOrthogonalQuotientEquiv

end InfoGeometry.Clifford.Clifford55
