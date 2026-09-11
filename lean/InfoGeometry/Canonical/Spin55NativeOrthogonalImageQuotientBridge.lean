import InfoGeometry.Canonical.Spin55NativeOrthogonalGroupKernelExact
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Clifford55

/-!
# First-isomorphism packaging for the native `Spin(5,5)` action

The native orthogonal action has an already proved exact kernel, namely the
two scalar signs.  This owner packages the corresponding quotient as the
actual range of the action.  It deliberately makes no surjectivity claim
onto the full orthogonal group or onto a separately chosen special subgroup.
-/

noncomputable def spinNativeOrthogonalImage :=
  (spinActionOrthogonalHom).range

noncomputable def spinNativeOrthogonalQuotientRangeEquiv :
    (Spin55 ⧸ (spinActionOrthogonalHom).ker) ≃*
      spinNativeOrthogonalImage :=
  QuotientGroup.quotientKerEquivRange spinActionOrthogonalHom

theorem spinNativeOrthogonalQuotientRangeEquiv_mk (g : Spin55) :
    spinNativeOrthogonalQuotientRangeEquiv (QuotientGroup.mk g) =
      ⟨spinActionOrthogonalHom g, ⟨g, rfl⟩⟩ := by
  rfl

noncomputable def spinSignQuotientNativeOrthogonalImageEquiv :
    (Spin55 ⧸ (spinSignSubgroup : Subgroup Spin55)) ≃*
      spinNativeOrthogonalImage := by
  exact
    (QuotientGroup.quotientMulEquivOfEq
      spinActionOrthogonalHom_kernel_eq_spinSignSubgroup).symm.trans
      spinNativeOrthogonalQuotientRangeEquiv

theorem spinSignQuotientNativeOrthogonalImageEquiv_mk (g : Spin55) :
    spinSignQuotientNativeOrthogonalImageEquiv (QuotientGroup.mk g) =
      ⟨spinActionOrthogonalHom g, ⟨g, rfl⟩⟩ := by
  rfl

end InfoGeometry.Clifford.Clifford55
