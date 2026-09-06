import InfoGeometry.Clifford.SplitClifford55SpinOrthogonalTransportBridge
import InfoGeometry.Clifford.Cl55WittOrthogonalDeterminantSign
import InfoGeometry.Canonical.SplitClifford55SpinOrthogonalImageQuotientBridge

/-!
# Transport of the native determinant-sign boundary

The Chevalley `Spin55` carrier already transports to the native orthogonal
action.  This owner packages the unconditional determinant dichotomy on that
transported action as a homomorphism into the determinant-sign subgroup.  It
does not promote the codomain to `specialOrthogonalGroup55`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitClifford55SpinOrthogonalDeterminantSignTransportBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
open InfoGeometry.Clifford.SplitClifford55SpinActionTransportBridge
open InfoGeometry.Clifford.SplitClifford55SpinOrthogonalTransportBridge
open InfoGeometry.Canonical.SplitClifford55SpinOrthogonalImageQuotientBridge

abbrev ChevalleySpin55 :=
  InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.ChevalleySpin55

noncomputable def transportedSpinActionOrthogonalDeterminantSignHom :
    ChevalleySpin55 →* orthogonalDeterminantSignSubgroup where
  toFun g := ⟨transportedSpinActionOrthogonal g, by
    rw [transportedSpinActionOrthogonal_apply]
    exact spinActionOrthogonal_det_eq_one_or_neg_one
      (spinGroupTransportEquiv g)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one transportedSpinActionOrthogonal
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul transportedSpinActionOrthogonal g h

@[simp] theorem transportedSpinActionOrthogonalDeterminantSignHom_apply
    (g : ChevalleySpin55) :
    transportedSpinActionOrthogonalDeterminantSignHom g =
      ⟨transportedSpinActionOrthogonal g, by
        rw [transportedSpinActionOrthogonal_apply]
        exact spinActionOrthogonal_det_eq_one_or_neg_one
          (spinGroupTransportEquiv g)⟩ := by
  rfl

theorem transportedSpinOrthogonalImage_le_orthogonalDeterminantSignSubgroup :
    transportedSpinOrthogonalImage ≤ orthogonalDeterminantSignSubgroup := by
  intro g hg
  rcases hg with ⟨s, rfl⟩
  change (transportedSpinActionOrthogonal s).1.det = (1 : ℝˣ) ∨
    (transportedSpinActionOrthogonal s).1.det = (-1 : ℝˣ)
  rw [transportedSpinActionOrthogonal_apply]
  exact spinActionOrthogonal_det_eq_one_or_neg_one
    (spinGroupTransportEquiv s)

noncomputable def transportedSpinSignQuotientDeterminantSignHom :
    (ChevalleySpin55 ⧸ transportedSpinSignSubgroup) →*
      orthogonalDeterminantSignSubgroup :=
  (Subgroup.inclusion
      transportedSpinOrthogonalImage_le_orthogonalDeterminantSignSubgroup).comp
    transportedSpinSignQuotientRangeEquiv.toMonoidHom

theorem transportedSpinSignQuotientDeterminantSignHom_injective :
    Function.Injective transportedSpinSignQuotientDeterminantSignHom := by
  intro x y hxy
  change
    (Subgroup.inclusion
      transportedSpinOrthogonalImage_le_orthogonalDeterminantSignSubgroup)
        (transportedSpinSignQuotientRangeEquiv x) =
      (Subgroup.inclusion
        transportedSpinOrthogonalImage_le_orthogonalDeterminantSignSubgroup)
        (transportedSpinSignQuotientRangeEquiv y) at hxy
  apply transportedSpinSignQuotientRangeEquiv.injective
  apply Subtype.ext
  exact congrArg
    (fun z : orthogonalDeterminantSignSubgroup =>
      (z : orthogonalGroup55)) hxy

@[simp] theorem transportedSpinSignQuotientDeterminantSignHom_mk
    (s : ChevalleySpin55) :
    transportedSpinSignQuotientDeterminantSignHom (QuotientGroup.mk s) =
      ⟨transportedSpinActionOrthogonal s,
        transportedSpinOrthogonalImage_le_orthogonalDeterminantSignSubgroup
          ⟨s, rfl⟩⟩ := by
  rfl

end InfoGeometry.Canonical.SplitClifford55SpinOrthogonalDeterminantSignTransportBridge
