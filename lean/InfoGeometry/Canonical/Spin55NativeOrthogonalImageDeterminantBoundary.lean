import InfoGeometry.Canonical.Spin55NativeOrthogonalImageQuotientBridge
import InfoGeometry.Canonical.Spin55NativeOrthogonalCentralKernel
import InfoGeometry.Canonical.Spin55OrthogonalActionCoherence
import InfoGeometry.Clifford.Cl55WittOrthogonalDeterminantSign

/-!
# Determinant-sign boundary of the native `Spin55` orthogonal image

The native `Spin55` action has an exact quotient-to-image description.  This
owner records the additional finite boundary that the image lies in the
already proved determinant-sign subgroup.  It deliberately does not promote
the image to the determinant-one subgroup: that requires an independent
orientation theorem, not merely the orthogonal determinant dichotomy.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

theorem spinNativeOrthogonalImage_le_orthogonalDeterminantSignSubgroup :
    spinNativeOrthogonalImage ≤ orthogonalDeterminantSignSubgroup := by
  intro g hg
  rcases hg with ⟨s, rfl⟩
  change (spinActionOrthogonalHom s).1.det = (1 : ℝˣ) ∨
    (spinActionOrthogonalHom s).1.det = (-1 : ℝˣ)
  rw [spinActionOrthogonalHom_apply]
  exact spinActionOrthogonal_det_eq_one_or_neg_one s

theorem orthogonalDeterminantSignSubgroup_eq_top :
    orthogonalDeterminantSignSubgroup = (⊤ : Subgroup orthogonalGroup55) := by
  apply le_antisymm
  · exact le_top
  · intro g hg
    exact orthogonalGroup55_det_eq_one_or_neg_one g

theorem spinNativeOrthogonalImage_det_eq_one_or_neg_one
      (g : spinNativeOrthogonalImage) :
      (g : orthogonalGroup55).1.det = (1 : ℝˣ) ∨
        (g : orthogonalGroup55).1.det = (-1 : ℝˣ) := by
  rcases g.2 with ⟨s, hs⟩
  rw [← hs]
  change (spinActionOrthogonalHom s).1.det = (1 : ℝˣ) ∨
    (spinActionOrthogonalHom s).1.det = (-1 : ℝˣ)
  rw [spinActionOrthogonalHom_apply]
  exact spinActionOrthogonal_det_eq_one_or_neg_one s

/-- The quotient-to-image map followed by subgroup inclusion.

This is a genuine homomorphism into the determinant-sign subgroup.  Its
codomain is intentionally not `specialOrthogonalGroup55`: the unconditional
native determinant theorem supplies only the `±1` boundary. -/
noncomputable def spinNativeOrthogonalQuotientDeterminantSignHom :
    (Spin55 ⧸ (spinActionOrthogonalHom).ker) →*
      orthogonalDeterminantSignSubgroup :=
  (Subgroup.inclusion
      spinNativeOrthogonalImage_le_orthogonalDeterminantSignSubgroup).comp
    spinNativeOrthogonalQuotientRangeEquiv.toMonoidHom

theorem spinNativeOrthogonalQuotientDeterminantSignHom_injective :
    Function.Injective spinNativeOrthogonalQuotientDeterminantSignHom := by
  intro x y hxy
  change
    (Subgroup.inclusion
      spinNativeOrthogonalImage_le_orthogonalDeterminantSignSubgroup)
        (spinNativeOrthogonalQuotientRangeEquiv x) =
      (Subgroup.inclusion
        spinNativeOrthogonalImage_le_orthogonalDeterminantSignSubgroup)
        (spinNativeOrthogonalQuotientRangeEquiv y) at hxy
  apply spinNativeOrthogonalQuotientRangeEquiv.injective
  apply Subtype.ext
  exact congrArg
    (fun z : orthogonalDeterminantSignSubgroup =>
      (z : orthogonalGroup55)) hxy

@[simp] theorem spinNativeOrthogonalQuotientDeterminantSignHom_mk
    (s : Spin55) :
    spinNativeOrthogonalQuotientDeterminantSignHom (QuotientGroup.mk s) =
      ⟨spinActionOrthogonalHom s,
        spinNativeOrthogonalImage_le_orthogonalDeterminantSignSubgroup
          ⟨s, rfl⟩⟩ := by
  rfl

theorem spinNativeOrthogonalQuotientDeterminantSignHom_isometry_readback
    (s : Spin55) :
    orthogonalGroup55IsometryEquiv
        (spinNativeOrthogonalQuotientDeterminantSignHom
          (QuotientGroup.mk s)).1 =
      spinNativeOrthogonalAction s := by
  rw [spinNativeOrthogonalQuotientDeterminantSignHom_mk]
  exact spinActionOrthogonalHom_native_readback s

/-- The same determinant-sign readout from the already identified sign quotient.

The quotient is the native quotient by the proved scalar-sign subgroup; this
still lands only in the actual orthogonal image boundary, not in an asserted
full `SO(5,5)` quotient. -/
noncomputable def spinSignQuotientDeterminantSignHom :
    (Spin55 ⧸ (spinSignSubgroup : Subgroup Spin55)) →*
      orthogonalDeterminantSignSubgroup :=
  (Subgroup.inclusion
      spinNativeOrthogonalImage_le_orthogonalDeterminantSignSubgroup).comp
    spinSignQuotientNativeOrthogonalImageEquiv.toMonoidHom

theorem spinSignQuotientDeterminantSignHom_injective :
    Function.Injective spinSignQuotientDeterminantSignHom := by
  intro x y hxy
  change
    (Subgroup.inclusion
      spinNativeOrthogonalImage_le_orthogonalDeterminantSignSubgroup)
        (spinSignQuotientNativeOrthogonalImageEquiv x) =
      (Subgroup.inclusion
        spinNativeOrthogonalImage_le_orthogonalDeterminantSignSubgroup)
        (spinSignQuotientNativeOrthogonalImageEquiv y) at hxy
  apply spinSignQuotientNativeOrthogonalImageEquiv.injective
  apply Subtype.ext
  exact congrArg
    (fun z : orthogonalDeterminantSignSubgroup =>
      (z : orthogonalGroup55)) hxy

@[simp] theorem spinSignQuotientDeterminantSignHom_mk
    (s : Spin55) :
    spinSignQuotientDeterminantSignHom (QuotientGroup.mk s) =
      ⟨spinActionOrthogonalHom s,
        spinNativeOrthogonalImage_le_orthogonalDeterminantSignSubgroup
          ⟨s, rfl⟩⟩ := by
  rfl

theorem spinSignQuotientDeterminantSignHom_isometry_readback
    (s : Spin55) :
    orthogonalGroup55IsometryEquiv
        (spinSignQuotientDeterminantSignHom
          (QuotientGroup.mk s)).1 =
      spinSignQuotientAction
        (QuotientGroup.mk' spinSignSubgroup s) := by
  rw [spinSignQuotientDeterminantSignHom_mk,
    spinSignQuotientAction_mk]
  exact spinActionOrthogonalHom_native_readback s

end InfoGeometry.Clifford.Clifford55
