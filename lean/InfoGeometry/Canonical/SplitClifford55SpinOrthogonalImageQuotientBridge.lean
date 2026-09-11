import InfoGeometry.Clifford.SplitClifford55SpinOrthogonalTransportBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitClifford55SpinOrthogonalKernelTransportBridge
import InfoGeometry.Canonical.Spin55NativeOrthogonalImageQuotientBridge

/-!
# Transported `Spin(5,5)` orthogonal image and quotient

This owner packages the exact kernel of the transported Chevalley Spin action
as the quotient-by-kernel isomorphism onto its actual orthogonal image.  The
target is deliberately the range of the action: no surjectivity onto the full
orthogonal group is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitClifford55SpinOrthogonalImageQuotientBridge

open InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
open InfoGeometry.Clifford.SplitClifford55SpinOrthogonalTransportBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.SplitClifford55SpinOrthogonalKernelTransportBridge

abbrev ChevalleySpin55 :=
  InfoGeometry.Clifford.SplitClifford55NeutralFormBridge.ChevalleySpin55

noncomputable def transportedSpinOrthogonalImage :=
  (transportedSpinActionOrthogonal).range

/-! ## Transport coherence of the actual orthogonal images -/

noncomputable def transportedSpinOrthogonalImageEquivNative :
    transportedSpinOrthogonalImage ≃*
      spinNativeOrthogonalImage := by
  let f : transportedSpinOrthogonalImage →*
      spinNativeOrthogonalImage := {
    toFun := fun x => ⟨x.1, by
      rcases x.2 with ⟨g, hg⟩
      refine ⟨spinGroupTransportEquiv g, ?_⟩
      rw [spinActionOrthogonalHom_apply]
      rw [← transportedSpinActionOrthogonal_apply g]
      exact hg⟩
    map_one' := by
      apply Subtype.ext
      rfl
    map_mul' := by
      intro x y
      apply Subtype.ext
      rfl }
  refine MulEquiv.ofBijective f ?_
  constructor
  · intro x y hxy
    have hxy' : (f x).1 = (f y).1 :=
      congrArg (fun z : spinNativeOrthogonalImage => z.1) hxy
    change x.1 = y.1 at hxy'
    exact Subtype.ext hxy'
  · intro y
    rcases y.2 with ⟨g, hg⟩
    let x : transportedSpinOrthogonalImage :=
      ⟨transportedSpinActionOrthogonal (spinGroupTransportEquiv.symm g), by
        exact ⟨spinGroupTransportEquiv.symm g, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change transportedSpinActionOrthogonal (spinGroupTransportEquiv.symm g) = y.1
    rw [transportedSpinActionOrthogonal_apply]
    rw [spinGroupTransportEquiv.apply_symm_apply]
    rw [← spinActionOrthogonalHom_apply g]
    simpa using hg

theorem transportedSpinOrthogonalImageEquivNative_apply
    (x : transportedSpinOrthogonalImage) :
    transportedSpinOrthogonalImageEquivNative x =
      ⟨x.1, by
        rcases x.2 with ⟨g, hg⟩
        refine ⟨spinGroupTransportEquiv g, ?_⟩
        rw [spinActionOrthogonalHom_apply]
        rw [← transportedSpinActionOrthogonal_apply g]
        exact hg⟩ := by
  rfl

@[simp] theorem transportedSpinOrthogonalImageEquivNative_val
    (x : transportedSpinOrthogonalImage) :
    (transportedSpinOrthogonalImageEquivNative x).1 = x.1 := by
  rfl

theorem transportedSpinOrthogonalImage_eq_native :
    transportedSpinOrthogonalImage = spinNativeOrthogonalImage := by
  ext A
  constructor
  · intro hA
    rcases hA with ⟨g, rfl⟩
    refine ⟨spinGroupTransportEquiv g, ?_⟩
    simp [transportedSpinActionOrthogonal_apply,
      spinActionOrthogonalHom_apply]
  · intro hA
    rcases hA with ⟨g, rfl⟩
    refine ⟨spinGroupTransportEquiv.symm g, ?_⟩
    simp [transportedSpinActionOrthogonal_apply,
      spinActionOrthogonalHom_apply]

noncomputable def transportedSpinOrthogonalQuotientRangeEquiv :
    (ChevalleySpin55 ⧸ (transportedSpinActionOrthogonal).ker) ≃*
      transportedSpinOrthogonalImage :=
  QuotientGroup.quotientKerEquivRange transportedSpinActionOrthogonal

theorem transportedSpinOrthogonalQuotientRangeEquiv_mk
    (g : ChevalleySpin55) :
    transportedSpinOrthogonalQuotientRangeEquiv
      (QuotientGroup.mk (s := (transportedSpinActionOrthogonal).ker) g) =
      ⟨transportedSpinActionOrthogonal g, ⟨g, rfl⟩⟩ := by
  rfl

noncomputable def transportedSpinSignSubgroup : Subgroup ChevalleySpin55 :=
  (spinSignSubgroup : Subgroup Spin55).comap
    spinGroupTransportEquiv.toMonoidHom

instance transportedSpinSignSubgroup_normal :
    transportedSpinSignSubgroup.Normal := by
  dsimp [transportedSpinSignSubgroup]
  infer_instance

theorem transportedSpinActionOrthogonal_kernel_eq_signSubgroup :
    (transportedSpinActionOrthogonal).ker =
      transportedSpinSignSubgroup := by
  ext g
  rw [transportedSpinActionOrthogonal_mem_kernel_iff_pm_one]
  change spinGroupTransportEquiv g = 1 ∨
    spinGroupTransportEquiv g = negOneSpin ↔
      spinGroupTransportEquiv g ∈ (spinSignSubgroup : Subgroup Spin55)
  exact (mem_spinSignSubgroup_iff _).symm

noncomputable def transportedSpinSignQuotientRangeEquiv :
    (ChevalleySpin55 ⧸ transportedSpinSignSubgroup) ≃*
      transportedSpinOrthogonalImage := by
  exact
    (QuotientGroup.quotientMulEquivOfEq
      transportedSpinActionOrthogonal_kernel_eq_signSubgroup).symm.trans
      transportedSpinOrthogonalQuotientRangeEquiv

theorem transportedSpinSignQuotientRangeEquiv_mk
    (g : ChevalleySpin55) :
    transportedSpinSignQuotientRangeEquiv (QuotientGroup.mk (s := transportedSpinSignSubgroup) g) =
      ⟨transportedSpinActionOrthogonal g, ⟨g, rfl⟩⟩ := by
  rfl

theorem transportedSpinSignQuotientRangeEquiv_native_coherence_mk
    (g : ChevalleySpin55) :
    transportedSpinOrthogonalImageEquivNative
        (transportedSpinSignQuotientRangeEquiv
          (QuotientGroup.mk (s := transportedSpinSignSubgroup) g)) =
      spinSignQuotientNativeOrthogonalImageEquiv
        (QuotientGroup.mk (s := (spinSignSubgroup : Subgroup Spin55))
          (spinGroupTransportEquiv g)) := by
  rw [transportedSpinSignQuotientRangeEquiv_mk]
  simp [transportedSpinOrthogonalImageEquivNative_apply,
    spinActionOrthogonalHom_apply,
    InfoGeometry.Clifford.Clifford55.spinSignQuotientNativeOrthogonalImageEquiv_mk]

noncomputable abbrev transportedSpinSignQuotientTransport :
    (ChevalleySpin55 ⧸ transportedSpinSignSubgroup) ≃*
      (Spin55 ⧸ (spinSignSubgroup : Subgroup Spin55)) :=
  (transportedSpinSignQuotientRangeEquiv.trans
    transportedSpinOrthogonalImageEquivNative).trans
  spinSignQuotientNativeOrthogonalImageEquiv.symm

noncomputable abbrev transportedSpinSignQuotientEquiv :
    (ChevalleySpin55 ⧸ transportedSpinSignSubgroup) →*
      (Spin55 ⧸ (spinSignSubgroup : Subgroup Spin55)) :=
  transportedSpinSignQuotientTransport.toMonoidHom

noncomputable abbrev spinSignQuotientToTransportedSignQuotient :
    (Spin55 ⧸ (spinSignSubgroup : Subgroup Spin55)) →*
      (ChevalleySpin55 ⧸ transportedSpinSignSubgroup) :=
  transportedSpinSignQuotientTransport.symm.toMonoidHom

@[simp] theorem transportedSpinSignQuotientTransport_mk
    (g : ChevalleySpin55) :
    transportedSpinSignQuotientTransport
        (QuotientGroup.mk (s := transportedSpinSignSubgroup) g) =
      QuotientGroup.mk (s := (spinSignSubgroup : Subgroup Spin55))
        (spinGroupTransportEquiv g) := by
  apply spinSignQuotientNativeOrthogonalImageEquiv.injective
  change
    spinSignQuotientNativeOrthogonalImageEquiv
      (transportedSpinSignQuotientTransport
        (QuotientGroup.mk (s := transportedSpinSignSubgroup) g))
      =
      spinSignQuotientNativeOrthogonalImageEquiv
        (QuotientGroup.mk (s := (spinSignSubgroup : Subgroup Spin55))
          (spinGroupTransportEquiv g))
  simpa [transportedSpinSignQuotientTransport,
    transportedSpinSignQuotientRangeEquiv_native_coherence_mk]

theorem transportedSpinSignQuotientTransport_toMonoidHom_eq :
    transportedSpinSignQuotientTransport.toMonoidHom =
      transportedSpinSignQuotientEquiv := by
  ext q
  change transportedSpinSignQuotientTransport (QuotientGroup.mk q) =
    transportedSpinSignQuotientEquiv (QuotientGroup.mk q)
  rfl

theorem transportedSpinSignQuotientRangeEquiv_native_coherence
    (q : ChevalleySpin55 ⧸ transportedSpinSignSubgroup) :
    transportedSpinOrthogonalImageEquivNative
        (transportedSpinSignQuotientRangeEquiv q) =
      spinSignQuotientNativeOrthogonalImageEquiv
        (transportedSpinSignQuotientTransport q) := by
  refine QuotientGroup.induction_on q ?_
  intro g
  simpa [transportedSpinSignQuotientTransport_mk,
    transportedSpinSignQuotientRangeEquiv_mk]
    using (transportedSpinSignQuotientRangeEquiv_native_coherence_mk g)

/-- Full coherence of quotient→image transport as a `MulEquiv`. -/
theorem transportedSpinSignQuotientRangeEquiv_native_coherence_mulEquiv :
    (transportedSpinSignQuotientRangeEquiv.trans
      transportedSpinOrthogonalImageEquivNative)
  = (transportedSpinSignQuotientTransport.trans
        spinSignQuotientNativeOrthogonalImageEquiv) := by
  apply MulEquiv.ext
  intro q
  exact transportedSpinSignQuotientRangeEquiv_native_coherence q

end InfoGeometry.Canonical.SplitClifford55SpinOrthogonalImageQuotientBridge
