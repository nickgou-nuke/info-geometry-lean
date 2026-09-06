import InfoGeometry.Canonical.Spin55NativeOrthogonalKernelExact

namespace InfoGeometry.Clifford.Clifford55

/-!
# Exact kernel after packaging the native action as an orthogonal-group hom

The exact `±1` kernel was proved first for the native quadratic-isometry
representation.  This file transports that result to the group-valued
`spinActionOrthogonalHom`; it introduces no new reflection or Pin argument.
-/

theorem spinActionOrthogonalHom_mem_kernel_iff_pm_one
    (g : Spin55) :
    g ∈ (spinActionOrthogonalHom).ker ↔
      g = 1 ∨ g = negOneSpin := by
  constructor
  · intro hg
    apply (spinNativeOrthogonalAction_mem_kernel_iff_pm_one g).mp
    apply MonoidHom.mem_ker.mpr
    apply DFunLike.ext
    intro v
    have h := congrArg
      (fun e : orthogonalGroup55 => (e : V55 ≃ₗ[ℝ] V55) v)
      (MonoidHom.mem_ker.mp hg)
    simpa [spinActionOrthogonalHom_apply, spinActionOrthogonal_apply] using h
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hnative : g ∈ (spinNativeOrthogonalAction).ker :=
      (spinNativeOrthogonalAction_mem_kernel_iff_pm_one g).mpr hg
    have hv := (spinNativeOrthogonalAction_mem_kernel_iff g).mp hnative v
    simpa [spinActionOrthogonalHom_apply, spinActionOrthogonal_apply] using hv

theorem spinActionOrthogonalHom_kernel_eq_spinSignSubgroup :
    (spinActionOrthogonalHom).ker = spinSignSubgroup := by
  ext g
  rw [spinActionOrthogonalHom_mem_kernel_iff_pm_one,
    mem_spinSignSubgroup_iff]

end InfoGeometry.Clifford.Clifford55
