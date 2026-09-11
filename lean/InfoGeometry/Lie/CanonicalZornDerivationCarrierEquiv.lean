import InfoGeometry.Lie.CanonicalZornMathlibRootSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationCarrierEquiv

abbrev Native := CanonicalZornDerivation.canonicalZornDerivations
abbrev Mathlib := CanonicalZornMathlibRootSpace.Der

noncomputable def nativeToMathlib : Native ≃ₗ⁅ℝ⁆ Mathlib := by
  let f : Native →ₗ⁅ℝ⁆ Mathlib :=
    { toFun := fun D => ⟨D.1, D.2⟩
      map_add' := by intro D E; rfl
      map_smul' := by intro r D; rfl
      map_lie' := by intro D E; rfl }
  apply LieEquiv.ofBijective f
  constructor
  · intro D E h
    exact Subtype.ext (congrArg Subtype.val h)
  · intro D
    exact ⟨⟨D.1, D.2⟩, rfl⟩

@[simp] theorem nativeToMathlib_apply (D : Native) :
    nativeToMathlib D = ⟨D.1, D.2⟩ := by rfl

theorem nativeToMathlib_symm_rootDerivation
    (rootDerivation : Mathlib) :
    nativeToMathlib.symm rootDerivation = rootDerivation := by
  apply nativeToMathlib.injective
  simp

end InfoGeometry.Lie.CanonicalZornDerivationCarrierEquiv
