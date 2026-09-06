import InfoGeometry.Canonical.H3ZornS3JordanAutomorphism

/-!
# Monoid representation by bundled continuous Jordan automorphisms

The carrier and its product are inherited from the verified `H3Zorn` Jordan
instance.  Composition is oriented as sequential composition: `e * f` means
first `e`, then `f`, matching the established `S3Perm.comp` convention.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

noncomputable section

instance : One ContinuousJordanAutomorphism where
  one := {
    toContinuousLinearEquiv := ContinuousLinearEquiv.refl ℝ (H3Zorn ℝ)
    map_mul' := by intro X Y; rfl }

instance : Mul ContinuousJordanAutomorphism where
  mul := ContinuousJordanAutomorphism.trans

instance : Inv ContinuousJordanAutomorphism where
  inv e := {
    toContinuousLinearEquiv := e.toContinuousLinearEquiv.symm
    map_mul' := by
      intro X Y
      apply e.toContinuousLinearEquiv.injective
      rw [e.map_mul]
      simp }

theorem ContinuousJordanAutomorphism.one_apply
    (X : H3Zorn ℝ) : (1 : ContinuousJordanAutomorphism) X = X := by
  rfl

theorem ContinuousJordanAutomorphism.mul_apply
    (e f : ContinuousJordanAutomorphism) (X : H3Zorn ℝ) :
    (e * f) X = f (e X) :=
  rfl

instance : Group ContinuousJordanAutomorphism where
  one_mul e := by
    apply ContinuousJordanAutomorphism.ext_toContinuousLinearEquiv
    apply ContinuousLinearEquiv.ext
    funext X
    rfl
  mul_one e := by
    apply ContinuousJordanAutomorphism.ext_toContinuousLinearEquiv
    apply ContinuousLinearEquiv.ext
    funext X
    rfl
  mul_assoc e f g := by
    apply ContinuousJordanAutomorphism.ext_toContinuousLinearEquiv
    apply ContinuousLinearEquiv.ext
    funext X
    rfl
  inv e := {
    toContinuousLinearEquiv := e.toContinuousLinearEquiv.symm
    map_mul' := by
      intro X Y
      apply e.toContinuousLinearEquiv.injective
      rw [e.map_mul]
      simp }
  inv_mul_cancel e := by
    apply ContinuousJordanAutomorphism.ext_toContinuousLinearEquiv
    apply ContinuousLinearEquiv.ext
    funext X
    change e.toContinuousLinearEquiv (e.toContinuousLinearEquiv.symm X) = X
    exact e.toContinuousLinearEquiv.apply_symm_apply X
  div := fun e f => e * f⁻¹
  div_eq_mul_inv e f := rfl

def S3OnH3ZornJordanMonoidHom : S3Perm →* ContinuousJordanAutomorphism where
  toFun := S3OnH3ZornJordanAutomorphism
  map_one' := by
    apply ContinuousJordanAutomorphism.ext_toContinuousLinearEquiv
    apply ContinuousLinearEquiv.ext
    funext X
    rfl
  map_mul' σ τ := (S3OnH3ZornJordanAutomorphism_trans σ τ).symm

abbrev S3OnH3ZornJordanGroupHom :
    S3Perm →* ContinuousJordanAutomorphism :=
  S3OnH3ZornJordanMonoidHom

@[simp] theorem S3OnH3ZornJordanMonoidHom_apply
    (σ : S3Perm) :
    S3OnH3ZornJordanMonoidHom σ =
      S3OnH3ZornJordanAutomorphism σ :=
  rfl

@[simp] theorem S3OnH3ZornJordanGroupHom_inv_apply
    (σ : S3Perm) :
    S3OnH3ZornJordanGroupHom (σ⁻¹) =
      (S3OnH3ZornJordanGroupHom σ)⁻¹ := by
  exact MonoidHom.map_inv S3OnH3ZornJordanGroupHom σ

end
end InfoGeometry.Canonical
