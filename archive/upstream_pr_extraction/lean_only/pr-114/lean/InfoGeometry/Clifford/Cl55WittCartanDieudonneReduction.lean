import InfoGeometry.Clifford.Cl55WittQuadraticReflection

namespace InfoGeometry.Clifford.Clifford55

def Q55OrthogonalComplement (x : V55) : Submodule ℝ V55 where
  carrier := {y | QuadraticMap.polar (⇑Q55) y x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz
    change QuadraticMap.polar (⇑Q55) (y + z) x = 0
    change QuadraticMap.polar (⇑Q55) y x = 0 at hy
    change QuadraticMap.polar (⇑Q55) z x = 0 at hz
    rw [QuadraticMap.polar_add_left, hy, hz, add_zero]
  smul_mem' := by
    intro a y hy
    change QuadraticMap.polar (⇑Q55) (a • y) x = 0
    change QuadraticMap.polar (⇑Q55) y x = 0 at hy
    rw [QuadraticMap.polar_smul_left, hy, smul_zero]

theorem Q55_isometry_preserves_polar
    (f : Q55.IsometryEquiv Q55) (a b : V55) :
    QuadraticMap.polar (⇑Q55) (f a) (f b) =
      QuadraticMap.polar (⇑Q55) a b := by
  change Q55 (f a + f b) - Q55 (f a) - Q55 (f b) =
    Q55 (a + b) - Q55 a - Q55 b
  rw [← map_add f a b, f.map_app (a + b), f.map_app a, f.map_app b]

theorem Q55_isometry_maps_orthogonalComplement
    (f : Q55.IsometryEquiv Q55) (x : V55)
    (hfx : f x = x) :
    ∀ y : V55, y ∈ Q55OrthogonalComplement x →
      f y ∈ Q55OrthogonalComplement x := by
  intro y hy
  change QuadraticMap.polar (⇑Q55) (f y) x = 0
  rw [← hfx, Q55_isometry_preserves_polar]
  exact hy

noncomputable def Q55_isometry_restrict_orthogonalComplement
    (f : Q55.IsometryEquiv Q55) (x : V55)
    (hfx : f x = x) :
    Q55OrthogonalComplement x ≃ₗ[ℝ] Q55OrthogonalComplement x := by
  have hsfx : f.symm x = x := by
    calc
      f.symm x = f.symm (f x) := by rw [hfx]
      _ = x := f.symm_apply_apply x
  let forward : Q55OrthogonalComplement x →ₗ[ℝ]
      Q55OrthogonalComplement x :=
    (f.toLinearMap.comp (Q55OrthogonalComplement x).subtype).codRestrict
      (Q55OrthogonalComplement x)
      (fun y => Q55_isometry_maps_orthogonalComplement f x hfx y.1 y.2)
  let backward : Q55OrthogonalComplement x →ₗ[ℝ]
      Q55OrthogonalComplement x :=
    (f.symm.toLinearMap.comp (Q55OrthogonalComplement x).subtype).codRestrict
      (Q55OrthogonalComplement x)
      (fun y => Q55_isometry_maps_orthogonalComplement f.symm x hsfx y.1 y.2)
  exact LinearEquiv.ofLinear forward backward (by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    dsimp [forward, backward]
    exact f.apply_symm_apply y.1) (by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    dsimp [forward, backward]
    exact f.symm_apply_apply y.1)

theorem Q55_isometry_restrict_orthogonalComplement_apply
    (f : Q55.IsometryEquiv Q55) (x : V55)
    (hfx : f x = x) (y : Q55OrthogonalComplement x) :
    Q55 (Q55_isometry_restrict_orthogonalComplement f x hfx y) =
      Q55 y := by
  change Q55 (f y.1) = Q55 y.1
  exact f.map_app y.1

/-!
# The local Cartan--Dieudonne reduction identity

This file proves the genuine reduction step for the split quadratic form:
if an isometry moves `x` by an anisotropic vector, the reflection in that
vector sends the image back to `x`.  The universal factorization theorem for
all `Q55`-isometries is intentionally not asserted here.
-/

theorem quadraticReflection_fixes_isometry_image
    (f : Q55.IsometryEquiv Q55) (x : V55)
    (hneq : f x ≠ x)
    (hnonzero : Q55 (f x - x) ≠ 0) :
    quadraticReflection (f x - x) hnonzero (f x) = x := by
  rw [quadraticReflection_apply]
  have hfx : Q55 (f x) = Q55 x := f.map_app x
  have hpolar :
      QuadraticMap.polar (⇑Q55) (f x) (f x - x) =
        Q55 (f x - x) := by
    rw [QuadraticMap.polar_sub_right Q55, QuadraticMap.polar_self Q55]
    symm
    rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q55),
      QuadraticMap.map_neg Q55, QuadraticMap.polar_neg_right]
    rw [hfx]
    module
  rw [hpolar, div_self hnonzero]
  module

end InfoGeometry.Clifford.Clifford55
