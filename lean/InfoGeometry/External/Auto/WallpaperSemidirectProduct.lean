import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Wallpaper groups as semidirect products

This file gives kernel-checked semidirect-product group theory for wallpaper groups.
The lattice/translation factor is a genuine normal subgroup of `T ⋊[φ] P`, and the
coordinate multiplication law is the standard wallpaper composition rule: translation
part followed by the point-group action on the next translation.
-/

namespace WallpaperSemidirectProduct

variable {T P : Type*} [Group T] [Group P] (φ : P →* MulAut T)

abbrev WallpaperGroup := T ⋊[φ] P

abbrev translationSubgroup : Subgroup (WallpaperGroup φ) :=
  (SemidirectProduct.inl : T →* WallpaperGroup φ).range

/-- The point-group coordinate of a pure translation is trivial. -/
theorem pure_translation_right (t : T) :
    (SemidirectProduct.inl t : WallpaperGroup φ).right = 1 := by
  rfl

/-- Membership in the translation subgroup is exactly having trivial point part. -/
theorem mem_translationSubgroup_iff_right_eq_one (x : WallpaperGroup φ) :
    x ∈ translationSubgroup φ ↔ x.right = 1 := by
  constructor
  · intro hx
    rcases hx with ⟨t, rfl⟩
    exact pure_translation_right φ t
  · intro hx
    refine ⟨x.left, ?_⟩
    ext <;> simp [hx]

/-- Coordinate multiplication in a wallpaper semidirect product. -/
theorem wallpaper_mul_coordinates (a b : WallpaperGroup φ) :
    a * b = SemidirectProduct.mk (a.left * (φ a.right) b.left) (a.right * b.right) := by
  exact SemidirectProduct.mul_def a b

/-- The translation subgroup is closed under conjugation by the full wallpaper group. -/
theorem conjugate_translation_mem (g : WallpaperGroup φ) (t : T) :
    g * SemidirectProduct.inl t * g⁻¹ ∈ translationSubgroup φ := by
  rw [mem_translationSubgroup_iff_right_eq_one]
  change (g.right * 1 * g.right⁻¹) = 1
  group

/-- Explicit normality criterion for the lattice/translation factor. -/
theorem translationSubgroup_normal : (translationSubgroup φ).Normal := by
  constructor
  intro t ht g
  rw [mem_translationSubgroup_iff_right_eq_one] at ht ⊢
  simp [ht]

/-- A symmorphic wallpaper group has unique translation/point coordinates. -/
theorem wallpaper_ext {a b : WallpaperGroup φ}
    (hT : a.left = b.left) (hP : a.right = b.right) : a = b := by
  exact SemidirectProduct.ext hT hP

/-- Projection to the point group is a group homomorphism. -/
theorem point_projection_mul (a b : WallpaperGroup φ) :
    (a * b).right = a.right * b.right := by
  rfl

/-- The kernel of the point projection is the translation subgroup. -/
theorem point_projection_kernel_eq_translationSubgroup :
    (SemidirectProduct.rightHom : WallpaperGroup φ →* P).ker = translationSubgroup φ := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rw [mem_translationSubgroup_iff_right_eq_one]
    simpa using hx
  · intro hx
    rw [MonoidHom.mem_ker]
    exact (mem_translationSubgroup_iff_right_eq_one φ x).mp hx

end WallpaperSemidirectProduct
