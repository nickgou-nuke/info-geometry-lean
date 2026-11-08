/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NullEigenspace

/-! Local fixed-pairing cancellation and its exact two-torsion boundary.
The sharpness witness is a genuine rank-one bilinear form over `ZMod 6`. -/
namespace InfoGeometry.Canonical.FixedPairingTorsionBoundary

theorem fixed_pair_double_zero {R V : Type*} [CommRing R]
    (g : V → V → R) (K : V → V)
    (ha : ∀ x y, g (K x) (K y) = -g x y)
    {x y : V} (hx : K x = x) (hy : K y = y) : 2 * g x y = 0 := by
  have h := ha x y
  rw [hx, hy] at h
  calc 2 * g x y = g x y + g x y := by ring
    _ = 0 := eq_neg_iff_add_eq_zero.mp h

theorem fixed_pair_zero {R V : Type*} [CommRing R]
    (ht : ∀ a : R, 2*a=0 → a=0) (g : V → V → R) (K : V → V)
    (ha : ∀ x y, g (K x) (K y) = -g x y)
    {x y : V} (hx : K x = x) (hy : K y = y) : g x y = 0 :=
  ht _ (fixed_pair_double_zero g K ha hx hy)

def coefficientForm {R : Type*} [CommRing R] (a : R) : R →ₗ[R] R →ₗ[R] R :=
  a • LinearMap.mul R R

@[simp] theorem coefficientForm_apply {R : Type*} [CommRing R] (a x y : R) :
    coefficientForm a x y = a * (x*y) := rfl

theorem coefficientForm_anti {R : Type*} [CommRing R] (a : R) (ha : 2*a=0) :
    ∀ x y, coefficientForm a x y = -coefficientForm a x y := by
  intro x y
  apply eq_neg_iff_add_eq_zero.mpr
  simp only [coefficientForm_apply]
  calc a*(x*y)+a*(x*y) = (2*a)*(x*y) := by ring
    _ = 0 := by rw [ha, zero_mul]

theorem two_torsion_free_iff_bilinear_fixed_pairing {R : Type*} [CommRing R] :
    (∀ a : R, 2*a=0 → a=0) ↔
    ∀ g : R →ₗ[R] R →ₗ[R] R, (∀ x y, g x y = -g x y) → g 1 1 = 0 := by
  constructor
  · intro ht g hg
    exact fixed_pair_zero ht (fun x y => g x y) id hg rfl rfl
  · intro h a ha
    simpa using h (coefficientForm a) (coefficientForm_anti a ha)

theorem zmod6_bilinear_boundary :
    (2 : ZMod 6) ≠ 0 ∧
    (∀ x y : ZMod 6, coefficientForm 3 x y = -coefficientForm 3 x y) ∧
    coefficientForm (3 : ZMod 6) 1 1 ≠ 0 := by
  refine ⟨by decide, coefficientForm_anti 3 (by decide), ?_⟩
  norm_num
  decide

end InfoGeometry.Canonical.FixedPairingTorsionBoundary
