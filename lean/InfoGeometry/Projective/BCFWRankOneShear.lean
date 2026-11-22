/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Rank-one BCFW shears

This file formalizes the algebraic core of a BCFW shift. It does not define a
scattering amplitude, a complex contour integral, or an amplituhedron form.
Given a vector `Z` and covector `W`, the rank-one operator is
`N(x) = W(x) • Z`. The hypothesis `W(Z) = 0` makes `N` square-zero, so
`x ↦ x + z • N(x)` is an invertible shear with inverse parameter `-z`.
-/

namespace InfoGeometry.Projective.BCFWRankOneShear

universe u
variable {R : Type u} [CommRing R]
variable {V : Type u} [AddCommGroup V] [Module R V]

/-- The genuine rank-one operator `x ↦ W(x) • Z`. -/
def rankOne (Z : V) (W : V →ₗ[R] R) : V →ₗ[R] V where
  toFun x := W x • Z
  map_add' x y := by simp [map_add, add_smul]
  map_smul' a x := by simp [map_smul, mul_smul]

@[simp] theorem rankOne_apply (Z : V) (W : V →ₗ[R] R) (x : V) :
    rankOne Z W x = W x • Z := rfl

/-- A rank-one operator is square-zero under the orthogonality condition
`W(Z) = 0`. -/
theorem rankOne_comp_rankOne_eq_zero (Z : V) (W : V →ₗ[R] R)
    (hWZ : W Z = 0) : (rankOne Z W).comp (rankOne Z W) = 0 := by
  ext x
  simp [rankOne, map_smul, hWZ]

/-- The finite unipotent shear associated to a rank-one operator. -/
def shear (z : R) (N : V →ₗ[R] V) : V →ₗ[R] V :=
  LinearMap.id + z • N

theorem shear_inverse (Z : V) (W : V →ₗ[R] R) (z : R)
    (hWZ : W Z = 0) :
    (shear z (rankOne Z W)).comp (shear (-z) (rankOne Z W)) = LinearMap.id ∧
    (shear (-z) (rankOne Z W)).comp (shear z (rankOne Z W)) = LinearMap.id := by
  constructor <;> ext x <;>
    simp [shear, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, rankOne, map_smul, hWZ,
      smul_smul, mul_comm, mul_left_comm]

/-- Applying the shear with `N(x) = W(x) • Z` produces the BCFW shift
`X ↦ X + z Z` when `W(X) = 1`. -/
theorem shear_gives_bcfw_shift (Z X : V) (W : V →ₗ[R] R) (z : R)
    (hWX : W X = 1) : shear z (rankOne Z W) X = X + z • Z := by
  simp [shear, rankOne, hWX]

/-- The covector of a shifted vector stays fixed when the shift direction is
annihilated by that covector. -/
theorem bcfw_shift_direction_fixed (Z X : V) (W : V →ₗ[R] R) (z : R)
    (hWZ : W Z = 0) : W (shear z (rankOne Z W) X) = W X := by
  simp [shear, rankOne, map_add, map_smul, hWZ, mul_comm]

end InfoGeometry.Projective.BCFWRankOneShear
