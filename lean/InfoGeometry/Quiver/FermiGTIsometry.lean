/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Formalization Team
-/
import Mathlib.Tactic

/-!
# Finite unipotent isometries

An exact algebraic isometry theorem for the shear `1 + tD`.  The skewness
condition cancels the two linear cross terms, while isotropy of the image of
`D` removes the quadratic term.  No metric-preservation conclusion is stored
as a field or assumed as a premise.
-/

namespace InfoGeometry.FermiGT

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The finite unipotent action associated to a linear operator `D`. -/
def unipotentShear (D : V →ₗ[ℝ] V) (t : ℝ) : V →ₗ[ℝ] V :=
  LinearMap.id + t • D

/--
If `D` is skew for a bilinear form and its image is isotropic, then the finite
shear `1 + tD` preserves that form for every real parameter `t`.

The result is a finite algebraic identity.  It does not assert positivity,
nondegeneracy, a Lie-group integration theorem, or a physical Fermi/GT model.
-/
theorem unipotentShear_preserves_bilinearForm
    (form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (D : V →ₗ[ℝ] V) (t : ℝ)
    (h_skew : ∀ x y, form (D x) y + form x (D y) = 0)
    (h_image_isotropic : ∀ x y, form (D x) (D y) = 0) (x y : V) :
    form (unipotentShear D t x) (unipotentShear D t y) = form x y := by
  have h_expand :
      form (unipotentShear D t x) (unipotentShear D t y) =
        form x y + t * form x (D y) + t * form (D x) y +
          t * t * form (D x) (D y) := by
    simp [unipotentShear, LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_smul, smul_eq_mul, mul_add]
    ring
  rw [h_expand, h_image_isotropic x y]
  simp only [mul_zero]
  linear_combination t * h_skew x y

end InfoGeometry.FermiGT
