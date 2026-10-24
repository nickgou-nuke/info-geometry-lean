/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.BivectorPlaneIdempotents

open InfoGeometry.Clifford.BivectorProjector

example : IsIdempotentElem ((0 : ℝ) • (1 : Cl) + (0 : ℝ) • unitBivector) := by
  rw [unitBivector_plane_idempotent_iff]
  exact Or.inl ⟨rfl, rfl⟩

example : IsIdempotentElem ((1 : ℝ) • (1 : Cl) + (0 : ℝ) • unitBivector) := by
  rw [unitBivector_plane_idempotent_iff]
  exact Or.inr ⟨rfl, rfl⟩

example : ¬ IsIdempotentElem ((1 / 2 : ℝ) • (1 : Cl) -
    (1 / 2 : ℝ) • unitBivector) := by
  rw [sub_eq_add_neg, ← neg_smul, unitBivector_plane_idempotent_iff]
  norm_num

#print axioms scalar_imaginary_idempotent_iff
#print axioms unitBivector_plane_idempotent_iff
#print axioms normalized_bivector_not_idempotent
#print axioms one_add_unitBivector_not_idempotent
#print axioms g0_projector_idempotent
