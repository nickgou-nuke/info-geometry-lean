/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Assumptions.Determinant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.LogSum

/-!
# Axioms

Compatibility facade over `InfoGeometry.Assumptions`.
-/

namespace InfoGeometry.Axioms

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem axioms_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

export InfoGeometry.Projective (
  logSum_inequality
)

export InfoGeometry.Assumptions.Determinant (
  gl_mul_inv
  gl_inv_mul
  detHom
  ker_det_eq_SL
  logAbsDet
  jacDet
  jacDet_comp
  jacobian_functoriality
)

universe u v

abbrev «GL» (R : Type u) (V : Type v) [Ring R] [Fintype V] [DecidableEq V] :=
  InfoGeometry.Assumptions.Determinant.GL R V

noncomputable abbrev «SL» (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :=
  InfoGeometry.Assumptions.Determinant.SL R V

end InfoGeometry.Axioms
