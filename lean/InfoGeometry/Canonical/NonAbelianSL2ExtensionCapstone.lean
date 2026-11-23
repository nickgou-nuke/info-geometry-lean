/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Gauge.NonAbelianSL2Extension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.NCG.DerivationDifferential

namespace InfoGeometry.Canonical.NonAbelianSL2ExtensionCapstone

open InfoGeometry.Gauge.NonAbelianSL2Extension
open InfoGeometry.NCG.DerivationDifferential

theorem capstone_sl2_algebra_synthesis :
    (genJ * genJ = - 1) ∧ (genK * genK = 1) ∧
    (genK * genE - genE * genK = (2 : ℝ) • genE) ∧
    (genK * genF - genF * genK = -((2 : ℝ) • genF)) ∧
    (genE * genF - genF * genE = genK) := by
  exact ⟨genJ_sq_eq_neg_one, genK_sq_eq_one, comm_K_E, comm_K_F, comm_E_F⟩

/-- The compact real form has the cyclic three-generator commutator table,
with a fixed orientation and normalization. -/
theorem compact_su2_lie_bracket_table :
    (su2X * su2Y - su2Y * su2X = -((2 : ℂ) • su2Z)) ∧
    (su2Y * su2Z - su2Z * su2Y = -((2 : ℂ) • su2X)) ∧
    (su2Z * su2X - su2X * su2Z = -((2 : ℂ) • su2Y)) :=
  ⟨su2X_su2Y_commutator, su2Y_su2Z_commutator, su2Z_su2X_commutator⟩

private abbrev SU2Operator := Matrix (Fin 2) (Fin 2) ℂ

/-- The Chevalley--Eilenberg curvature of the identity one-form on the
associative inner-derivation Lie system evaluates to twice the ordered matrix
commutator. This connects the compact `su(2)` matrix directions to the
repository's operator-valued degree-two curvature construction. -/
theorem su2_identity_form_curvature :
    curvature (innerSystem (A := SU2Operator)) (fun X : SU2Operator => X)
        su2X su2Y =
      (2 : ℤ) • (su2X * su2Y - su2Y * su2X) := by
  simpa [InfoGeometry.NCG.bracket] using
    (innerSystem_identityForm_curvature (A := SU2Operator) su2X su2Y)

/-- The resulting curvature is nonzero for these two compact Lie algebra
directions. -/
theorem su2_identity_form_curvature_ne_zero :
    curvature (innerSystem (A := SU2Operator)) (fun X : SU2Operator => X)
        su2X su2Y ≠ 0 := by
  rw [su2_identity_form_curvature, su2X_su2Y_commutator]
  intro h
  have h00 := congrArg (fun M : SU2Operator => M 0 0) h
  change (2 : ℤ) • -((2 : ℂ) • Complex.I) = 0 at h00
  norm_num at h00

end InfoGeometry.Canonical.NonAbelianSL2ExtensionCapstone
