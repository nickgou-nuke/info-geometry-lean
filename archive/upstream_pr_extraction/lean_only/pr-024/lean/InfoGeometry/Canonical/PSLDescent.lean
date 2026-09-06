/-
InfoGeometry/Canonical/PSLDescent.lean

Projective descent contract for the modular upper half-plane action.

This file stays at the contract level supported by Mathlib:
- the base action is the genuine `SL(2, ℝ)` action on `UpperHalfPlane`;
- the kernel element `-g` acts the same as `g`;
- the actual quotient-level `PSL(2, ℝ)` action is deferred to a later
  descent file.
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.NumberTheory.Modular
import InfoGeometry.Canonical.ProjectiveFoundation

noncomputable section

open scoped MatrixGroups Modular
open UpperHalfPlane

namespace InfoGeometry.Canonical.PSLDescent

abbrev SL2R : Type := SL(2, ℝ)
abbrev PSL2R : Type := PSL(2, ℝ)

abbrev SL2Z : Type := SL(2, ℤ)
abbrev PSL2Z : Type := PSL(2, ℤ)

/--
The `SL(2, ℝ)` action on `UpperHalfPlane` is insensitive to the central sign.

This is the exact contract-level input needed for a later quotient descent
to a genuine `PSL(2, ℝ)` action.
-/
theorem sl2r_neg_smul (g : SL2R) (τ : UpperHalfPlane) :
    (-g) • τ = g • τ := by
  change ((Matrix.SpecialLinearGroup.mapGL ℝ) (-g)) • τ =
      ((Matrix.SpecialLinearGroup.mapGL ℝ) g) • τ
  have h :
      ((Matrix.SpecialLinearGroup.mapGL ℝ) (-g)) =
        -((Matrix.SpecialLinearGroup.mapGL ℝ) g) := by
    ext i j
    simp
  simp [h]

/--
The integer modular subgroup has the same kernel-triviality on the base action.
-/
theorem sl2z_neg_smul (g : SL2Z) (τ : UpperHalfPlane) :
    (-g) • τ = g • τ := by
  simp

/--
Contract-level descent datum for the projective modular geometry.

The theorem packet deliberately stops at kernel-triviality. The actual
quotient-level `PSL(2, ℝ)` action can be added later without changing the
base geometry statements.
-/
structure PSLDescentContract : Prop where
  sl2r_kernel_trivial_on_base :
    ∀ g : SL2R, ∀ τ : UpperHalfPlane, (-g) • τ = g • τ

/-- The descent contract is witnessed directly by Mathlib's `neg_smul` lemma. -/
theorem pslDescentContract : PSLDescentContract :=
  ⟨sl2r_neg_smul⟩

end InfoGeometry.Canonical.PSLDescent
