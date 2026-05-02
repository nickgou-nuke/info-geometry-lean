/-
InfoGeometry/Compatibility/MathlibProjectiveDescentShadow.lean

Compatibility shadow for Mathlib's complex-backed projective descent.

This file is downstream-only. The real core does not import it.
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.NumberTheory.Modular
import InfoGeometry.Compatibility.MathlibUpperHalfPlaneShadow

noncomputable section

open scoped MatrixGroups Modular

namespace InfoGeometry.Compatibility

open UpperHalfPlane

abbrev projSL2R : Type := SL(2, ℝ)
abbrev projPSL2R : Type := PSL(2, ℝ)
abbrev projSL2Z : Type := SL(2, ℤ)
abbrev projPSL2Z : Type := PSL(2, ℤ)

/--
The `SL(2,ℝ)` action on Mathlib's complex upper half-plane is insensitive to
central sign.
-/
theorem sl2r_neg_smul (g : projSL2R) (τ : UpperHalfPlane) :
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
theorem sl2z_neg_smul (g : projSL2Z) (τ : UpperHalfPlane) :
    (-g) • τ = g • τ := by
  simp

/--
Compatibility contract for the complex-backed projective descent.
-/
structure MathlibProjectiveDescentContract : Prop where
  sl2r_kernel_trivial_on_base :
    ∀ g : projSL2R, ∀ τ : UpperHalfPlane, (-g) • τ = g • τ

/-- The descent contract is witnessed directly by Mathlib's `neg_smul` lemma. -/
theorem mathlibProjectiveDescentContract : MathlibProjectiveDescentContract :=
  ⟨sl2r_neg_smul⟩

/--
Projective quotient aliases for the Mathlib shadow layer.
-/
abbrev mathlibPSL2R := projPSL2R
abbrev mathlibPSL2Z := projPSL2Z

end InfoGeometry.Compatibility
