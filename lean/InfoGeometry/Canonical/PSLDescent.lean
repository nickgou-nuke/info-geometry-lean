/-
InfoGeometry/Canonical/PSLDescent.lean

Native central-sign invariance for the modular upper-half-plane action.
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- The genuine `SL(2, ℝ)` action is insensitive to the central sign. -/
theorem sl2r_neg_smul (g : SL2R) (tau : UpperHalfPlane) :
    (-g) • tau = g • tau := by
  change ((Matrix.SpecialLinearGroup.mapGL ℝ) (-g)) • tau =
      ((Matrix.SpecialLinearGroup.mapGL ℝ) g) • tau
  have h :
      ((Matrix.SpecialLinearGroup.mapGL ℝ) (-g)) =
        -((Matrix.SpecialLinearGroup.mapGL ℝ) g) := by
    ext i j
    simp
  simp [h]

/-- The integer modular subgroup has the same central-sign invariance. -/
theorem sl2z_neg_smul (g : SL2Z) (tau : UpperHalfPlane) :
    (-g) • tau = g • tau := by
  simp

/-- Native proposition expressing central-sign invariance of the real action. -/
abbrev PSLDescentContract : Prop :=
  ∀ g : SL2R, ∀ tau : UpperHalfPlane, (-g) • tau = g • tau

namespace PSLDescentContract

/-- Historical field name, now direct application of the quantified theorem. -/
theorem sl2r_kernel_trivial_on_base
    (h : PSLDescentContract)
    (g : SL2R) (tau : UpperHalfPlane) :
    (-g) • tau = g • tau :=
  h g tau

end PSLDescentContract

/-- The native central-sign theorem supplies the descent datum. -/
theorem pslDescentContract : PSLDescentContract :=
  sl2r_neg_smul

/-- Direct readback of the owner-backed projective descent law. -/
theorem sl2r_kernel_trivial_on_base :
    ∀ g : SL2R, ∀ tau : UpperHalfPlane, (-g) • tau = g • tau :=
  pslDescentContract.sl2r_kernel_trivial_on_base

end InfoGeometry.Canonical.PSLDescent
