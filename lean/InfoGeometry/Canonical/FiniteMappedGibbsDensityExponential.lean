/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteSeedRepresentedRealTime
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-! Finite Gibbs density transport as a Banach-algebra exponential.
The finite matrix CFC is mapped to an existing
C⋆ target before using its normed exponential. No raw matrix normed-ring
instance, complex-time flow, or strip KMS theorem is introduced.
-/
noncomputable section
open scoped ComplexOrder

namespace InfoGeometry.Canonical.FiniteSeedRepresentedDensityExponential

open FiniteMatrixGibbsFunctional

section DensityCFC

variable {A : Type*} [CStarAlgebra A]

-- Fix the native target CFC choices before elaborating the helper statements.
local instance targetComplexCFC : ContinuousFunctionalCalculus ℂ A IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
local instance targetRealCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Map the actual finite Gibbs density to the real CFC on its represented image. -/
theorem map_gibbsDensity_eq_cfc
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ →⋆ₐ[ℂ] A)
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    f (gibbsDensity H hH β) = cfc (R := ℝ) (expWeight β) (f H) := by
  let : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
    Matrix.IsHermitian.instContinuousFunctionalCalculus
  have hfH : IsSelfAdjoint (f H) := by
    change star (f H) = f H
    rw [← map_star]
    exact congrArg f hH
  let fR : Matrix n n ℂ →⋆ₐ[ℝ] A := f.restrictScalars ℝ
  have hcont : Continuous fR :=
    f.toAlgHom.toLinearMap.continuous_of_finiteDimensional
  calc
    f (gibbsDensity H hH β) = fR (cfc (R := ℝ) (expWeight β) H) :=
      congrArg f (hH.cfc_eq (expWeight β)).symm
    _ = cfc (R := ℝ) (expWeight β) (fR H) :=
      StarAlgHom.map_cfc (R := ℝ) (S := ℝ) fR (expWeight β) H
        (by unfold expWeight; fun_prop) hcont hH hfH

/-- Evaluate the Gibbs scalar weight on any self-adjoint element of the target. -/
theorem cfc_expWeight_eq_exp (G : A) (hG : IsSelfAdjoint G) (β : ℝ) :
    cfc (R := ℝ) (expWeight β) G = NormedSpace.exp ((-β) • G) := by
  have hscaled : IsSelfAdjoint ((-β) • G) := by
    change star ((-β) • G) = (-β) • G
    simp only [star_smul, star_trivial, hG.star_eq]
  calc
    cfc (R := ℝ) (expWeight β) G = cfc (R := ℝ) Real.exp ((-β) • G) :=
      cfc_comp_const_mul (-β) Real.exp G (by fun_prop) hG
    _ = NormedSpace.exp ((-β) • G) := CFC.real_exp_eq_normedSpace_exp hscaled

/-- Transport and evaluate the actual finite density inside a genuine C⋆ target. -/
theorem map_gibbsDensity_eq_exp
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ →⋆ₐ[ℂ] A)
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    f (gibbsDensity H hH β) = NormedSpace.exp ((-β) • f H) := by
  have hfH : IsSelfAdjoint (f H) := by
    change star (f H) = f H
    rw [← map_star]
    exact congrArg f hH
  exact (map_gibbsDensity_eq_cfc f H hH β).trans (cfc_expWeight_eq_exp (f H) hfH β)

end DensityCFC

/-- The inverse of the mapped native density unit is the opposite exponential.
Its value is forced by unit inverse uniqueness, not supplied as extra data. -/
theorem map_gibbsDensityUnit_inv_eq_exp
    {A : Type*} [CStarAlgebra A]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ →⋆ₐ[ℂ] A)
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (((Units.map f.toMonoidHom (gibbsDensityUnit H hH β))⁻¹ : Aˣ) : A) =
      NormedSpace.exp (β • f H) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  apply Units.inv_eq_of_mul_eq_one_right
  change f (↑(gibbsDensityUnit H hH β)) * NormedSpace.exp (β • f H) = 1
  rw [gibbsDensityUnit_coe, map_gibbsDensity_eq_exp f H hH β]
  have hc : Commute ((-β) • f H) (β • f H) :=
    ((Commute.refl (f H)).smul_left (-β)).smul_right β
  rw [← NormedSpace.exp_add_of_commute hc]
  simp only [neg_smul, neg_add_cancel, NormedSpace.exp_zero]

end InfoGeometry.Canonical.FiniteSeedRepresentedDensityExponential
