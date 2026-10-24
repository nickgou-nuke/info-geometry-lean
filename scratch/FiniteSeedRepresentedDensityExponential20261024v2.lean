/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteSeedRepresentedRealTime
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-! Actual finite-seed density as a Banach-algebra exponential.
Sandbox v2 candidate, uncompiled. The finite matrix CFC is mapped to an existing
C⋆ target before using its normed exponential. No raw matrix normed-ring
instance, complex-time flow, or strip KMS theorem is introduced.
-/
noncomputable section
open scoped ComplexOrder

namespace InfoGeometry.Canonical.FiniteSeedRepresentedDensityExponential

open FiniteMatrixGibbsFunctional

/-- Transport the actual finite CFC Gibbs density through a star algebra map. -/
theorem map_gibbsDensity_eq_exp
    {A : Type*} [CStarAlgebra A]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ →⋆ₐ[ℂ] A)
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    f (gibbsDensity H hH β) = NormedSpace.exp ((-β) • f H) := by
  let : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
    Matrix.IsHermitian.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℂ A IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hfH : IsSelfAdjoint (f H) := by
    change star (f H) = f H
    rw [← map_star]
    exact congrArg f hH
  have hscaled : IsSelfAdjoint ((-β) • f H) := by
    change star ((-β) • f H) = (-β) • f H
    simp only [star_smul, star_trivial, hfH.star_eq]
  let fR : Matrix n n ℂ →⋆ₐ[ℝ] A := f.restrictScalars ℝ
  have hcont : Continuous fR :=
    f.toAlgHom.toLinearMap.continuous_of_finiteDimensional
  have hmap : fR (cfc (R := ℝ) (expWeight β) H) =
      cfc (R := ℝ) (expWeight β) (fR H) :=
    StarAlgHom.map_cfc (R := ℝ) (S := ℝ) fR (expWeight β) H
      (by unfold expWeight; fun_prop) hcont hH hfH
  calc
    f (gibbsDensity H hH β) = fR (cfc (R := ℝ) (expWeight β) H) := by
      exact congrArg f (hH.cfc_eq (expWeight β)).symm
    _ = cfc (R := ℝ) (expWeight β) (fR H) := hmap
    _ = cfc (R := ℝ) Real.exp ((-β) • f H) := by
      exact cfc_comp_const_mul (-β) Real.exp (f H) (by fun_prop) hfH
    _ = NormedSpace.exp ((-β) • f H) :=
      CFC.real_exp_eq_normedSpace_exp hscaled

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

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSMatrixRealTime
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CantorBernoulliCStarMatrixTraceState CuntzMatrixTowerInstantiation
open AlgebraicKMSStateColimit FiniteSeedRepresentedRealTime

private abbrev stageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun _ => inferInstance
private abbrev stageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun _ => inferInstance
private abbrev stageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun _ => inferInstance
attribute [local instance] stageCStarFamily stageOrderFamily stageStarOrderFamily

/-- The existing represented density, for every real inverse temperature. -/
theorem representedDensityUnit_coe_eq_exp {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    (representedDensityUnit H hH β :
      representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β)) =
      NormedSpace.exp ((-β) • (seedStageHom H hH β H)) := by
  change (seedStageHom H hH β) (↑(gibbsDensityUnit H hH β)) = _
  rw [gibbsDensityUnit_coe]
  exact map_gibbsDensity_eq_exp (seedStageHom H hH β) H hH β

/-- Opposite exponential for the inverse of that same actual represented unit. -/
theorem representedDensityUnit_inv_coe_eq_exp {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    (((representedDensityUnit H hH β)⁻¹) :
      representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β)) =
      NormedSpace.exp (β • (seedStageHom H hH β H)) := by
  exact map_gibbsDensityUnit_inv_eq_exp (seedStageHom H hH β) H hH β

end InfoGeometry.Canonical.FiniteSeedRepresentedDensityExponential
