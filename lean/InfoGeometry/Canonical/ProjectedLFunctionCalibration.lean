import Mathlib
import InfoGeometry.Meta.CalibrationReexport
import InfoGeometry.Automorphic.ProjectedLFunction

/-!
# InfoGeometry.Canonical.ProjectedLFunctionCalibration

Canonical wrapper for the existing projected automorphic L-function surface.

This file adds no new analytic content. It re-exports the already-native
projection and resonance theorems under a canonical owner-facing namespace.
-/

noncomputable section

namespace InfoGeometry.Canonical.ProjectedLFunctionCalibration

open InfoGeometry.Automorphic.SiegelResonance

/-- Canonical re-export of the raw-to-cuspidal projection theorem. -/
theorem cuspidalLFunction_eq_raw_of_siegel_zero
    {Bulk : Type*} {Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (Λ : AutomorphicLFunctional Bulk)
    (F : Bulk)
    (hF : W.siegel F = 0) :
    cuspidalLFunction W Λ F = rawLFunction Λ F :=
  by reexport W.cuspidalLFunction_eq_raw_of_siegel_zero Λ F hF

/-- Canonical re-export of the projected-L evaluation theorem. -/
theorem projectedL_eval_eq_projected
    {Bulk : Type*} {Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (P : ProjectedAutomorphicLFunctionWitness W)
    (s : ℂ) :
    P.L s =
      P.functional.coeff s (W.cuspidalProjector P.bulkState) :=
  by reexport P.eval_eq_projected s

/-- Canonical re-export of the projected-L resonance/zero theorem. -/
theorem projectedL_resonance_iff_zero
    {Bulk : Type*} {Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (P : ProjectedAutomorphicLFunctionWitness W)
    (s : ℂ) :
    IsAutomorphicResonance P.L s ↔
      P.functional.coeff s (W.cuspidalProjector P.bulkState) = 0 :=
  by reexport P.resonance_iff_projected_zero s

/-- Canonical re-export of the projected-L owner target. -/
theorem projectedAutomorphicLFunctionOwnerTarget :
    ProjectedAutomorphicLFunctionOwnerTarget := by
  intro Bulk _ _ Boundary _ _ W Λ F
  intro s
  exact InfoGeometry.Automorphic.SiegelResonance.projectedAutomorphicLFunctionOwnerTarget
    Bulk Boundary W Λ F s

end InfoGeometry.Canonical.ProjectedLFunctionCalibration
