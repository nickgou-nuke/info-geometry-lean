/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.IncompressibleBitBridge
import InfoGeometry.Canonical.SpectralInference
import Mathlib.LinearAlgebra.Determinant

namespace InfoGeometry.Canonical.ChiralAction

open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.SpectralInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The finite-dimensional operator perturbation `D + g • χ`. -/
noncomputable def chiralDirac (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g : ℝ) : E →L[ℝ] E :=
  IST.D + g • CI.chiralAnomaly

/-- Log absolute determinant of the square of an endomorphism, scaled by `Λ²`. -/
noncomputable def logAbsSquareDetAction (D : E →L[ℝ] E) (Λ : ℝ) : ℝ :=
  Real.log (|LinearMap.det (D * D).toLinearMap|) / (Λ ^ 2)

/-- The corresponding action of the unperturbed information Dirac operator. -/
noncomputable def spectralInformationAction (IST : InfoSpectralTriple E) (Λ : ℝ) : ℝ :=
  logAbsSquareDetAction IST.D Λ

/-- The same finite-dimensional observable evaluated on the chiral perturbation. -/
noncomputable def chiralInformationAction (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g Λ : ℝ) : ℝ :=
  logAbsSquareDetAction (chiralDirac IST CI g) Λ

omit [FiniteDimensional ℝ E] in
/--
Theorem: If the inference system is normal (ε = 0), the Chiral Information Action
reduces to the standard Spectral Action.
-/
theorem chiral_action_reduces_for_normal (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g : ℝ)
    (h_normal : CI.IsNormalInference) :
    chiralDirac IST CI g = IST.D := by
  have hActionZero : CI.unitOfAction = 0 :=
    CI.unitOfAction_eq_zero_of_normalInference h_normal
  have hNormZero : ‖CI.actionStructureConstantOp‖ = 0 := by
    simpa [ConformalInference.unitOfAction] using hActionZero
  have hActionOpZero : CI.actionStructureConstantOp = 0 :=
    norm_eq_zero.mp hNormZero
  have hc : CI.chiralAnomaly = 0 := by
    have hAnomZero : CI.chiralAnomalyOperator = 0 := by
      simpa [CI.actionStructureConstantOp_eq_chiralAnomalyOperator] using hActionOpZero
    simpa [ConformalInference.chiralAnomalyOperator] using hAnomZero
  unfold chiralDirac
  rw [hc, smul_zero, add_zero]

omit [FiniteDimensional ℝ E] in
/-- Normal inference makes the perturbed determinant action equal the base action. -/
theorem chiralInformationAction_eq_spectralInformationAction_of_normal
    (IST : InfoSpectralTriple E) (CI : ConformalInference E) (g Λ : ℝ)
    (hNormal : CI.IsNormalInference) :
    chiralInformationAction IST CI g Λ = spectralInformationAction IST Λ := by
  change logAbsSquareDetAction (chiralDirac IST CI g) Λ =
    logAbsSquareDetAction IST.D Λ
  rw [chiral_action_reduces_for_normal IST CI g hNormal]

end InfoGeometry.Canonical.ChiralAction
