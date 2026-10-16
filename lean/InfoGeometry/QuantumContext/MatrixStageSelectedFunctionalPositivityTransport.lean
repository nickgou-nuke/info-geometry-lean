/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixStageFullColimitEquivalence
import InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity
import InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamily

/-!
# Selected-functional positivity across the matrix colimit presentations

This module identifies the selected-family functional on the BitWord quotient
with the pullback of the selected functional on the Mathlib direct-limit
carrier. It transfers nonnegative real parts on star-squares. It makes no
claim about a normalized state or a completion.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MatrixStageSelectedFunctionalPositivityTransport

open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.QuantumContext.MatrixStageFullColimitEquivalence
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamily
open InfoGeometry.QuantumContext.MatrixStageSelectedMatrixFamilyPositivity
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional

/-- The selected-family functional on the BitWord quotient is the pullback
of the selected functional on the canonical direct-limit carrier. -/
theorem selectedFamilyFunctional_eq_pullback (k : ℕ) (Dk : MatrixStage k)
    (x : MatrixStageLimit) :
    selectedMatrixFamilyColimitFunctional k Dk x =
      selectedStageColimitFunctional k Dk (carrierStarAlgEquiv x) := by
  induction x using Quotient.inductionOn with
  | h rep =>
      rcases rep with ⟨n, A⟩
      change selectedMatrixFamilyColimitFunctional k Dk (canonicalStageHom n A) =
        selectedStageColimitFunctional k Dk
          (stageInjection n (stageStarAlgEquiv n A))
      rw [selectedMatrixFamilyColimitFunctional_stage]
      change matrixTraceFunctional n
          (stageStarAlgEquiv n A * selectedMatrixFamily k Dk n) =
        colimitFunctional (selectedStageFunctional k Dk)
          (selectedStageFunctional_compatible k Dk)
          (stageInjection n (stageStarAlgEquiv n A))
      rw [colimitFunctional_stage,
        selectedStageFunctional_eq_weightedSelectedFamily]
      rw [weightedStageFunctional_apply]

/-- Bundle the selected-family quotient functional as a complex-linear map by
transporting the already descended direct-limit `LinearMap` across the proved
full-matrix colimit equivalence. -/
def selectedFamilyLinearFunctional (k : ℕ) (Dk : MatrixStage k) :
    MatrixStageLimit →ₗ[ℂ] ℂ :=
  (selectedStageColimitFunctional k Dk).comp
    carrierStarAlgEquiv.toAlgEquiv.toLinearMap

/-- The bundled linear map has exactly the values of the functional descended
from the compatible partial-trace family. -/
theorem selectedFamilyLinearFunctional_apply (k : ℕ) (Dk : MatrixStage k)
    (x : MatrixStageLimit) :
    selectedFamilyLinearFunctional k Dk x =
      selectedMatrixFamilyColimitFunctional k Dk x := by
  simpa [selectedFamilyLinearFunctional] using
    (selectedFamilyFunctional_eq_pullback k Dk x).symm

/-- Positivity on star-squares transports to the BitWord quotient through the
full-matrix colimit star-algebra equivalence. -/
theorem selectedFamilyFunctional_positive (k : ℕ) (Dk : MatrixStage k)
    (hD : InfoGeometry.Quantum.FiniteAttentionCanonicalBridges.ComplexPositive Dk)
    (x : MatrixStageLimit) :
    0 ≤ (selectedFamilyLinearFunctional k Dk (star x * x)).re := by
  change 0 ≤ (selectedStageColimitFunctional k Dk
    (carrierStarAlgEquiv (star x * x))).re
  rw [map_mul carrierStarAlgEquiv (star x) x, map_star carrierStarAlgEquiv x]
  exact selectedStageColimitFunctional_positive k Dk hD (carrierStarAlgEquiv x)

/-- Hermitian seed data makes the same star-square functional value real. -/
theorem selectedFamilyFunctional_starSquare_im_zero (k : ℕ) (Dk : MatrixStage k)
    (hD : Dk.IsHermitian) (x : MatrixStageLimit) :
    (selectedFamilyLinearFunctional k Dk (star x * x)).im = 0 := by
  change (selectedStageColimitFunctional k Dk
    (carrierStarAlgEquiv (star x * x))).im = 0
  rw [map_mul carrierStarAlgEquiv (star x) x, map_star carrierStarAlgEquiv x]
  exact selectedStageColimitFunctional_starSquare_im_zero k Dk hD
    (carrierStarAlgEquiv x)

end InfoGeometry.QuantumContext.MatrixStageSelectedFunctionalPositivityTransport
