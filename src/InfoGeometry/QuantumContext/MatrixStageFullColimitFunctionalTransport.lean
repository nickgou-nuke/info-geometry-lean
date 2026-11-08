/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixStageFullColimitEquivalence

/-!
# Functional transport across the full matrix colimit equivalence

The repository already contains a star-algebra equivalence between the
BitWord-indexed quotient colimit and the canonical `Fin (2^n)` matrix
colimit.  This file transports the existing compatible weighted functional
through that equivalence and proves its exact finite-stage readout.

No completion, state normalization, or identification of a weighted
functional with the canonical trace is asserted here.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MatrixStageFullColimitFunctionalTransport

open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.QuantumContext.MatrixStageFullColimitEquivalence
open InfoGeometry.QuantumContext.MatrixStageWeightedFunctionalColimit

/-- Pull a compatible weighted functional back along the proved comparison
equivalence from the canonical direct-limit carrier to the quotient carrier.
-/
def transportedWeightedFunctional
    (D : ∀ n : ℕ, MatrixStage n)
    (hD : WeightedCompatible D) :
    InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.Carrier → ℂ :=
  fun x => weightedMatrixStageColimitFunctional D hD (carrierToQuotient x)

/-- The transported functional agrees with the original stage functional on
every canonical finite matrix stage.
-/
@[simp] theorem transportedWeightedFunctional_stage
    (D : ∀ n : ℕ, MatrixStage n)
    (hD : WeightedCompatible D) (n : ℕ) (A : MatrixStage n) :
    transportedWeightedFunctional D hD (stageInjection n A) =
      weightedStageFunctional D n A := by
  change weightedMatrixStageColimitFunctional D hD
      (carrierToQuotient (stageInjection n A)) = _
  rw [carrierToQuotient_stage,
    weightedMatrixStageColimitFunctional_stageEquiv]
  simp

end InfoGeometry.QuantumContext.MatrixStageFullColimitFunctionalTransport

end
