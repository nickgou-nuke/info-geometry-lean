/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMatrixGibbsNontracial
import InfoGeometry.Canonical.FilteredGNSNontracialReadback

/-!
# Nontracial represented Gibbs state from the stage-one tilt Hamiltonian

For real `h` and `β` with `β * h ≠ 0`, the native matrix units distinguish
ordered products under the Gibbs functional for `h • tilt2`. Finite-seed
readback transports this inequality to the algebraic colimit and refutes
traciality of the constructed state on the represented C⋆ closure, for every
choice of vacuum stage. No nontraciality premise or new state carrier is used.

This consumer uses the native finite inequality and completed-state transport;
it does not assert an analytic KMS classification or nontriviality at `β * h = 0`.
-/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.Canonical.AlgebraicKMSStateColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSVacuumState
open CStarStateColimit.Native.FilteredGNSNontracialReadback
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Physics.KleinBottleSewingExact

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))

attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily
  matrixStageStarOrderFamily

attribute [local instance]
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralOrder
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralStarOrderedRing

/-- Explicit stage-one Hamiltonian, actual compatible family and completed state. -/
theorem tiltSeed_representedVacuumState_not_tracial (h β : ℝ)
    (hβh : β * h ≠ 0) (v : ℕ) :
    ¬ representedVacuumIsTracial CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates (k := 1) (h • tilt2)
        (tiltHamiltonian_isHermitian h) β) v := by
  exact finiteSeed_representedVacuumState_not_tracial (k := 1)
    (h • tilt2) (tiltHamiltonian_isHermitian h) β
    (Matrix.single 0 1 (1 : ℂ)) (Matrix.single 1 0 (1 : ℂ))
    (tiltHamiltonian_gibbs_matrixUnits_ne h β hβh) v

/-- The same concrete inequality already survives the native algebraic readback. -/
theorem tiltSeed_algebraic_product_readback_ne (h β : ℝ) (hβh : β * h ≠ 0) :
    normalizedDeltaWeightedFunctional
      (stageUnitToColimit 1 (gibbsDensityUnit (h • tilt2) (tiltHamiltonian_isHermitian h) β))
      (stageInjection 1
        ((Matrix.single 0 1 (1 : ℂ) : MatrixStage 1) * Matrix.single 1 0 (1 : ℂ))) ≠
    normalizedDeltaWeightedFunctional
      (stageUnitToColimit 1 (gibbsDensityUnit (h • tilt2) (tiltHamiltonian_isHermitian h) β))
      (stageInjection 1
        ((Matrix.single 1 0 (1 : ℂ) : MatrixStage 1) * Matrix.single 0 1 (1 : ℂ))) := by
  rw [normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional,
    normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional]
  exact tiltHamiltonian_gibbs_matrixUnits_ne h β hβh

end InfoGeometry.Canonical.AlgebraicKMSStateColimit
