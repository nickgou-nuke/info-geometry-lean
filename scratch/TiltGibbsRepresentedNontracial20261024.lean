/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Canonical.FiniteMatrixGibbsNontracial
import InfoGeometry.Canonical.FilteredGNSNontracialReadback

/-! A concrete nontracial completed Gibbs state from the stage-one tilt seed.
This uncompiled consumer targets the planned native finite and transport owners.
The only nondegeneracy condition is β*h ≠ 0; no nontraciality hypothesis is assumed.
-/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.Canonical.AlgebraicKMSStateColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSVacuumState
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Physics.KleinBottleSewingExact

local instance matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => inferInstance
local instance matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => inferInstance
local instance matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => inferInstance

attribute [local instance]
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralOrder
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralStarOrderedRing

/-- Explicit stage-one Hamiltonian, actual compatible family and completed state. -/
theorem tiltSeed_representedVacuumState_not_tracial (h β : ℝ)
    (hβh : β * h ≠ 0) (v : ℕ) :
    ¬ ∀ A B : representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates (k := 1) (h • tilt2)
          (tiltHamiltonian_isHermitian h) β),
      (representedVacuumState CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates (k := 1) (h • tilt2)
          (tiltHamiltonian_isHermitian h) β) v).functional (A * B) =
      (representedVacuumState CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates (k := 1) (h • tilt2)
          (tiltHamiltonian_isHermitian h) β) v).functional (B * A) := by
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
