/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import scratch.FiniteMappedGibbsDensityExponential20261024

/-! Actual represented density exponential, v4 consumer.
The explicit local C⋆ instance is the existing native closure instance.
No new carrier, norm, hypothesis, budget, or transparency setting.
-/
noncomputable section
open scoped ComplexOrder
namespace InfoGeometry.Canonical.FiniteSeedRepresentedDensityExponential
open FiniteMatrixGibbsFunctional

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

/-- Select the existing closure instance before elaborating its exponential. -/
local instance seedClosureCStarAlgebra {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    CStarAlgebra (representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β)) :=
  representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)

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
