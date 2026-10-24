/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteSeedRepresentationFaithfulness

/-! Uncompiled action-alignment diagnostic. No new state, map or flow.
Compare the native inferred automorphism type before and after application.
No motion claim and no re-proving of the accepted seed injectivity theorem. -/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.Canonical.SeedRealTimeActionAlignmentProbeV2

open CStarStateColimit.Native
open FilteredGNSMatrixRealTime
open CantorBernoulliCStarMatrixTraceState CuntzMatrixTowerInstantiation
open AlgebraicKMSStateColimit FiniteSeedRepresentedRealTime

private abbrev stageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun _n => inferInstance
private abbrev stageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun _n => inferInstance
private abbrev stageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun _n => inferInstance
attribute [local instance] stageCStarFamily stageOrderFamily stageStarOrderFamily

variable {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)

/-- First boundary: the whole automorphism, without observable application. -/
theorem seedRealTimeAut_eq_matrixRealTimeAut_probe (t : ℝ) :
    seedRealTimeAut H hH β t =
      matrixRealTimeAut CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) (seedStageHom H hH β) H hH t := by
  rfl

/-- Second boundary: application to the actual represented seed observable. -/
theorem seedRealTimeAut_apply_eq_matrixRealTimeAut_probe
    (t : ℝ) (x : MatrixStage k) :
    seedRealTimeAut H hH β t (seedStageHom H hH β x) =
      matrixRealTimeAut CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) (seedStageHom H hH β) H hH t
        (seedStageHom H hH β x) := by
  exact DFunLike.congr_fun (seedRealTimeAut_eq_matrixRealTimeAut_probe H hH β t)
    (seedStageHom H hH β x)

end InfoGeometry.Canonical.SeedRealTimeActionAlignmentProbeV2
