/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSMatrixFaithfulness
import InfoGeometry.Canonical.FiniteSeedRepresentedRealTime

/-! Diagnostic candidate only: isolate the first concrete seed-map obligation.
No motion theorem, transparency attributes, or replacement state/flow. -/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.Canonical.SeedStageInjectivityProbe

open CStarStateColimit.Native
open FilteredGNSHilbertColimit FilteredGNSGlobalStageRepresentation
open FilteredGNSRepresentedCStarClosure FilteredGNSAlgebraicColimitRepresentation
open FilteredGNSMatrixRealTime FilteredGNSMatrixFaithfulness
open CantorBernoulliCStarMatrixTraceState CuntzMatrixTowerInstantiation
open AlgebraicKMSStateColimit FiniteSeedRepresentedRealTime

private abbrev stageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => inferInstance
private abbrev stageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => inferInstance
private abbrev stageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => inferInstance
attribute [local instance] stageCStarFamily stageOrderFamily stageStarOrderFamily

variable {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
local notation "ωseed" => finiteSeedCompatibleStageStates H hH β

/-- Proposed native application API: the actual seed map read back as an operator. -/
theorem seedStageHom_coe_apply_probe (a : MatrixStage k) :
    (seedStageHom H hH β a :
      GNSHilbertColimit CStarMatrixStage cstarMatrixInductiveSystem ωseed →L[ℂ]
        GNSHilbertColimit CStarMatrixStage cstarMatrixInductiveSystem ωseed) =
    globalStageRepresentationStarAlgHom CStarMatrixStage cstarMatrixInductiveSystem
      ωseed k ((CStarMatrix.ofMatrixStarAlgEquiv :
        MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k) a) := by
  simp only [seedStageHom, representedMatrixStageMap, StarAlgHom.comp_apply,
    algebraicColimitToRepresentedClosure_coe, algebraicColimitGNSRepresentation_of]

/-- First concrete specialization only: no exponential/action tail in this probe. -/
theorem seedStageHom_injective_probe :
    Function.Injective (seedStageHom H hH β) := by
  intro a b hab
  have hop := congrArg Subtype.val hab
  rw [seedStageHom_coe_apply_probe, seedStageHom_coe_apply_probe] at hop
  exact (CStarMatrix.ofMatrixStarAlgEquiv :
    MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k).injective
    (globalStageRepresentation_injective CStarMatrixStage cstarMatrixInductiveSystem
      ωseed k hop)

end InfoGeometry.Canonical.SeedStageInjectivityProbe
