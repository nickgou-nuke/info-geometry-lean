/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMappedGibbsDensityExponential

/-! Actual represented density exponential, v7 consumer.
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

section Seed
variable {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
local notation "SeedClosure" => representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem
  (finiteSeedCompatibleStageStates H hH β)

/-- All local structure choices are projections of this actual native closure instance. -/
local instance seedClosureCStarAlgebra : CStarAlgebra SeedClosure :=
  representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)

local instance seedClosureNormedRing : NormedRing SeedClosure :=
  (representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)).toNormedRing

local instance seedClosureSeminormedRing : SeminormedRing SeedClosure :=
  @NormedRing.toSeminormedRing SeedClosure
    (representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β)).toNormedRing

local instance seedClosureRing : Ring SeedClosure :=
  (representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)).toNormedRing.toRing

local instance seedClosureMetricSpace : MetricSpace SeedClosure :=
  (representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)).toNormedRing.toMetricSpace

local instance seedClosureTopology : TopologicalSpace SeedClosure :=
  (representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)).toNormedRing.toMetricSpace.toUniformSpace.toTopologicalSpace

/-- The multiplicative structure is the projection of the native closure ring. -/
local instance seedClosureMonoid : Monoid SeedClosure :=
  (representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)).toNormedRing.toRing.toMonoid

/-- Select the standard real restriction of the native complex algebra explicitly. -/
local instance seedClosureRealSMul : SMul ℝ SeedClosure :=
  (@Algebra.complexToReal SeedClosure
    (representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β)).toNormedRing.toRing.toSemiring
    (representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β)).toNormedAlgebra.toAlgebra).toSMul

/-- The existing represented density, for every real inverse temperature. -/
theorem representedDensityUnit_coe_eq_exp :
    (representedDensityUnit H hH β :
      representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β)) =
      NormedSpace.exp (@SMul.smul ℝ SeedClosure (seedClosureRealSMul H hH β)
        (-β) (seedStageHom H hH β H)) := by
  change (seedStageHom H hH β) (↑(gibbsDensityUnit H hH β)) = _
  rw [gibbsDensityUnit_coe]
  exact map_gibbsDensity_eq_exp (A := SeedClosure) (seedStageHom H hH β) H hH β

/-- Opposite exponential for the inverse of that same actual represented unit. -/
theorem representedDensityUnit_inv_coe_eq_exp :
    (↑((representedDensityUnit H hH β : SeedClosureˣ)⁻¹) : SeedClosure) =
      NormedSpace.exp (@SMul.smul ℝ SeedClosure (seedClosureRealSMul H hH β)
        β (seedStageHom H hH β H)) := by
  exact map_gibbsDensityUnit_inv_eq_exp (A := SeedClosure) (seedStageHom H hH β) H hH β

end Seed

end InfoGeometry.Canonical.FiniteSeedRepresentedDensityExponential
