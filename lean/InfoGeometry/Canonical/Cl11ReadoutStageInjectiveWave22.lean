/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitComparisonWave20

noncomputable section

namespace InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge

open CategoryTheory CategoryTheory.Limits
open FilteredColimit
open FilteredColimit.Native
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- Each finite `Cl(1,1)` stage is faithfully represented by the native
`ModuleCat` colimit readout. -/
theorem limitReadout_stage_injective (n : ℕ) :
    Function.Injective
      (fun x : Stage n =>
        limitReadout ((colimit.ι (moduleDiagram directSystem) n).hom x)) := by
  intro x y hxy
  change limitReadout ((colimit.ι (moduleDiagram directSystem) n).hom x) =
    limitReadout ((colimit.ι (moduleDiagram directSystem) n).hom y) at hxy
  rw [limitReadout_stage_apply n x, limitReadout_stage_apply n y] at hxy
  exact InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_injective
    InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond
    (fun k => by
      change Function.Injective
        (fun A : InfoGeometry.Clifford.Cl11TensorTower.MatStage k =>
          InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed k A)
      exact InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_injective k)
    n hxy

end InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge
