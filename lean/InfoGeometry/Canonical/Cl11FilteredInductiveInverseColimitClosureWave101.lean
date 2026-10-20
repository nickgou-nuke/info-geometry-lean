/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge

noncomputable section

namespace InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge

open CategoryTheory CategoryTheory.Limits
open FilteredColimit
open FilteredColimit.Native
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- The canonical map from the native `ModuleCat` colimit to the concrete
`Cl(1,1)` direct-limit carrier is uniquely determined by its stage maps. -/
theorem limitReadout_unique
    (f : nativeModuleColimit ⟶ ModuleCat.of ℝ Limit)
    (hf : ∀ n : ℕ,
      colimit.ι (moduleDiagram directSystem) n ≫ f =
        (moduleCocone directSystem colimitCocone).ι.app n) :
    f = limitReadout := by
  apply colimit.hom_ext
  intro n
  rw [hf n, limitReadout_stage n]

/-- Any linear readout on the concrete direct limit that agrees with the
finite normalized traces factors exactly through the canonical stage map. -/
theorem traceReadout_factorization_unique
    (f : Limit →ₗ[ℝ] ℝ)
    (hf : ∀ (n : ℕ) (A : Stage n),
      f (ofStage n A) =
        normalizedTrace n A) :
    traceReadout = limitReadout ≫ ModuleCat.ofHom f := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro A
  let A' : Stage n := A
  dsimp [nativeModuleColimit]
  change traceReadout ((colimit.ι (moduleDiagram directSystem) n).hom A') =
    f (limitReadout ((colimit.ι (moduleDiagram directSystem) n).hom A'))
  calc
    traceReadout ((colimit.ι (moduleDiagram directSystem) n).hom A') =
        normalizedTrace n A' := traceReadout_stage_apply n A
    _ = f (ofStage n A') := (hf n A').symm
    _ = f (limitReadout ((colimit.ι (moduleDiagram directSystem) n).hom A')) := by
      rw [limitReadout_stage_apply n A']

end InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge

#print axioms InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge.limitReadout_unique
#print axioms InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge.traceReadout_factorization_unique
