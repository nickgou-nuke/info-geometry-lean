/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitComparisonWave20
import InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge

noncomputable section

namespace InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge

open CategoryTheory CategoryTheory.Limits
open FilteredColimit
open FilteredColimit.Native
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
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

/-- The native `ModuleCat ℝ` colimit readout into the algebraic direct limit
is injective. Equality of two readouts is moved to a common finite stage by
the filtered-colimit equality criterion; injectivity of the algebraic stage
maps then reflects that equality back to the native colimit. -/
theorem limitReadout_injective : Function.Injective limitReadout.hom := by
  let F := moduleDiagram directSystem ⋙ forget (ModuleCat ℝ)
  let c := (forget (ModuleCat ℝ)).mapCocone
    (colimit.cocone (moduleDiagram directSystem))
  have hc : IsColimit c :=
    isColimitOfPreserves (forget (ModuleCat ℝ))
      (colimit.isColimit (moduleDiagram directSystem))
  intro x y hxy
  obtain ⟨i, xi, hxi⟩ := Types.jointly_surjective_of_isColimit hc x
  obtain ⟨j, yj, hyj⟩ := Types.jointly_surjective_of_isColimit hc y
  change Stage i at xi
  change Stage j at yj
  have hxi' : (colimit.ι (moduleDiagram directSystem) i).hom xi = x := by
    simpa [c] using hxi
  have hyj' : (colimit.ι (moduleDiagram directSystem) j).hom yj = y := by
    simpa [c] using hyj
  have hconcrete : ofStage i xi = ofStage j yj := by
    calc
      ofStage i xi = limitReadout.hom ((colimit.ι (moduleDiagram directSystem) i).hom xi) :=
        (limitReadout_stage_apply i xi).symm
      _ = limitReadout.hom x := by rw [hxi']
      _ = limitReadout.hom y := hxy
      _ = limitReadout.hom ((colimit.ι (moduleDiagram directSystem) j).hom yj) := by
        rw [hyj']
      _ = ofStage j yj := limitReadout_stage_apply j yj
  let k := max i j
  have hik : i ≤ k := Nat.le_max_left i j
  have hjk : j ≤ k := Nat.le_max_right i j
  have hcommon :
      InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf
          stageBond k (bondMap stageBond i k hik xi) =
        InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf
          stageBond k (bondMap stageBond j k hjk yj) := by
    rw [directLimitOf_bondMap stageBond i k hik xi,
      directLimitOf_bondMap stageBond j k hjk yj]
    exact hconcrete
  have hstage :
      bondMap stageBond i k hik xi = bondMap stageBond j k hjk yj := by
    apply (directLimitOf_eq_iff_of_injective
      (bond := stageBond)
      (fun n => InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_injective n)
      (n := k)).mp
    exact hcommon
  have hmaps : F.map (homOfLE hik) xi = F.map (homOfLE hjk) yj := by
    change directSystem.f hik xi = directSystem.f hjk yj
    change stageEmbedMap hik (xi : Stage i) = stageEmbedMap hjk (yj : Stage j)
    rw [coherentStageEmbedMap_eq_bondMap hik xi,
      coherentStageEmbedMap_eq_bondMap hjk yj]
    exact hstage
  have hrep_i :
      (colimit.ι (moduleDiagram directSystem) i).hom xi =
        (colimit.ι (moduleDiagram directSystem) k).hom
          (F.map (homOfLE hik) xi) := by
    have hw := congrArg ModuleCat.Hom.hom
      (colimit.w (moduleDiagram directSystem) (homOfLE hik)).symm
    have hx := LinearMap.congr_fun hw xi
    change (colimit.ι (moduleDiagram directSystem) i).hom xi =
      (colimit.ι (moduleDiagram directSystem) k).hom
        (F.map (homOfLE hik) xi)
    exact hx
  have hrep_j :
      (colimit.ι (moduleDiagram directSystem) j).hom yj =
        (colimit.ι (moduleDiagram directSystem) k).hom
          (F.map (homOfLE hjk) yj) := by
    have hw := congrArg ModuleCat.Hom.hom
      (colimit.w (moduleDiagram directSystem) (homOfLE hjk)).symm
    have hy := LinearMap.congr_fun hw yj
    change (colimit.ι (moduleDiagram directSystem) j).hom yj =
      (colimit.ι (moduleDiagram directSystem) k).hom
        (F.map (homOfLE hjk) yj)
    exact hy
  have hrep_mid :
      (colimit.ι (moduleDiagram directSystem) k).hom
          (F.map (homOfLE hik) xi) =
        (colimit.ι (moduleDiagram directSystem) k).hom
          (F.map (homOfLE hjk) yj) :=
    congrArg (fun z => (colimit.ι (moduleDiagram directSystem) k).hom z) hmaps
  have hrepresentatives :
      (colimit.ι (moduleDiagram directSystem) i).hom xi =
        (colimit.ι (moduleDiagram directSystem) j).hom yj := by
    exact hrep_i.trans (hrep_mid.trans hrep_j.symm)
  rw [← hxi', ← hyj']
  exact hrepresentatives

end InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge
