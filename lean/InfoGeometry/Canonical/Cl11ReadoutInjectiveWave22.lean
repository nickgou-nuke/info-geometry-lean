/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitComparisonWave20

noncomputable section
namespace InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge
open CategoryTheory CategoryTheory.Limits
open FilteredColimit FilteredColimit.Native
open InfoGeometry.Clifford.Cl11TensorTowerLimit

abbrev DirectCarrier : Type := Module.DirectLimit Stage
  (fun m n h => directSystem.f h)

noncomputable def directCocone : Cocone (moduleDiagram directSystem) where
  pt := ModuleCat.of ℝ DirectCarrier
  ι :=
    { app := fun n => ModuleCat.ofHom
        (Module.DirectLimit.of ℝ ℕ Stage
          (fun m n h => directSystem.f h) n)
      naturality := by
        intro m n f
        ext x
        exact Module.DirectLimit.of_f }

noncomputable def directCoconeIsColimit : IsColimit directCocone where
  desc t := ModuleCat.ofHom
    (Module.DirectLimit.lift ℝ ℕ Stage
      (fun m n h => directSystem.f h)
      (fun n => (t.ι.app n).hom)
      (by
        intro m n h x
        have hn := t.ι.naturality (homOfLE h)
        have hn' := congrArg (fun g => g x) hn
        simpa using hn'.symm))
  fac t n := by
    ext x
    exact Module.DirectLimit.lift_of _ _
  uniq t m hm := by
    apply Module.DirectLimit.hom_ext
    intro n
    ext x
    exact congrArg (fun g => g x) (hm n)

noncomputable def nativeDirectIso :
    ModuleCat.of ℝ DirectCarrier ≅ nativeModuleColimit :=
  directCoconeIsColimit.coconePointUniqueUpToIso (colimit.isColimit _)

noncomputable def directLift : DirectCarrier →ₗ[ℝ] Limit :=
  Module.DirectLimit.lift ℝ ℕ Stage
    (fun m n h => directSystem.f h)
    (fun n => colimitCocone.psi n)
    (by
      intro m n h x
      exact colimitCocone_eval h x)

theorem nativeDirectIso_hom_limitReadout :
    (limitReadout.hom).comp nativeDirectIso.hom.hom = directLift := by
  apply Module.DirectLimit.hom_ext
  intro n
  ext x
  change limitReadout ((colimit.ι (moduleDiagram directSystem) n).hom x) = _
  rw [limitReadout_stage_apply]
  exact Module.DirectLimit.lift_of _ _

theorem limitReadout_injective :
    Function.Injective limitReadout.hom := by
  have hcomp : Function.Injective ((limitReadout.hom).comp nativeDirectIso.hom.hom) := by
    rw [nativeDirectIso_hom_limitReadout]
    apply Module.DirectLimit.lift_injective
    intro n
    change Function.Injective (ofStage n)
    exact InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf_injective
      (fun n => (stageEmbed n).toRingHom)
      (fun n => stageEmbed_injective n)
      n
  intro x y hxy
  apply nativeDirectIso.hom.hom.injective
  apply hcomp
  exact hxy

end InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge
