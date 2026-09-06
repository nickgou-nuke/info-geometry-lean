import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
import InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction

/-!
# Dynamics transported to the categorical readout limit

The finite-stage scalar action is a natural transformation of the readout
diagram.  Mathlib's native `limit.map` therefore supplies the corresponding
action on the categorical inverse limit.  This owner records the projection
formula and makes no completion or KMS claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutStageActionTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction

def scalarDilationReadoutNatTrans (t : ℝ) :
    readoutDiagram ⟶ readoutDiagram :=
  NatTrans.ofSequence
    (app := fun n => stageReadoutActionTopCatHom n t)
    (naturality := by
      intro n
      have hmap :
          readoutDiagram.map (homOfLE (Nat.le_succ n)) =
            readoutPullbackTopCatHom n := by
        simpa [readoutDiagram] using
          (Functor.ofSequence_map_homOfLE_succ
            (f := fun n => readoutPullbackTopCatHom n) n)
      rw [hmap]
      change readoutPullbackTopCatHom n ≫
          stageReadoutActionTopCatHom (n + 1) t =
        stageReadoutActionTopCatHom n t ≫
          readoutPullbackTopCatHom n
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro ρ
      apply ContinuousLinearMap.ext
      intro X
      change stageReadoutActionContinuous (n + 1) t
          (readoutPullbackCLM n ρ) X =
        readoutPullbackCLM n
          (stageReadoutActionContinuous n t ρ) X
      simpa [readoutPullbackCLM_apply] using
        (stageReadoutActionContinuous_restriction_naturality n t ρ X).symm)

noncomputable def scalarDilationReadoutInverseLimitAction (t : ℝ) :
    limit readoutDiagram ⟶ limit readoutDiagram :=
  lim.map (scalarDilationReadoutNatTrans t)

theorem scalarDilationReadoutInverseLimitAction_projection
    (t : ℝ) (n : ℕ) :
    scalarDilationReadoutInverseLimitAction t ≫
        limit.π readoutDiagram n =
      limit.π readoutDiagram n ≫
        (scalarDilationReadoutNatTrans t).app n := by
  change IsLimit.map (limit.cone readoutDiagram)
      (limit.isLimit readoutDiagram)
      (scalarDilationReadoutNatTrans t) ≫
        (limit.cone readoutDiagram).π.app n =
    (limit.cone readoutDiagram).π.app n ≫
      (scalarDilationReadoutNatTrans t).app n
  exact IsLimit.map_π (limit.cone readoutDiagram)
    (limit.isLimit readoutDiagram)
    (scalarDilationReadoutNatTrans t) n

theorem scalarDilationReadoutInverseLimitAction_projection_apply
    (t : ℝ) (n : ℕ)
    (x : TopCat.carrier (limit readoutDiagram)) :
    (limit.π readoutDiagram n)
        (scalarDilationReadoutInverseLimitAction t x) =
      (stageReadoutActionTopCatHom n t)
        ((limit.π readoutDiagram n) x) := by
  exact congrArg (fun f => f x)
    (scalarDilationReadoutInverseLimitAction_projection t n)

theorem scalarDilationReadoutInverseLimitAction_transport
    (t : ℝ) :
    scalarDilationTopCatAction t ≫
        compatibleReadoutInverseLimitIso.hom =
      compatibleReadoutInverseLimitIso.hom ≫
        scalarDilationReadoutInverseLimitAction t := by
  apply (limit.isLimit readoutDiagram).hom_ext
  intro n
  simp only [Category.assoc]
  change scalarDilationTopCatAction t ≫
        compatibleReadoutInverseLimitIso.hom ≫
        limit.π readoutDiagram n =
      compatibleReadoutInverseLimitIso.hom ≫
        scalarDilationReadoutInverseLimitAction t ≫
        limit.π readoutDiagram n
  rw [show compatibleReadoutInverseLimitIso.hom ≫
        limit.π readoutDiagram n = readoutInverseCone.π.app n by
      simpa [compatibleReadoutInverseLimitIso] using
        (IsLimit.conePointUniqueUpToIso_hom_comp
          readoutInverseConeIsLimit (limit.isLimit readoutDiagram) n)]
  rw [scalarDilationReadoutInverseLimitAction_projection t n]
  rw [← Category.assoc]
  rw [show compatibleReadoutInverseLimitIso.hom ≫
        limit.π readoutDiagram n = readoutInverseCone.π.app n by
      simpa [compatibleReadoutInverseLimitIso] using
        (IsLimit.conePointUniqueUpToIso_hom_comp
          readoutInverseConeIsLimit (limit.isLimit readoutDiagram) n)]
  exact coordinateTopCatHom_action_square n t

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics

end
