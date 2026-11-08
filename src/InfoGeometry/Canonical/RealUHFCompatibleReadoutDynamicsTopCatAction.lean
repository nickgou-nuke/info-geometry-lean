import InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The scalar readout dynamics as a `TopCat` action

This packages the already-proved pullback evolution as continuous endomorphisms
of the compatible-family carrier.  The laws are categorical composition laws;
the construction remains below any completed UHF or KMS claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopological
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit

noncomputable def scalarDilationTopCatAction (t : ℝ) :
    TopCat.of CompatibleContinuousReadoutFamily ⟶
      TopCat.of CompatibleContinuousReadoutFamily :=
  TopCat.ofHom
    { toFun := fun ρ => pullback scalarDilationStageFlow t ρ
      continuous_toFun :=
        continuous_scalarDilation_pullback.comp
          ((continuous_const :
            Continuous (fun _ : CompatibleContinuousReadoutFamily => t)).prodMk
            continuous_id) }

@[simp] theorem scalarDilationTopCatAction_apply
    (t : ℝ) (ρ : CompatibleContinuousReadoutFamily) :
    scalarDilationTopCatAction t ρ =
      pullback scalarDilationStageFlow t ρ := by
  simp [scalarDilationTopCatAction]

theorem scalarDilationTopCatAction_zero :
    scalarDilationTopCatAction 0 =
      𝟙 (TopCat.of CompatibleContinuousReadoutFamily) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  simpa [scalarDilationTopCatAction] using
    scalarDilation_pullback_zero_action ρ

theorem scalarDilationTopCatAction_add (s t : ℝ) :
    scalarDilationTopCatAction (s + t) =
      scalarDilationTopCatAction s ≫ scalarDilationTopCatAction t := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro ρ
  simpa [scalarDilationTopCatAction] using
    scalarDilation_pullback_add_action s t ρ

end InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
