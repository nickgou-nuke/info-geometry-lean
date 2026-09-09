import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitOrbitClosureCompHaus

/-!
# Finite-stage observations on inverse-limit symbolic-latent orbit closures

This owner restricts an existing inverse-limit stage evaluation to a native
symbolic-latent orbit closure.  It proves the exact scalar covariance of that
observable under the inverse-limit action, but does not assert compactness or
surjectivity of the resulting observation range.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev carrier :=
  (limit readoutDiagram).carrier

abbrev flow := scalarDilationSymbolicLatentFlow

variable [T2Space carrier]

def stageObservationTopCatHom
    (n : ℕ) (X : MatStage n) :
    TopCat.of carrier ⟶ TopCat.of ℝ :=
  inverseLimitStageEvaluationTopCatHom n X

@[simp] theorem stageObservationTopCatHom_apply
    (n : ℕ) (X : MatStage n) (ρ : carrier) :
    stageObservationTopCatHom n X ρ =
      inverseLimitStageEvaluationTopCatHom n X ρ := rfl

def orbitClosureStageObservationTopCatHom
    (ρ : carrier) (n : ℕ) (X : MatStage n) :
    TopCat.of (SymbolicLatentModularOrbitClosure flow ρ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun y => stageObservationTopCatHom n X y.1
      continuous_toFun :=
        (stageObservationTopCatHom n X).hom.continuous.comp
          continuous_subtype_val }

@[simp] theorem orbitClosureStageObservationTopCatHom_apply
    (ρ : carrier) (n : ℕ) (X : MatStage n)
    (y : SymbolicLatentModularOrbitClosure flow ρ) :
    orbitClosureStageObservationTopCatHom ρ n X y =
      stageObservationTopCatHom n X y.1 := rfl

theorem orbitClosureStageObservation_scalar_covariance
    (ρ : carrier) (n : ℕ) (t : ℝ) (X : MatStage n)
    (y : SymbolicLatentModularOrbitClosure flow ρ) :
    orbitClosureStageObservationTopCatHom (flow.act t ρ) n X
        (⟨flow.act t y.1, by
          rw [← flow.actHomeomorph_image_orbitClosure t ρ]
          exact ⟨y.1, y.2, rfl⟩⟩) =
      (Real.exp t) •
        orbitClosureStageObservationTopCatHom ρ n X y := by
  change stageObservationTopCatHom n X (flow.act t y.1) =
    (Real.exp t) • stageObservationTopCatHom n X y.1
  simpa [stageObservationTopCatHom, flow,
    scalarDilationSymbolicLatentFlow_apply] using
    (inverseLimitStageEvaluation_action_scalar y.1 n t X)

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
end
