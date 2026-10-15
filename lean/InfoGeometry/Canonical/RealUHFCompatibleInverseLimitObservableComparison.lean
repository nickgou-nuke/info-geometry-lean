import InfoGeometry.Canonical.RealUHFCompatibleInverseLimitFlowComparison
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables
import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat

/-!
# Observable comparison on symbolic-latent orbit closures

The compatible readout carrier and the native inverse-limit carrier are kept as
distinct types.  This owner compares their finite-stage observables after the
canonical carrier map.  It does not identify the carriers by an unproved
definitional equality and it does not add any completion or `K`-theory claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleInverseLimitObservableComparison

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleInverseLimitFlowComparison
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitObservables
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat
open InfoGeometry.Canonical.RealUHFCompatibleStateObservableTopCat
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev compatibleOrbitClosure (ρ : compatibleCarrier) :=
  SymbolicLatentModularOrbitClosure compatibleFlow ρ

noncomputable def compatibleOrbitClosureStageObservationTopCatHom
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n) :
    TopCat.of (compatibleOrbitClosure ρ) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := fun y => coordinateEvaluationTopCatHom n X y.1
      continuous_toFun :=
        (coordinateEvaluationTopCatHom n X).hom.continuous.comp
          continuous_subtype_val }

@[simp] theorem compatibleOrbitClosureStageObservationTopCatHom_apply
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n)
    (y : compatibleOrbitClosure ρ) :
    compatibleOrbitClosureStageObservationTopCatHom ρ n X y =
      coordinateEvaluationTopCatHom n X y.1 := rfl

theorem canonical_orbitClosure_stageObservation_square
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n) :
    canonicalOrbitClosureTopCatHom ρ ≫
        orbitClosureStageObservationTopCatHom
          (canonicalData.map ρ) n X =
      compatibleOrbitClosureStageObservationTopCatHom ρ n X := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  change stageObservationTopCatHom n X
      (canonicalOrbitClosureMap ρ y) =
    coordinateEvaluationTopCatHom n X y.1
  rw [canonicalOrbitClosureMap_inclusion]
  exact canonical_stage_observation_agreement y.1 n X

theorem canonical_orbitClosure_stageObservation_apply
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n)
    (y : compatibleOrbitClosure ρ) :
    stageObservationTopCatHom n X (canonicalOrbitClosureMap ρ y) =
      coordinateEvaluationTopCatHom n X y.1 := by
  have h := congrArg (fun f => f y)
    (canonical_orbitClosure_stageObservation_square ρ n X)
  rw [TopCat.comp_app, canonicalOrbitClosureTopCatHom_apply,
    compatibleOrbitClosureStageObservationTopCatHom_apply] at h
  exact h

noncomputable def compatibleOrbitClosureToInverseStageObservationRangeTopCatHom
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n) :
    TopCat.of (compatibleOrbitClosure ρ) ⟶
      TopCat.of (stageObservationRange (canonicalData.map ρ) n X) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨coordinateEvaluationTopCatHom n X y.1, by
          exact ⟨canonicalOrbitClosureMap ρ y,
            canonical_orbitClosure_stageObservation_apply ρ n X y⟩⟩
      continuous_toFun :=
        (coordinateEvaluationTopCatHom n X).hom.continuous.comp
          continuous_subtype_val |>.subtype_mk (by
            intro y
            exact ⟨canonicalOrbitClosureMap ρ y,
              canonical_orbitClosure_stageObservation_apply ρ n X y⟩) }

@[simp] theorem compatibleOrbitClosureToInverseStageObservationRangeTopCatHom_apply
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n)
    (y : compatibleOrbitClosure ρ) :
    compatibleOrbitClosureToInverseStageObservationRangeTopCatHom
        ρ n X y =
      ⟨coordinateEvaluationTopCatHom n X y.1, by
        exact ⟨canonicalOrbitClosureMap ρ y,
          canonical_orbitClosure_stageObservation_apply ρ n X y⟩⟩ := rfl

theorem compatibleOrbitClosureToInverseStageObservationRange_factorization
    (ρ : compatibleCarrier) (n : ℕ) (X : MatStage n) :
    compatibleOrbitClosureToInverseStageObservationRangeTopCatHom
        ρ n X ≫
        stageObservationRangeInclusionTopCatHom
          (canonicalData.map ρ) n X =
      compatibleOrbitClosureStageObservationTopCatHom ρ n X := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

end InfoGeometry.Canonical.RealUHFCompatibleInverseLimitObservableComparison
end
