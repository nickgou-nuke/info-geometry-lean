import InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction

/-!
# State-side coordinate naturality for the compatible-family action

The topological action on compatible readout families is compatible with every
finite-stage coordinate.  This is the state-side counterpart of the colimit
readout covariance theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopologicalDynamics

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopCat
open InfoGeometry.Clifford.Cl11TensorTower

theorem scalarDilationTopCatAction_zero :
    scalarDilationTopCatAction 0 =
      𝟙 (TopCat.of CompatibleContinuousReadoutFamily) := by
  exact InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction.scalarDilationTopCatAction_zero

theorem scalarDilationTopCatAction_add (s t : ℝ) :
    scalarDilationTopCatAction (s + t) =
      scalarDilationTopCatAction s ≫ scalarDilationTopCatAction t := by
  exact InfoGeometry.Canonical.RealUHFCompatibleReadoutDynamicsTopCatAction.scalarDilationTopCatAction_add s t

theorem coordinateTopCatHom_scalarDilation_naturality
    (t : ℝ) (n : ℕ)
    (ρ : CompatibleContinuousReadoutFamily)
    (X : MatStage n) :
    (coordinateTopCatHom n)
        (scalarDilationTopCatAction t ρ) X =
      ρ.1 n ((scalarDilationStageFlow.flow n t) X) := by
  rw [scalarDilationTopCatAction_apply]
  exact pullback_apply scalarDilationStageFlow t ρ n X

theorem coordinateTopCatHom_scalarDilation_naturality_exp
    (t : ℝ) (n : ℕ)
    (ρ : CompatibleContinuousReadoutFamily)
    (X : MatStage n) :
    (coordinateTopCatHom n)
        (scalarDilationTopCatAction t ρ) X =
      ρ.1 n (Real.exp t • X) := by
  simpa only [scalarDilationStageFlow_apply] using
    coordinateTopCatHom_scalarDilation_naturality t n ρ X

theorem scalarDilationTopCatAction_coordinate_zero
    (n : ℕ) (X : MatStage n) (ρ : CompatibleContinuousReadoutFamily) :
    coordinateTopCatHom n
        (scalarDilationTopCatAction 0 ρ) X = ρ.1 n X := by
  simpa using
    coordinateTopCatHom_scalarDilation_naturality 0 n ρ X

end InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitTopologicalDynamics
