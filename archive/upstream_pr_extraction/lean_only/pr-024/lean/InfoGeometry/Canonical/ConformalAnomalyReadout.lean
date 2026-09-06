import InfoGeometry.Canonical.ConformalAnomalyOperator

namespace InfoGeometry.Canonical.ConformalUnification

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ConformalInference

variable (CI : ConformalInference E)

/--
Functorial scalar readout package from the operator owner layer.

These are representation maps from the noncommutative obstruction operator into
scalar image lanes (`‖·‖₊` and derived scalars), not independent sources.
-/
@[rep_depth thermo] def ObstructionScalarReadout : Prop :=
  ‖CI.projectorObstruction‖₊ = CI.obstructionScale ∧
  CI.obstructionScale = ‖CI.projectorObstruction‖₊ ∧
  CI.chiralScale = CI.obstructionScale ∧
  CI.epsilon = CI.obstructionScale ∧
  CI.unitOfAction = CI.obstructionScale ∧
  CI.unitOfAction = ‖CI.projectorObstruction‖₊

section

/-- Canonical scalar readout map from the obstruction operator layer. -/
@[rep_depth thermo] theorem obstructionScalarReadout :
    ObstructionScalarReadout (CI := CI) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact CI.projectorObstruction_nnnorm_eq_obstructionScale
  · exact CI.obstructionScale_eq_projectorObstruction_nnnorm
  · exact CI.chiralScale_eq_obstructionScale
  · exact CI.epsilon_eq_obstructionScale
  · exact CI.unitOfAction_eq_obstructionScale
  · calc
      CI.unitOfAction = CI.obstructionScale := CI.unitOfAction_eq_obstructionScale
      _ = ‖CI.projectorObstruction‖₊ := CI.obstructionScale_eq_projectorObstruction_nnnorm

end

end ConformalInference

end InfoGeometry.Canonical.ConformalUnification
