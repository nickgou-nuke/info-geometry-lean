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
@[rep_depth thermo] structure ObstructionScalarReadout : Prop where
  projectorObstruction_nnnorm_eq_chiralScale :
    ‖CI.projectorObstruction‖₊ = CI.chiralScale
  chiralScale_eq_projectorObstruction_nnnorm :
    CI.chiralScale = ‖CI.projectorObstruction‖₊
  unitOfAction_eq_chiralScale :
    CI.unitOfAction = CI.chiralScale
  unitOfAction_eq_projectorObstruction_nnnorm :
    CI.unitOfAction = ‖CI.projectorObstruction‖₊

section

/-- Canonical scalar readout map from the obstruction operator layer. -/
@[rep_depth thermo] theorem obstructionScalarReadout :
    ObstructionScalarReadout (CI := CI) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact CI.projectorObstruction_nnnorm_eq_chiralScale
  · exact CI.chiralScale_eq_projectorObstruction_nnnorm
  · exact CI.unitOfAction_eq_chiralScale
  · calc
      CI.unitOfAction = CI.chiralScale := CI.unitOfAction_eq_chiralScale
      _ = ‖CI.projectorObstruction‖₊ := CI.chiralScale_eq_projectorObstruction_nnnorm

end

end ConformalInference

end InfoGeometry.Canonical.ConformalUnification
