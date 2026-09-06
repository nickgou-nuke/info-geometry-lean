import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.ConformalAnomalySource
import InfoGeometry.Canonical.ConformalAnomalyOperator
import InfoGeometry.Canonical.ConformalAnomalyReadout
import InfoGeometry.Canonical.ConformalAnomalyDegenerate

namespace InfoGeometry

namespace Canonical.ConformalUnification

open InfoGeometry.Canonical.KKTCore

section CanopyAssembly

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Canopy assembly package for the conformal anomaly lane.
The package carries the KKT wing hypotheses required to discharge the operator
owner surface.
-/
def ConformalCanopyPackage
    (CI : ConformalInference E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E) : Prop :=
  IsGOne X CI.A ∧
    IsGNegOne X CI.A_MP ∧
      IsGNegOne X CI.A_D

/--
Operator-owner canopy surface: the obstruction operator is discharged as a
grade-zero block object from the KKT wings.
-/
theorem canopy_obstructionOperatorOwner
    {CI : ConformalInference E}
    {X : InfoGeometry.Quantum.RealSplitCl11Action E}
    (P : ConformalCanopyPackage (E := E) CI X) :
    ConformalInference.ObstructionOperatorOwner (CI := CI) X := by
  exact CI.obstructionOperatorOwner_of_kkt_wings
    (X := X) P.1 P.2.1 P.2.2

/--
Scalar-readout canopy surface: the operator owner projects to the canonical
readout package.
-/
theorem canopy_obstructionScalarReadout
    {CI : ConformalInference E}
    {X : InfoGeometry.Quantum.RealSplitCl11Action E}
    (P : ConformalCanopyPackage (E := E) CI X) :
    (‖CI.projectorObstruction‖₊ = CI.obstructionScale ∧ CI.obstructionScale = ‖CI.projectorObstruction‖₊ ∧ CI.chiralScale = CI.obstructionScale ∧ CI.epsilon = CI.obstructionScale ∧ CI.unitOfAction = CI.obstructionScale ∧ CI.unitOfAction = ‖CI.projectorObstruction‖₊) := by
  have _ := canopy_obstructionOperatorOwner (E := E) (CI := CI) (X := X) P
  exact CI.obstructionScalarReadout

/--
Combined canopy closure for the conformal lane:
operator-owner and scalar-readout branches are both present.
-/
theorem canopy_operator_and_scalar
    {CI : ConformalInference E}
    {X : InfoGeometry.Quantum.RealSplitCl11Action E}
    (P : ConformalCanopyPackage (E := E) CI X) :
    ConformalInference.ObstructionOperatorOwner (CI := CI) X ∧
      (‖CI.projectorObstruction‖₊ = CI.obstructionScale ∧ CI.obstructionScale = ‖CI.projectorObstruction‖₊ ∧ CI.chiralScale = CI.obstructionScale ∧ CI.epsilon = CI.obstructionScale ∧ CI.unitOfAction = CI.obstructionScale ∧ CI.unitOfAction = ‖CI.projectorObstruction‖₊) := by
  refine ⟨?_, ?_⟩
  · exact canopy_obstructionOperatorOwner (E := E) (CI := CI) (X := X) P
  · exact canopy_obstructionScalarReadout (E := E) (CI := CI) (X := X) P

end CanopyAssembly

end Canonical.ConformalUnification

end InfoGeometry
