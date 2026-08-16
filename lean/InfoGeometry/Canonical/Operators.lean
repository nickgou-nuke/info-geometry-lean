import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.OnsagerReciprocity

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.Operators

Thin naming/export surface for the operatorial thermodynamic lane.

Boundary:

* owner/operatorial content lives in `CertifiedModularReduction`,
  `OperatorialHessianBridge`, and `OnsagerReciprocity`;
* this file only packages the already-owned scalar and probe-read projections
  under operator-thermodynamic names;
* the diagonal/scalar readouts here are shadows of the richer mixed
  noncommutative second-variation packet, not new primitive owner definitions.
-/

namespace InfoGeometry.Canonical.Operators

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Krein

section Bridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Scalar free-energy/log-readout shadow of the operatorial transport lane. -/
@[rep_depth transport]
noncomputable def operatorFreeEnergyReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  scalarLogReadout (E := E) ω X A t

/-- Symmetric operatorial Fisher/Onsager mixed readout before diagonal collapse. -/
@[rep_depth transport]
noncomputable def operatorFisherReadout
    (X Y A : EndH) : EndH :=
  operatorInformationMetricPart (E := E) X Y A

/-- Diagonal probe target: a shadow of the mixed operatorial second variation. -/
@[rep_depth transport]
noncomputable def operatorFisherDiagonal
    (X A : EndH) : EndH :=
  InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian (E := E) X A

/-- Scalar probe of the symmetric operatorial Hessian form. -/
@[rep_depth transport]
noncomputable def probedFisherReadout
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  operatorMetricHessianForm (E := E) P A X Y

/-- Onsager coefficient exported from the symmetric operatorial response lane. -/
@[rep_depth transport]
noncomputable def onsagerCoefficient
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  responseCoefficient (E := E) P X Y A

/--
Entropy-production shadow exported as the probe of the operatorial Fisher
Diagonal. This is intentionally a shadow/export theorem surface, not the owner
positivity producer.
-/
@[rep_depth transport]
noncomputable def entropyProduction
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)) (X A : EndH) : ℝ :=
  P.probe (operatorFisherDiagonal (E := E) X A)

end Bridge

end InfoGeometry.Canonical.Operators
