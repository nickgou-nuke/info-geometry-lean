import InfoGeometry.Canonical.RelationalInformationCore
import InfoGeometry.Canonical.ThermodynamicAction
import InfoGeometry.Meta.Vacuity

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ModularHessian

Expository modular-Hessian aliases on the relational datum surface.

This file keeps the older naming surface, but the owned mathematical content is
already elsewhere:

- the modular Hessian is the comparison-state second variation;
- its Fisher side is the comparison-state metric form; and
- its vortex/phase side is the `(Jε)`-twisted comparison-state phase form.
-/

namespace InfoGeometry.Canonical.ModularHessian

open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.ThermodynamicAction

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The modular Hessian: the owned comparison-state second-variation form.
-/
@[rep_depth transport]
noncomputable def modularHessian
    (R : RelationalInformationDatum (E := E)) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  comparisonGeneratorMetric R

/--
The Fisher side of the modular Hessian.
-/
@[rep_depth transport]
noncomputable def fisherPart
    (R : RelationalInformationDatum (E := E)) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  comparisonGeneratorMetric R

/--
The phase/vortex side of the modular Hessian.
-/
@[rep_depth transport]
noncomputable def vortexPart
    (R : RelationalInformationDatum (E := E)) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  comparisonGeneratorPhase R

/--
Reference-gauge fixing on the relational datum surface is zero functional shift.
-/
@[rep_depth transport]
def IsReferenceGaugeFixed
    (R : RelationalInformationDatum (E := E)) : Prop :=
  operatorialKLDivergence (E := E) R = 0

attribute [expository]
  modularHessian
  fisherPart
  vortexPart
  IsReferenceGaugeFixed

end Core

end InfoGeometry.Canonical.ModularHessian
