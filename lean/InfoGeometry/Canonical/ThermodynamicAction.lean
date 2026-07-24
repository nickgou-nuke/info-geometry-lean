import InfoGeometry.Canonical.RelationalInformationCore
import InfoGeometry.Canonical.ThermodynamicGenerator
import InfoGeometry.Meta.Vacuity

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ThermodynamicAction

Expository thermodynamic-action aliases on the relational datum surface.

This file does not introduce a new thermodynamic owner layer. It only records
already-owned identifications:

- the operatorial KL/action surface is the relational functional shift;
- the Fisher metric surface is the comparison-state second variation; and
- operatorial Killing/equilibrium language is already carried by
  `ThermodynamicGenerator`.
-/

namespace InfoGeometry.Canonical.ThermodynamicAction

open InfoGeometry.Canonical.RelationalInformationCore

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The operatorial Kullback-Leibler/action surface on a relational datum.

This is exactly the already-owned relative functional shift from reference to
comparison state.
-/
@[rep_depth transport]
noncomputable def operatorialKLDivergence
    (R : RelationalInformationDatum (E := E)) : ℝ :=
  functionalShift R

/--
The Fisher metric surface on a relational datum.

This is exactly the already-owned comparison-state second-variation form.
-/
@[rep_depth transport]
noncomputable def fisherInformationMetric
    (R : RelationalInformationDatum (E := E))
    (X Y : PerturbationChannel E) : ℝ :=
  comparisonGeneratorMetric R X Y

attribute [expository]
  operatorialKLDivergence
  fisherInformationMetric

end Core

end InfoGeometry.Canonical.ThermodynamicAction
