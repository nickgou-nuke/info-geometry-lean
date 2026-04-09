import InfoGeometry.Canonical.RelationalInformationCore
import InfoGeometry.Canonical.ThermodynamicGenerator

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ThermodynamicAction

Thin thermodynamic-action aliases on the relational datum surface.

This file does not introduce a new thermodynamic ontology. It only records the
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

@[rep_depth transport, simp] theorem operatorialKLDivergence_eq_functionalShift
    (R : RelationalInformationDatum (E := E)) :
    operatorialKLDivergence (E := E) R = functionalShift R := rfl

/--
The Fisher metric surface on a relational datum.

This is exactly the already-owned comparison-state second-variation form.
-/
@[rep_depth transport]
noncomputable def fisherInformationMetric
    (R : RelationalInformationDatum (E := E))
    (X Y : PerturbationChannel E) : ℝ :=
  comparisonGeneratorMetric R X Y

@[rep_depth transport, simp] theorem fisherInformationMetric_eq_comparisonGeneratorMetric
    (R : RelationalInformationDatum (E := E))
    (X Y : PerturbationChannel E) :
    fisherInformationMetric (E := E) R X Y
      =
    comparisonGeneratorMetric R X Y := rfl

end Core

end InfoGeometry.Canonical.ThermodynamicAction
