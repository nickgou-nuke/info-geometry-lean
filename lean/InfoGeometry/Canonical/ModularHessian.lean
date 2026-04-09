import InfoGeometry.Canonical.RelationalInformationCore
import InfoGeometry.Canonical.ThermodynamicAction

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ModularHessian

Thin modular-Hessian aliases on the relational datum surface.

This file keeps the older naming surface, but the owned mathematical content is
now explicit:

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

@[rep_depth transport, simp] theorem modularHessian_eq_comparisonGeneratorMetric
    (R : RelationalInformationDatum (E := E)) :
    modularHessian (E := E) R = comparisonGeneratorMetric R := rfl

@[rep_depth transport, simp] theorem fisherPart_eq_comparisonGeneratorMetric
    (R : RelationalInformationDatum (E := E)) :
    fisherPart (E := E) R = comparisonGeneratorMetric R := rfl

@[rep_depth transport, simp] theorem vortexPart_eq_comparisonGeneratorPhase
    (R : RelationalInformationDatum (E := E)) :
    vortexPart (E := E) R = comparisonGeneratorPhase R := rfl

/--
The thermodynamic Fisher metric is exactly the modular Hessian read as a
bilinear form.
-/
@[rep_depth transport]
theorem fisher_metric_eq_symmetric_hessian
    (R : RelationalInformationDatum (E := E)) :
    fisherInformationMetric (E := E) R
      =
    fun X Y => modularHessian (E := E) R X Y := by
  rfl

end Core

end InfoGeometry.Canonical.ModularHessian
