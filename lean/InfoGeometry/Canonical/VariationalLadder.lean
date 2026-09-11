import InfoGeometry.Canonical.RelationalInformationCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ModularHessian
import InfoGeometry.Meta.Vacuity

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.VariationalLadder

Direct readout carrier over the owned first- and second-variation data.

The ladder is represented by a product of its three actual readouts; no
additional proof or compatibility field is introduced here.
-/

namespace InfoGeometry.Canonical.VariationalLadder

open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.ModularHessian
variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The first-variation current on a relational datum.
-/
@[rep_depth transport]
noncomputable def informationalCurrent
    (R : RelationalInformationDatum (E := E))
    (X : PerturbationChannel E) : ℝ :=
  R.firstVariation R.comparisonState X

/-! The three readouts are carried directly as a product. -/
@[rep_depth transport]
abbrev Ladder (R : RelationalInformationDatum (E := E)) :=
  (PerturbationChannel E → ℝ) ×
    LinearMap.BilinForm ℝ (PerturbationChannel E) ×
      LinearMap.BilinForm ℝ (PerturbationChannel E)

namespace Ladder

variable {R : RelationalInformationDatum (E := E)}

@[rep_depth transport]
abbrev current (L : Ladder R) : PerturbationChannel E → ℝ := L.1

@[rep_depth transport]
abbrev fisher (L : Ladder R) : LinearMap.BilinForm ℝ (PerturbationChannel E) := L.2.1

@[rep_depth transport]
abbrev vortex (L : Ladder R) : LinearMap.BilinForm ℝ (PerturbationChannel E) := L.2.2

@[rep_depth transport]
def mk
    (current : PerturbationChannel E → ℝ)
    (fisher vortex : LinearMap.BilinForm ℝ (PerturbationChannel E)) : Ladder R :=
  (current, fisher, vortex)

@[rep_depth transport]
noncomputable def canonical (R : RelationalInformationDatum (E := E)) : Ladder R :=
  mk (R := R) (informationalCurrent R) (fisherPart R) (vortexPart R)

end Ladder

/--
Compatibility predicate for vanishing first variation.
-/
@[rep_depth transport]
def IsOnsagerStationary
    (R : RelationalInformationDatum (E := E)) (X : PerturbationChannel E) : Prop :=
  informationalCurrent R X = 0

attribute [expository]
  informationalCurrent
  Ladder
  IsOnsagerStationary

end InfoGeometry.Canonical.VariationalLadder
