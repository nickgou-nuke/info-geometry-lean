import InfoGeometry.Canonical.RelationalInformationCore
import InfoGeometry.Canonical.ModularHessian
import InfoGeometry.Meta.Vacuity

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.VariationalLadder

Expository variational naming surface over owned first- and second-variation
data.

This file is a compatibility shell. It keeps ladder/current vocabulary readable
without claiming new owner mathematics beyond the already maintained
relational, Hessian, and Onsager surfaces.
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

/--
Compatibility bundle collecting the current/fisher/vortex ladder.
-/
@[rep_depth transport]
structure Ladder (R : RelationalInformationDatum (E := E)) where
  current : PerturbationChannel E → ℝ := informationalCurrent R
  fisher : LinearMap.BilinForm ℝ (PerturbationChannel E) := fisherPart R
  vortex : LinearMap.BilinForm ℝ (PerturbationChannel E) := vortexPart R

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
