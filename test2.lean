import InfoGeometry.Canonical.ContinuousLeftActionTopCat
import InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge

noncomputable section
namespace InfoGeometry.Canonical.ToeplitzCuntzThreeContinuousActionTopCat

open CategoryTheory
open InfoGeometry.Canonical.ContinuousLeftActionTopCat
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge

variable {R : Type*} [Ring R] [StarRing R]
variable [TopologicalSpace R] [ContinuousMul R]
variable (g : ToeplitzCuntzThreeGenerators R)

abbrev cuntzRegularAction : ContinuousLeftAction R R :=
  regularLeftAction

#check translation cuntzRegularAction (braidGenerator1 g)
