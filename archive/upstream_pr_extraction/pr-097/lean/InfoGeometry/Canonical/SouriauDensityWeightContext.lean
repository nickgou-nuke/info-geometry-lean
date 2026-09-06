import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Canonical.DensityWeightIntertwinerBridge

/-!
# InfoGeometry.Canonical.SouriauDensityWeightContext

Context bridge from finite Souriau representation weights to the operatorial
density-weight/dilation lane.

The finite weight is a representation/shadow layer.  This file does not claim
that the finite state space is the full operator theory.  It records the exact
context in which the finite number/charge component is used as the scalar
density weight for the existing doubled-carrier transport generator.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.SouriauDensityWeight

open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Canonical.DensityWeightIntertwinerBridge
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein

variable {α : Type _}
variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Context linking a finite Souriau representation weight to the doubled-carrier
density-weight transport lane.
-/
structure SouriauDensityWeightContext where
  M : SouriauMomentMap α
  T : GeometricTemperature
  state : α
  P : PotentialDatum (E := E)
  ψ : DoubledSpace E

namespace SouriauDensityWeightContext

variable (C : SouriauDensityWeightContext (α := α) (E := E))

/-- The finite representation weight selected by the context. -/
@[rep_depth thermo]
def representationWeight : SouriauWeight :=
  souriauWeightAt C.M C.state

/-- The count/charge component used as density weight on the operator lane. -/
@[rep_depth thermo]
def densityWeight : ℝ :=
  C.representationWeight.numberWeight

/-- The weighted operatorial Souriau generator induced by this context. -/
@[rep_depth thermo]
noncomputable def liftedTransportGenerator : DoubledSpace E →L[ℝ] DoubledSpace E :=
  densityWeightLiftedTransportGenerator (E := E) C.P C.ψ C.densityWeight

/-- The context density weight is the finite representation number/charge weight. -/
@[rep_depth thermo]
theorem densityWeight_eq_numberWeight :
    C.densityWeight = (souriauWeightAt C.M C.state).numberWeight :=
  rfl

/--
The lifted generator is the existing Souriau temperature vector plus the
representation number/charge weight times the internal dilation axis.
This is an untagged definitional readback; the tagged public bridge below uses
the existing density-weight theorem that already exposes the dilation axis.
-/
theorem liftedTransportGenerator_eq_souriau_add_number_weighted_dilation :
    C.liftedTransportGenerator =
      ThermodynamicGenerator.souriauTemperatureVector (E := E) C.P C.ψ
        + C.densityWeight • densityWeightPhaseAxis (E := E) :=
  rfl

/--
Equivalent dilation-axis form of the lifted generator.
-/
@[rep_depth thermo]
theorem liftedTransportGenerator_eq_souriau_add_number_weighted_dilationOperator :
    C.liftedTransportGenerator =
      ThermodynamicGenerator.souriauTemperatureVector (E := E) C.P C.ψ
        + C.densityWeight • dilationOperator (E := E) := by
  exact densityWeightLiftedTransportGenerator_eq_souriau_add_weighted_dilation
    (E := E) C.P C.ψ C.densityWeight

end SouriauDensityWeightContext

end InfoGeometry.Canonical.SouriauDensityWeight
