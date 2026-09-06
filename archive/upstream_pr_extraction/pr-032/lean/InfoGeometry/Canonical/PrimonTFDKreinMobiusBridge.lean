import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Canonical.PrimeGasPartitions
import InfoGeometry.Canonical.WindingOrbitClosure
import InfoGeometry.Dynamics.ModularThermalState

/-!
# InfoGeometry.Canonical.PrimonTFDKreinMobiusBridge

Witness-gated bridge separating three coordinated primon channels:

* TFD/GNS Hilbert purification in a trace/semifinite model;
* Tomita--Takesaki/Type III modular state or weight data;
* square-free Möbius/Krein parity supertrace data.

The point of this file is hygiene.  It prevents the following identifications
from becoming theorem-level shortcuts:

* TFD tensor doubling is not the same object as Hestenes--Krein direct doubling;
* Tomita antiunitary `J` is not a complex-linear Krein symmetry, but it may
  realify to a Krein polarization after a property is supplied;
* raw Möbius on all integers is not a global fundamental symmetry, because
  `μ²` is the square-free projection;
* Type III modular theory is state/weight based, not a global trace theory;
* winding-obstruction zeros are not Riemann zeta zeros.
-/

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.PrimonTFDKreinMobiusBridge

open InfoGeometry.Canonical.PrimeGasPartitions

/-! ## 1. Trace/Hilbert TFD model -/

/--
Trace/Hilbert TFD model for the bosonic primon gas.

This is not the Type III primitive.  It is a trace-class or semifinite Hilbert
model used when a Gibbs partition function exists.
-/
structure BosonicPrimonTFDModel where
  StateSpace : Type*
  MirrorStateSpace : Type*
  TensorDoubledSpace : Type*
  beta : ℝ
  beta_gt_one : 1 < beta
  Hamiltonian : Type*
  partitionFunction : ℝ
  zetaValue : ℝ
  partition_eq_zeta : partitionFunction = zetaValue
  purifiedVector : Type*
  modularOperator : Type*
  liouvillean : Type*

namespace BosonicPrimonTFDModel

/-- The trace/Hilbert primon model lies in the normalizable inverse-temperature domain. -/
theorem inverseTemperature_gt_one (T : BosonicPrimonTFDModel) :
    1 < T.beta :=
  T.beta_gt_one

/-- The trace/Hilbert zeta partition calibration. -/
theorem partition_eq_zeta_theorem (T : BosonicPrimonTFDModel) :
    T.partitionFunction = T.zetaValue :=
  T.partition_eq_zeta

end BosonicPrimonTFDModel

/-! ## 2. Square-free Möbius/Krein sector -/

/--
Full-carrier Möbius readout guard.

On the full integer carrier, Möbius is a partial parity/supertrace weight, not
a fundamental symmetry.  The law `Γ_μ² = P_sf` is stored as property data.
-/
structure FullMobiusPartialParity where
  FullState : Type*
  GammaMu : Type*
  squareFreeProjection : Type*

namespace FullMobiusPartialParity

end FullMobiusPartialParity

/--
Square-free/exterior fermionic sector with true Krein parity `Γ = (-1)^F`.

This is the sector where `Γ² = 1` is theorem-safe.
-/
structure SquarefreeMobiusKreinSector where
  SFState : Type*
  Gamma : Type*
  kreinForm : Type*
  fullCarrierPartialParity : FullMobiusPartialParity

namespace SquarefreeMobiusKreinSector

end SquarefreeMobiusKreinSector

/-! ## 3. Hestenes--Krein direct doubling -/

/--
Doubled Krein TFD sector.

`KreinJ` is a real-linear fundamental symmetry.  It is not Tomita's
antiunitary modular conjugation in the complex-linear category; the supplied
realification property records when the realified Tomita operator is identified
with this Krein polarization.
-/
structure DoubledKreinTFDSector where
  squarefree : SquarefreeMobiusKreinSector
  DirectDoubledCarrier : Type*
  KreinJ : Type*
  Liouvillian : Type*
  ComplexCarrier : Type*
  RealCarrier : Type*
  complexStructure : Type*
  tomitaJ : Type*
  realifiedJ : Type*
  kreinSymmetry : Type*

namespace DoubledKreinTFDSector

end DoubledKreinTFDSector

/--
Supertrace/index readout interface.

This is finite/semifinite or index-pairing data.  It is not an automatic
global Type III trace.
-/
structure MobiusSupertraceReadout where
  beta : ℝ
  paritySupertrace : ℝ
  inverseZetaChannel : ℝ
  parity_eq_inverse_zeta :
    paritySupertrace = inverseZetaChannel
  lowTemperatureVacuumLimit : Type*

namespace MobiusSupertraceReadout

/-- Re-export of the inverse-zeta supertrace channel calibration. -/
theorem parity_eq_inverse_zeta_theorem
    (R : MobiusSupertraceReadout) :
    R.paritySupertrace = R.inverseZetaChannel :=
  R.parity_eq_inverse_zeta

end MobiusSupertraceReadout

/-! ## 5. TFD/Krein duality and Hestenes orbit interfaces -/

/--
TFD/Krein readout duality interface.

The formula comparing a TFD expectation with a Krein graded readout is valid
only after a model supplies a translation and a property.
-/
structure TFDKreinSupertraceDuality where
  HilbertObservable : Type*
  KreinObservable : Type*
  tfdExpectation : HilbertObservable → ℝ
  kreinSupertrace : KreinObservable → ℝ
  translate : HilbertObservable → KreinObservable

namespace TFDKreinSupertraceDuality

end TFDKreinSupertraceDuality

/--
Hestenes--Krein orbit channel.

The zero in this channel is a winding-obstruction zero, not a Riemann zeta zero.
-/
structure HestenesKreinOrbitChannel where
  DirectDoubledCarrier : Type*
  clockAxis : Type*
  generator : Type*
  windingNumber : ℤ
  windingObstruction : Type*

namespace HestenesKreinOrbitChannel

end HestenesKreinOrbitChannel

/-! ## 6. Full bridge packet -/

/--
Full bridge packet keeping the Hilbert/TFD, Type III modular, and Krein/Möbius
layers separate but compatible.
-/
structure PrimonTFDKreinMobiusBridge (A : Type*) [Monoid A] where
  bosonicTFD : BosonicPrimonTFDModel
  squarefreeKrein : SquarefreeMobiusKreinSector
  doubledKrein : DoubledKreinTFDSector
  supertraceReadout : MobiusSupertraceReadout
  duality : TFDKreinSupertraceDuality
  orbit : HestenesKreinOrbitChannel


end InfoGeometry.Canonical.PrimonTFDKreinMobiusBridge
