import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Canonical.PrimeGasPartitions
import InfoGeometry.Canonical.WindingOrbitClosure
import InfoGeometry.Dynamics.ModularThermalState
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget

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
Witness that a complex Tomita modular conjugation has been transported to the
real doubled/Krein category.

The intended doctrine is categorical:

* in the complex Hilbert category, Tomita `J` is antiunitary/conjugate-linear;
* after realification, it is a real-linear involutive isometry;
* anti-linearity becomes anti-commutation with the complex structure;
* a model may then identify the realified Tomita operator with a Krein
  fundamental symmetry or polarization.
-/
structure TomitaKreinRealificationWitness where
  ComplexCarrier : Type*
  RealCarrier : Type*
  complexStructure : Type*
  tomitaJ : Type*
  realifiedJ : Type*
  kreinSymmetry : Type*

namespace TomitaKreinRealificationWitness

end TomitaKreinRealificationWitness

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
  tomitaKreinRealification : TomitaKreinRealificationWitness

namespace DoubledKreinTFDSector

end DoubledKreinTFDSector

/-! ## 4. Type III modular socket -/

/--
Modular/Tomita socket for Type III or non-tracial versions.

No trace, density matrix, determinant, or partition function is assumed here.
-/
@[socket_debt_tag]
structure TypeIIIModularPrimonSocket (A : Type*) [Monoid A] where
  modularState : InfoGeometry.Dynamics.ModularThermalState A
  standardFormData : Type*
  naturalConeData : Type*
  faithfulNormalStateOrWeight : Type*
  modularFlowReadout : Type*
  nontracialReadout : Type*

/--
Supertrace/index readout socket.

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

/-! ## 5. TFD/Krein duality and Hestenes orbit sockets -/

/--
TFD/Krein readout duality socket.

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

/--
Witness-gated zeta-zero socket.

Riemann zero locations are not inferred from TFD, Krein parity, or Hestenes
winding periodicity.  They require a separate analytic/spectral property.
-/
@[socket_debt_tag]
structure WitnessGatedZetaZeroSocket where
  spectralObject : Type*
  zetaZeroReadout : Type*
  /-- Complex-valued spectral function whose zero set is being tracked. -/
  spectralFunction : ℂ → ℂ
  /-- Open domain on which the continuation agrees with the spectral function. -/
  continuationDomain : Set ℂ
  continuationDomain_open : IsOpen continuationDomain
  /-- Candidate analytic continuation. -/
  continuation : ℂ → ℂ
  continuation_eq_function :
    ∀ z, z ∈ continuationDomain → continuation z = spectralFunction z
  continuation_holomorphic : DifferentiableOn ℂ continuation continuationDomain
  /-- The tracked zero locus is defined by the supplied continuation. -/
  zeroLocation : Set ℂ
  zeroLocation_spec :
    ∀ z, z ∈ zeroLocation ↔ continuation z = 0

namespace WitnessGatedZetaZeroSocket

end WitnessGatedZetaZeroSocket

/-! ## 6. Full bridge packet -/

/--
Full bridge packet keeping the Hilbert/TFD, Type III modular, and Krein/Möbius
layers separate but compatible.
-/
structure PrimonTFDKreinMobiusBridge (A : Type*) [Monoid A] where
  bosonicTFD : BosonicPrimonTFDModel
  squarefreeKrein : SquarefreeMobiusKreinSector
  doubledKrein : DoubledKreinTFDSector
  typeIIIModular : TypeIIIModularPrimonSocket A
  supertraceReadout : MobiusSupertraceReadout
  duality : TFDKreinSupertraceDuality
  orbit : HestenesKreinOrbitChannel
  zetaZeroSocket : WitnessGatedZetaZeroSocket


end InfoGeometry.Canonical.PrimonTFDKreinMobiusBridge
