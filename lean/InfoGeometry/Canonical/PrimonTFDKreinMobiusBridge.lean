import Mathlib
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
  realify to a Krein polarization after a witness is supplied;
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
  beta_gt_one : Prop
  Hamiltonian : Type*
  partitionFunction : ℝ
  zetaValue : ℝ
  partition_eq_zeta : partitionFunction = zetaValue
  purifiedVector : Type*
  purifiedVectorWitness : Type*
  modularOperator : Type*
  liouvillean : Type*
  typeI_modular_law : Prop
  typeI_modular_certificate : typeI_modular_law

namespace BosonicPrimonTFDModel

/-- Re-export of the trace/Hilbert zeta partition calibration. -/
theorem partition_eq_zeta_theorem (T : BosonicPrimonTFDModel) :
    T.partitionFunction = T.zetaValue :=
  T.partition_eq_zeta

/-- Re-export of the supplied finite/type-I modular law. -/
theorem typeI_modular (T : BosonicPrimonTFDModel) :
    T.typeI_modular_law :=
  T.typeI_modular_certificate

end BosonicPrimonTFDModel

/-! ## 2. Square-free Möbius/Krein sector -/

/--
Full-carrier Möbius readout guard.

On the full integer carrier, Möbius is a partial parity/supertrace weight, not
a fundamental symmetry.  The law `Γ_μ² = P_sf` is stored as witness data.
-/
structure FullMobiusPartialParity where
  FullState : Type*
  GammaMu : Type*
  squareFreeProjection : Type*
  gamma_sq_eq_squarefree_projection_law : Prop
  gamma_sq_eq_squarefree_projection_certificate :
    gamma_sq_eq_squarefree_projection_law
  not_global_fundamental_symmetry_guard : Type*

namespace FullMobiusPartialParity

/-- Re-export of the supplied `μ² = P_sf` law. -/
theorem gamma_sq_eq_squarefree_projection
    (M : FullMobiusPartialParity) :
    M.gamma_sq_eq_squarefree_projection_law :=
  M.gamma_sq_eq_squarefree_projection_certificate

end FullMobiusPartialParity

/--
Square-free/exterior fermionic sector with true Krein parity `Γ = (-1)^F`.

This is the sector where `Γ² = 1` is theorem-safe.
-/
structure SquarefreeMobiusKreinSector where
  SFState : Type*
  Gamma : Type*
  gamma_sq_one_law : Prop
  gamma_sq_one_certificate : gamma_sq_one_law
  gamma_self_adjoint_law : Prop
  gamma_self_adjoint_certificate : gamma_self_adjoint_law
  kreinForm : Type*
  mobius_squarefree_parity_guard : Type*
  fullCarrierPartialParity : FullMobiusPartialParity

namespace SquarefreeMobiusKreinSector

/-- Re-export of the square-free fundamental-symmetry law. -/
theorem gamma_sq_one (S : SquarefreeMobiusKreinSector) :
    S.gamma_sq_one_law :=
  S.gamma_sq_one_certificate

/-- Re-export of the supplied self-adjointness law. -/
theorem gamma_self_adjoint (S : SquarefreeMobiusKreinSector) :
    S.gamma_self_adjoint_law :=
  S.gamma_self_adjoint_certificate

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
  tomita_antilinear_law : Prop
  tomita_antilinear_certificate : tomita_antilinear_law
  realifiedJ_real_linear_law : Prop
  realifiedJ_real_linear_certificate : realifiedJ_real_linear_law
  realifiedJ_involutive_law : Prop
  realifiedJ_involutive_certificate : realifiedJ_involutive_law
  anticommutesWithComplexStructure_law : Prop
  anticommutesWithComplexStructure_certificate :
    anticommutesWithComplexStructure_law
  realifiedJ_eq_kreinSymmetry_law : Prop
  realifiedJ_eq_kreinSymmetry_certificate :
    realifiedJ_eq_kreinSymmetry_law

namespace TomitaKreinRealificationWitness

/-- Re-export of anti-linearity in the complex Hilbert category. -/
theorem tomita_antilinear (W : TomitaKreinRealificationWitness) :
    W.tomita_antilinear_law :=
  W.tomita_antilinear_certificate

/-- Re-export of real-linearity after realification. -/
theorem realifiedJ_real_linear (W : TomitaKreinRealificationWitness) :
    W.realifiedJ_real_linear_law :=
  W.realifiedJ_real_linear_certificate

/-- Re-export of the realified involution law. -/
theorem realifiedJ_involutive (W : TomitaKreinRealificationWitness) :
    W.realifiedJ_involutive_law :=
  W.realifiedJ_involutive_certificate

/-- Re-export of `J I = -I J` in realified form. -/
theorem anticommutesWithComplexStructure (W : TomitaKreinRealificationWitness) :
    W.anticommutesWithComplexStructure_law :=
  W.anticommutesWithComplexStructure_certificate

/-- Re-export of the supplied identification with the Krein polarization. -/
theorem realifiedJ_eq_kreinSymmetry (W : TomitaKreinRealificationWitness) :
    W.realifiedJ_eq_kreinSymmetry_law :=
  W.realifiedJ_eq_kreinSymmetry_certificate

end TomitaKreinRealificationWitness

/--
Doubled Krein TFD sector.

`KreinJ` is a real-linear fundamental symmetry.  It is not Tomita's
antiunitary modular conjugation in the complex-linear category; the supplied
realification witness records when the realified Tomita operator is identified
with this Krein polarization.
-/
structure DoubledKreinTFDSector where
  squarefree : SquarefreeMobiusKreinSector
  DirectDoubledCarrier : Type*
  KreinJ : Type*
  kreinJ_sq_one_law : Prop
  kreinJ_sq_one_certificate : kreinJ_sq_one_law
  kreinJ_self_adjoint_law : Prop
  kreinJ_self_adjoint_certificate : kreinJ_self_adjoint_law
  Liouvillian : Type*
  liouvillian_krein_self_adjoint_law : Prop
  liouvillian_krein_self_adjoint_certificate :
    liouvillian_krein_self_adjoint_law
  evolution_krein_unitary_law : Prop
  evolution_krein_unitary_certificate : evolution_krein_unitary_law
  tomitaKreinRealification : TomitaKreinRealificationWitness

namespace DoubledKreinTFDSector

/-- Re-export of the doubled Krein fundamental-symmetry law. -/
theorem kreinJ_sq_one (D : DoubledKreinTFDSector) :
    D.kreinJ_sq_one_law :=
  D.kreinJ_sq_one_certificate

/-- Re-export of the Krein-unitary evolution law. -/
theorem evolution_krein_unitary (D : DoubledKreinTFDSector) :
    D.evolution_krein_unitary_law :=
  D.evolution_krein_unitary_certificate

/-- Re-export of the realified Tomita/Krein polarization witness. -/
theorem tomita_realifies_to_kreinSymmetry (D : DoubledKreinTFDSector) :
    D.tomitaKreinRealification.realifiedJ_eq_kreinSymmetry_law :=
  D.tomitaKreinRealification.realifiedJ_eq_kreinSymmetry_certificate

end DoubledKreinTFDSector

/-! ## 4. Type III modular socket -/

/--
Modular/Tomita socket for Type III or non-tracial versions.

No trace, density matrix, determinant, or partition function is assumed here.
-/
@[socket_debt_tag]
structure TypeIIIModularPrimonSocket (A : Type*) [Mul A] where
  modularState : InfoGeometry.Dynamics.ModularThermalState A
  standardFormData : Type*
  naturalConeData : Type*
  faithfulNormalStateOrWeight : Type*
  modularFlowReadout : Type*
  nontracialReadout : Type*
  noTraceGuard : Type*

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
  mobiusInversionWitness : Type*
  not_constant_witten_index_guard : Type*

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
only after a model supplies a translation and a certificate.
-/
structure TFDKreinSupertraceDuality where
  HilbertObservable : Type*
  KreinObservable : Type*
  tfdExpectation : HilbertObservable → ℝ
  kreinSupertrace : KreinObservable → ℝ
  translate : HilbertObservable → KreinObservable
  dualityLaw : Prop
  dualityCertificate : dualityLaw

namespace TFDKreinSupertraceDuality

/-- Re-export of the supplied TFD/Krein readout duality law. -/
theorem duality (D : TFDKreinSupertraceDuality) :
    D.dualityLaw :=
  D.dualityCertificate

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
  clock_commutation_law : Prop
  clock_commutation_certificate : clock_commutation_law
  periodicityLaw : Prop
  periodicityCertificate : periodicityLaw
  obstruction_zero_law : Prop
  obstruction_zero_certificate : obstruction_zero_law
  obstruction_vs_zeta_zero_guard : Type*

namespace HestenesKreinOrbitChannel

/-- Re-export of the supplied periodicity law. -/
theorem periodicity (O : HestenesKreinOrbitChannel) :
    O.periodicityLaw :=
  O.periodicityCertificate

/-- Re-export of the supplied winding-obstruction zero law. -/
theorem obstruction_zero (O : HestenesKreinOrbitChannel) :
    O.obstruction_zero_law :=
  O.obstruction_zero_certificate

end HestenesKreinOrbitChannel

/--
Witness-gated zeta-zero socket.

Riemann zero locations are not inferred from TFD, Krein parity, or Hestenes
winding periodicity.  They require a separate analytic/spectral witness.
-/
@[socket_debt_tag]
structure WitnessGatedZetaZeroSocket where
  spectralObject : Type*
  zetaZeroReadout : Type*
  analyticContinuationWitness : Type*
  zeroLocationLaw : Prop
  zeroLocationCertificate : zeroLocationLaw
  not_implied_by_winding_obstruction_guard : Type*

namespace WitnessGatedZetaZeroSocket

/-- Re-export of the supplied zero-location law. -/
@[bridge_target_tag]
theorem zero_location (Z : WitnessGatedZetaZeroSocket) :
    Z.zeroLocationLaw :=
  Z.zeroLocationCertificate

end WitnessGatedZetaZeroSocket

/-! ## 6. Full bridge packet -/

/--
Full bridge packet keeping the Hilbert/TFD, Type III modular, and Krein/Möbius
layers separate but compatible.
-/
structure PrimonTFDKreinMobiusBridge (A : Type*) [Mul A] where
  bosonicTFD : BosonicPrimonTFDModel
  squarefreeKrein : SquarefreeMobiusKreinSector
  doubledKrein : DoubledKreinTFDSector
  typeIIIModular : TypeIIIModularPrimonSocket A
  supertraceReadout : MobiusSupertraceReadout
  duality : TFDKreinSupertraceDuality
  orbit : HestenesKreinOrbitChannel
  zetaZeroSocket : WitnessGatedZetaZeroSocket
  tfd_modular_compatibility : Type*
  krein_mobius_compatibility : Type*

/--
Main theorem-safe bridge conclusion.

It only exports the certified TFD/Krein readout duality and the certified
Hestenes periodicity law.  It does not assert a Type III trace formula and does
not identify winding-obstruction zeros with zeta zeros.
-/
@[bridge_target_tag]
theorem tfd_krein_mobius_duality_channel
    {A : Type*} [Mul A]
    (P : PrimonTFDKreinMobiusBridge A) :
    P.duality.dualityLaw ∧ P.orbit.periodicityLaw :=
  ⟨P.duality.dualityCertificate, P.orbit.periodicityCertificate⟩

end InfoGeometry.Canonical.PrimonTFDKreinMobiusBridge
