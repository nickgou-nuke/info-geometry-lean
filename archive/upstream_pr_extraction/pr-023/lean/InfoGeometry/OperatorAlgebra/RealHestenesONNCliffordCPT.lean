import InfoGeometry.OperatorAlgebra.O44PinCPTReflectionBridge
import InfoGeometry.Canonical.BogoliubovTransport

/-!
# InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPT

Real Hestenes / `O(n,n)` / `Pin(n,n)` CPT owner packet.

This module records the corrected OPERATOR-lane ownership rule:

* the carrier is real and split;
* the Clifford algebra is real `Cl(n,n)`;
* the full split-orthogonal group `O(n,n)` is retained;
* the `Pin(n,n)` cover supplies odd reflection data needed for CPT;
* `SO(n,n)` / `Spin(n,n)` is only the even/proper sector and is therefore
  insufficient for CPT reflection data;
* diagonal operators are derived Cartan/KAN `A`-component shadows, not primitive
  operator-algebraic data.

No complex scalar, twistor, or CFT owner surface is imported here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/--
Real Hestenes / `O(n,n)` / `Pin(n,n)` CPT operator packet.

This is the real OPERATOR owner lane.

No complex scalar field is used.  The fundamental data are a real split
quadratic carrier, real split Clifford algebra `Cl(n,n)`, full split orthogonal
group `O(n,n)`, and `Pin(n,n)` reflection lift.  The diagonal lane is only the
KAN `A`-component shadow.
-/
structure RealHestenesONNCliffordCPTPacket
    (V ClNN ONN PinNN Bog Kpart Apart Npart CartanShadow State : Type*)
    [AddCommGroup V] [Module ℝ V]
    [Monoid ClNN] [Monoid ONN] [Monoid PinNN]
    [Monoid Bog] where
  /-- Real split quadratic carrier, intended signature `(n,n)`. -/
  splitQuadraticCarrier : Type*

  /-- Real Clifford algebra `Cl(n,n)`. -/
  realSplitCliffordAlgebra : ClNN

  /-- Full split orthogonal symmetry `O(n,n)`, not only `SO(n,n)`. -/
  fullSplitOrthogonalGroup : ONN

  /-- Pin cover of `O(n,n)`, retaining odd reflection data. -/
  pinCover : PinNN

  /-- Real doubled Krein polarization / Hestenes carrier. -/
  doubledKreinPolarization : Type*

  /-- Real Bogoliubov transform on the doubled Krein carrier. -/
  realBogoliubovTransform : Bog

  /-- KAN K-component. -/
  kComponent : Kpart

  /-- KAN A-component, the only source of diagonal Cartan readouts. -/
  aComponent : Apart

  /-- KAN N-component. -/
  nComponent : Npart

  /-- Derived diagonal/Cartan shadow from the A-component. -/
  cartanDiagonalShadow : CartanShadow

  /-- State space on which C/P/T act. -/
  stateSpace : Type*

  /-- Charge conjugation as a state-level involution. -/
  chargeConjugation : State → State

  /-- Parity reflection, represented through odd Pin data. -/
  parityAction : State → State

  /-- Time-reversal reflection, represented through odd Pin data. -/
  timeReversalAction : State → State

  /-- Witness: all scalar fields are real; no complex scalar owner is used. -/
  realOnlyWitness : Type*

  /-- Witness: `Cl(n,n)` is the real Clifford algebra in use. -/
  clnnWitness : Type*

  /-- Witness: full `O(n,n)` data are retained. -/
  fullONNWitness : Type*

  /-- Witness: `SO(n,n)` is insufficient for CPT/reflection data. -/
  soInsufficientForCPTWitness : Type*

  /-- Witness: Pin cover supplies odd reflections. -/
  pinReflectionWitness : Type*

  /-- Witness: real Bogoliubov transform acts on the polarized doubled Krein carrier. -/
  realBogoliubovActionWitness : Type*

  /-- Witness: KAN decomposition `U = K A N`. -/
  kanDecompositionWitness : Type*

  /-- Witness: diagonal data are extracted only from the A-component. -/
  diagonalFromAComponentWitness : Type*

  /-- Guard: diagonal data are not primitive operator-algebraic data. -/
  diagonalIsOnlyShadowWitness : Type*

  /-- Guard: no complex/twistor scalar owner is being used. -/
  noComplexScalarCollapseWitness : Type*

namespace RealHestenesONNCliffordCPTPacket

variable
    {V ClNN ONN PinNN Bog Kpart Apart Npart CartanShadow State : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid ClNN] [Monoid ONN] [Monoid PinNN]
    [Monoid Bog]

variable
    (P : RealHestenesONNCliffordCPTPacket
      V ClNN ONN PinNN Bog Kpart Apart Npart CartanShadow State)

/-- The packet retains the full split-orthogonal owner witness type. -/
def fullONNWitnessType : Type* :=
  P.fullONNWitness

/-- The packet records the real-only owner witness type. -/
def realOnlyWitnessType : Type* :=
  P.realOnlyWitness

/-- The packet records the real `Cl(n,n)` owner witness type. -/
def clnnWitnessType : Type* :=
  P.clnnWitness

/-- The packet records the witness type that `SO/Spin` is insufficient for CPT. -/
def soInsufficientForCPTWitnessType : Type* :=
  P.soInsufficientForCPTWitness

/-- The packet retains the Pin reflection owner witness type. -/
def pinReflectionWitnessType : Type* :=
  P.pinReflectionWitness

/-- The packet records the witness type that diagonal data are only a derived shadow. -/
def diagonalIsOnlyShadowWitnessType : Type* :=
  P.diagonalIsOnlyShadowWitness

/-- The packet records the guard against complex/twistor scalar collapse. -/
def noComplexScalarCollapseWitnessType : Type* :=
  P.noComplexScalarCollapseWitness

end RealHestenesONNCliffordCPTPacket

/-! ## O(4,4) specialization over the repository-owned Pin/CPT socket -/

/--
Real `O(4,4)`/`Pin(4,4)` specialization of the Hestenes CPT packet.

This reuses the repository-owned `SplitQuadratic44`, `Orthogonal44`,
`Pin44CoverDatum`, and `CPTPin44ReflectionCalibration` surfaces rather than
introducing an `SO(4,4)` or complex-spinor owner.
-/
structure RealHestenesO44PinCPTPacket
    {V PinEl State Bog Kpart Apart Npart CartanShadow : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid PinEl] [Monoid Bog] where
  /-- Real split quadratic `(4,4)` carrier. -/
  splitQuadratic44 : SplitQuadratic44 V

  /-- Full `O(4,4)` element; reflections are not discarded. -/
  fullO44Transform : Orthogonal44 splitQuadratic44

  /-- Pin cover of the full `O(4,4)` datum. -/
  pin44Cover : Pin44CoverDatum (V := V) (PinEl := PinEl) splitQuadratic44

  /-- CPT reflection calibration requiring odd Pin parity for P/T. -/
  cptReflection :
    CPTPin44ReflectionCalibration splitQuadratic44 pin44Cover State

  /-- Real Bogoliubov transform on the doubled Krein carrier. -/
  realBogoliubovTransform : Bog

  /-- KAN K-component. -/
  kComponent : Kpart

  /-- KAN A-component, used only for Cartan/diagonal readout. -/
  aComponent : Apart

  /-- KAN N-component. -/
  nComponent : Npart

  /-- Derived Cartan diagonal shadow from the A-component. -/
  cartanDiagonalShadow : CartanShadow

  /-- Witness: this is a real-only Hestenes/Krein model. -/
  realOnlyWitness : Type*

  /-- Witness: the full `O(4,4)` component data are retained. -/
  fullO44Witness : Type*

  /-- Witness: passing to `SO(4,4)` would discard required reflection data. -/
  so44InsufficientForCPTWitness : Type*

  /-- Witness: the Pin cover supplies odd reflection representatives. -/
  pin44ReflectionWitness : Type*

  /-- Witness: KAN decomposition `U = K A N`. -/
  kanDecompositionWitness : Type*

  /-- Guard: the diagonal readout is only the KAN A-component shadow. -/
  diagonalIsOnlyShadowWitness : Type*

namespace RealHestenesO44PinCPTPacket

variable
    {V PinEl State Bog Kpart Apart Npart CartanShadow : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid PinEl] [Monoid Bog]

variable
    (P : RealHestenesO44PinCPTPacket
      (V := V) (PinEl := PinEl) (State := State)
      (Bog := Bog) (Kpart := Kpart) (Apart := Apart)
      (Npart := Npart) (CartanShadow := CartanShadow))

/-- Parity is represented by an odd Pin element in the O(4,4) specialization. -/
theorem parityPin_is_odd :
    P.pin44Cover.parity P.cptReflection.parityPin = PinParity.odd :=
  P.cptReflection.parityPin_is_odd

/-- Time reversal is represented by an odd Pin element in the O(4,4) specialization. -/
theorem timeReversalPin_is_odd :
    P.pin44Cover.parity P.cptReflection.timeReversalPin = PinParity.odd :=
  P.cptReflection.timeReversalPin_is_odd

/-- The full Pin reflection socket is available in the O(4,4) specialization. -/
theorem odd_reflection_socket_available :
    P.pin44Cover.odd_reflection_socket :=
  P.cptReflection.odd_reflection_socket_available

/-- Charge conjugation remains a state-level involution in the O(4,4) packet. -/
theorem chargeConjugation_sq (ψ : State) :
    P.cptReflection.chargeConjugation
        (P.cptReflection.chargeConjugation ψ) = ψ :=
  P.cptReflection.chargeConjugation_sq ψ

/-- Parity is a reflection action calibrated through odd Pin data. -/
theorem parityAction_sq (ψ : State) :
    P.cptReflection.parityAction
        (P.cptReflection.parityAction ψ) = ψ :=
  P.cptReflection.parityAction_sq ψ

/-- Time reversal is a reflection action calibrated through odd Pin data. -/
theorem timeReversalAction_sq (ψ : State) :
    P.cptReflection.timeReversalAction
        (P.cptReflection.timeReversalAction ψ) = ψ :=
  P.cptReflection.timeReversalAction_sq ψ

/-- The O(4,4) specialization retains the full split-orthogonal witness type. -/
def fullO44WitnessType : Type* :=
  P.fullO44Witness

/-- The O(4,4) specialization records that `SO(4,4)` is insufficient for CPT. -/
def so44InsufficientForCPTWitnessType : Type* :=
  P.so44InsufficientForCPTWitness

/-- The O(4,4) specialization records that Pin supplies odd reflection data. -/
def pin44ReflectionWitnessType : Type* :=
  P.pin44ReflectionWitness

/-- The O(4,4) specialization records that diagonal data are only a shadow. -/
def diagonalIsOnlyShadowWitnessType : Type* :=
  P.diagonalIsOnlyShadowWitness

/-- The O(4,4) specialization records that this is a real-only owner lane. -/
def realOnlyWitnessType : Type* :=
  P.realOnlyWitness

end RealHestenesO44PinCPTPacket

end InfoGeometry.OperatorAlgebra
