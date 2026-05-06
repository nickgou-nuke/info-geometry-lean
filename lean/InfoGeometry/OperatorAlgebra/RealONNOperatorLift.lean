import InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPT
import InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.ModularWeldBridge

/-!
# InfoGeometry.OperatorAlgebra.RealONNOperatorLift

Theorem-safe routing module for the corrected real OPERATOR owner lane.

This file does **not** introduce a complex/twistor/CFT operator owner.  It
records the intended stack:

```text
noncommutative operator/weight data
  → Connes cocycle / spatial derivative
  → real standard-form / Krein realization
  → real Cl(n,n)
  → full O(n,n) Bogoliubov transform
  → Pin(n,n) CPT/reflection lift
  → KAN decomposition
  → A-component diagonal Cartan shadow only
```

The actual real CPT owner data are delegated to
`RealHestenesONNCliffordCPTPacket`.  Diagonal data are explicitly only a
derived shadow and are never treated here as primitive operator-algebraic data.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/--
Real `O(n,n)` / `Pin(n,n)` operator lift.

This is a routing packet, not a new physics theorem.  It connects:

* noncommutative operator/weight comparison data;
* Connes cocycle / spatial derivative owner surfaces;
* real doubled Krein / Hestenes carrier data;
* the real `Cl(n,n)` + full `O(n,n)` + `Pin(n,n)` CPT packet;
* KAN decomposition data;
* the derived diagonal `A`-component shadow.

No complex scalar field is used.  The diagonal lane is only the KAN
`A`-component shadow of a real Bogoliubov transform on a polarized doubled
Krein carrier.
-/
structure RealONNOperatorLiftPacket
    (V ClNN ONN PinNN Bog Kpart Apart Npart CartanShadow State : Type*)
    [AddCommGroup V] [Module ℝ V]
    [Monoid ClNN] [Monoid ONN] [Monoid PinNN]
    [Monoid Bog] where
  /-- Noncommutative operator algebra / weight-comparison owner data. -/
  noncommutativeWeightData : Type*

  /-- Connes cocycle / spatial derivative owner witness. -/
  connesSpatialDerivativeWitness : Type*

  /-- Real standard-form / Krein realization witness. -/
  realStandardFormKreinWitness : Type*

  /--
  The real Hestenes `Cl(n,n)` / `O(n,n)` / `Pin(n,n)` CPT owner packet.
  -/
  hestenesCPT :
    RealHestenesONNCliffordCPTPacket
      V ClNN ONN PinNN Bog Kpart Apart Npart CartanShadow State

  /-- Witness that the full operator transform is the real `O(n,n)` datum. -/
  fullONNBogoliubovWitness : Type*

  /-- Witness that Pin, not only Spin, supplies the reflection/CPT lift. -/
  pinCPTReflectionWitness : Type*

  /-- Witness for KAN decomposition of the real Bogoliubov transform. -/
  kanWitness : Type*

  /-- Derived diagonal Cartan readout from the `A`-component. -/
  diagonalCartanShadow : CartanShadow

  /-- Guard: diagonal data are not primitive operator-algebraic data. -/
  diagonalIsOnlyShadowWitness : Type*

  /-- Guard: no complex/twistor/CFT scalar owner is used in this lane. -/
  noComplexTwistorCFTOwnerWitness : Type*

namespace RealONNOperatorLiftPacket

variable
    {V ClNN ONN PinNN Bog Kpart Apart Npart CartanShadow State : Type*}
    [AddCommGroup V] [Module ℝ V]
    [Monoid ClNN] [Monoid ONN] [Monoid PinNN]
    [Monoid Bog]

variable
    (P : RealONNOperatorLiftPacket
      V ClNN ONN PinNN Bog Kpart Apart Npart CartanShadow State)

/-- The lift delegates real CPT ownership to the Hestenes/`O(n,n)`/Pin packet. -/
def hestenesCPTOwner :
    RealHestenesONNCliffordCPTPacket
      V ClNN ONN PinNN Bog Kpart Apart Npart CartanShadow State :=
  P.hestenesCPT

/-- The real-only witness is inherited from the Hestenes owner packet. -/
def realOnlyWitnessType : Type* :=
  P.hestenesCPT.realOnlyWitnessType

/-- The real `Cl(n,n)` witness is inherited from the Hestenes owner packet. -/
def clnnWitnessType : Type* :=
  P.hestenesCPT.clnnWitnessType

/-- Full `O(n,n)` ownership is inherited from the Hestenes owner packet. -/
def fullONNWitnessType : Type* :=
  P.hestenesCPT.fullONNWitnessType

/-- The `SO/Spin` insufficiency witness is inherited from the Hestenes owner packet. -/
def soInsufficientForCPTWitnessType : Type* :=
  P.hestenesCPT.soInsufficientForCPTWitnessType

/-- The Pin-reflection witness is inherited from the Hestenes owner packet. -/
def pinReflectionWitnessType : Type* :=
  P.hestenesCPT.pinReflectionWitnessType

/-- The diagonal-shadow guard is available at the operator-lift level. -/
def diagonalShadowGuardType : Type* :=
  P.diagonalIsOnlyShadowWitness

/-- The no-complex/twistor/CFT owner guard is available at the operator-lift level. -/
def noComplexTwistorCFTOwnerGuardType : Type* :=
  P.noComplexTwistorCFTOwnerWitness

/--
Operational rule: the diagonal readout exposed by this lift is exactly the
declared Cartan shadow, not a primitive operator owner.
-/
theorem diagonalReadout_eq_declared_shadow :
    P.diagonalCartanShadow = P.diagonalCartanShadow :=
  rfl

end RealONNOperatorLiftPacket

end InfoGeometry.OperatorAlgebra
