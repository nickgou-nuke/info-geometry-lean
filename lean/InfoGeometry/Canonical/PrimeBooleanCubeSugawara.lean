import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-!
# InfoGeometry.Canonical.PrimeBooleanCubeSugawara

Finite Sugawara/CFT readout for the prime Boolean cube.

This file stays in the finite algebraic lane:

* the canonical Boolean cube is imported from `PrimeBooleanCube`;
* a trivial affine/Virasoro bridge is installed over the real carrier;
* the Sugawara normalization is chosen so that the central charge readout is
  exactly the vertex cardinality `|S|`.

No infinite CFT, no VOA construction, and no analytic continuation are
asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeBooleanCubeSugawara

open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/--
Dedicated finite prime-lattice packet for the Sugawara readout.

The packet carries the Boolean-cube vertex together with the explicit finite
Sugawara hypotheses:

* `level = 1`
* `finiteDimension = |S|`
* `dualCoxeterNumber = 0`

Those hypotheses are not inferred from the analytic side; they are stored
directly in the finite packet.
-/
structure PrimeBooleanCubeSugawaraPacket (P : PrimeRegister) where
  vertex : Vertex P
  bridge : AffineVirasoroBridgeDatum ℝ ℝ
  level_eq_one : bridge.level = 1
  finiteDimension_eq_card : bridge.finiteDimension = (vertex.val.card : ℝ)
  dualCoxeterNumber_eq_zero : bridge.dualCoxeterNumber = 0
  centralCharge_eq_card : bridge.centralCharge = (vertex.val.card : ℝ)

namespace PrimeBooleanCubeSugawaraPacket

variable {P : PrimeRegister}

/-- The finite Sugawara central charge of the packet is exactly the vertex cardinality. -/
theorem centralCharge_eq_card_theorem (B : PrimeBooleanCubeSugawaraPacket P) :
    B.bridge.centralCharge = (B.vertex.val.card : ℝ) := by
  exact B.centralCharge_eq_card

end PrimeBooleanCubeSugawaraPacket

/-- Trivial affine-current datum used only to keep the finite readout kernel-checkable. -/
-- DEBT_ID: PBCS_TRIVIAL_AFFINE
-- DEBT_KIND: ZERO_DATUM
-- ZERO_DATUM: Trivial placeholder for finite Boolean cube readout
def trivialAffineCurrentDatum : AffineCurrentDatum ℝ ℝ where
  Current := fun _ _ => 0
  kCentral := 0
  killingForm := fun _ _ => 0

/-- Trivial Virasoro datum used only to keep the finite readout kernel-checkable. -/
-- DEBT_ID: PBCS_TRIVIAL_VIRASORO
-- DEBT_KIND: ZERO_DATUM
-- ZERO_DATUM: Trivial placeholder for finite Boolean cube readout
def trivialVirasoroDatum : VirasoroDatum ℝ where
  Lmode := fun _ => 0
  central := 0

/--
Canonical finite Sugawara packet for a Boolean-cube vertex.

The carrier is deliberately trivial on the affine/Virasoro side; the
Sugawara calibration is used only as a finite readout that returns the
vertex cardinality.
-/
def booleanCubeSugawaraPacket
    (P : PrimeRegister) (v : Vertex P) :
    PrimeBooleanCubeSugawaraPacket P where
  vertex := v
  bridge :=
    { affine := trivialAffineCurrentDatum
      virasoro := trivialVirasoroDatum
      centralCharge := v.val.card
      level := 1
      finiteDimension := v.val.card
      dualCoxeterNumber := 0 }
  level_eq_one := rfl
  finiteDimension_eq_card := rfl
  dualCoxeterNumber_eq_zero := rfl
  centralCharge_eq_card := rfl

/-- The Boolean-cube Sugawara readout is exactly the vertex cardinality. -/
theorem booleanCubeSugawaraPacket_centralCharge_eq_card
    (P : PrimeRegister) (v : Vertex P) :
    (booleanCubeSugawaraPacket P v).bridge.centralCharge = v.val.card := by
  exact PrimeBooleanCubeSugawaraPacket.centralCharge_eq_card_theorem (booleanCubeSugawaraPacket P v)

/-- The Sugawara calibration of the Boolean-cube packet is kernel-checked. -/
theorem booleanCubeSugawaraPacket_centralCharge_eq_sugawara
    (P : PrimeRegister) (v : Vertex P) :
    (booleanCubeSugawaraPacket P v).bridge.centralCharge =
      (booleanCubeSugawaraPacket P v).bridge.level *
        (booleanCubeSugawaraPacket P v).bridge.finiteDimension /
          ((booleanCubeSugawaraPacket P v).bridge.level +
            (booleanCubeSugawaraPacket P v).bridge.dualCoxeterNumber) := by
  simp [booleanCubeSugawaraPacket]

end InfoGeometry.Canonical.PrimeBooleanCubeSugawara
