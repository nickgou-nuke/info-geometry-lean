import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.OwnerTarget
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

namespace PrimeBooleanCubeSugawaraPacket

variable {P : PrimeRegister}

/-- The finite Sugawara central charge of the packet is exactly the vertex cardinality. -/
theorem centralCharge_eq_card (B : PrimeBooleanCubeSugawaraPacket P) :
    B.bridge.centralCharge = (B.vertex.val.card : ℝ) := by
  rw [B.bridge.centralCharge_calibrated, B.level_eq_one, B.finiteDimension_eq_card,
    B.dualCoxeterNumber_eq_zero]
  norm_num

end PrimeBooleanCubeSugawaraPacket

/-- Trivial affine-current datum used only to keep the finite readout kernel-checkable. -/
def trivialAffineCurrentDatum : AffineCurrentDatum ℝ ℝ where
  Current := fun _ _ => 0
  kCentral := 0
  kCentral_commutes := by
    intro X
    simp
  killingForm := fun _ _ => 0
  affine_bracket := by
    intro m n X Y
    simp

/-- Trivial Virasoro datum used only to keep the finite readout kernel-checkable. -/
def trivialVirasoroDatum : VirasoroDatum ℝ where
  Lmode := fun _ => 0
  central := 0
  central_commutes := by
    intro X
    simp
  virasoro_bracket := by
    intro m n
    simp

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
      virasoro_acts_on_currents := by
        intro m n X
        simp [trivialAffineCurrentDatum, trivialVirasoroDatum]
      centralCharge := v.val.card
      level := 1
      finiteDimension := v.val.card
      dualCoxeterNumber := 0
      centralCharge_eq_sugawara := by
        norm_num [sugawaraCentralCharge] }
  level_eq_one := rfl
  finiteDimension_eq_card := rfl
  dualCoxeterNumber_eq_zero := rfl

/-- The Boolean-cube Sugawara readout is exactly the vertex cardinality. -/
@[bridge_target_tag]
theorem booleanCubeSugawaraPacket_centralCharge_eq_card
    (P : PrimeRegister) (v : Vertex P) :
    (booleanCubeSugawaraPacket P v).bridge.centralCharge = v.val.card := by
  exact PrimeBooleanCubeSugawaraPacket.centralCharge_eq_card (booleanCubeSugawaraPacket P v)

/-- The Sugawara calibration of the Boolean-cube packet is kernel-checked. -/
@[bridge_target_tag]
theorem booleanCubeSugawaraPacket_centralCharge_eq_sugawara
    (P : PrimeRegister) (v : Vertex P) :
    (booleanCubeSugawaraPacket P v).bridge.centralCharge =
      (booleanCubeSugawaraPacket P v).bridge.level *
        (booleanCubeSugawaraPacket P v).bridge.finiteDimension /
          ((booleanCubeSugawaraPacket P v).bridge.level +
            (booleanCubeSugawaraPacket P v).bridge.dualCoxeterNumber) := by
  simpa using
    (AffineVirasoroBridgeDatum.centralCharge_calibrated
      (booleanCubeSugawaraPacket P v).bridge)

/-- Canonical finite conformal owner target for the Boolean cube. -/
@[owner_target_tag]
def PrimeBooleanCubeSugawaraOwnerTarget : Prop :=
  ∀ (P : PrimeRegister) (v : Vertex P),
    (booleanCubeSugawaraPacket P v).bridge.centralCharge = v.val.card

/-- The canonical finite conformal owner target is closed. -/
theorem primeBooleanCubeSugawaraOwnerTarget :
    PrimeBooleanCubeSugawaraOwnerTarget := by
  intro P v
  exact PrimeBooleanCubeSugawaraPacket.centralCharge_eq_card (booleanCubeSugawaraPacket P v)

end InfoGeometry.Canonical.PrimeBooleanCubeSugawara
