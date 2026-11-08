import InfoGeometry.Twistor.Pin55PurePinorVacuum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge
import InfoGeometry.Clifford.Cl55PinPlusMinusNative

/-!
# The transported `Pin⁻(5,5)` carrier

The opposite quadratic presentation is transported to the repository's native
`Q55` Clifford presentation by the existing quadratic isometry.  Composing
that algebra equivalence with the existing `Q55` spinor representation gives
a genuine unit-valued representation of the opposite-sign Pin group.

This file deliberately proves only the carrier-level representation laws.  It
does not identify the transported action with the exterior pure-pinor action,
nor does it assert preservation of the pure-pinor annihilator; those require a
separate equivariance theorem for the transported module.
-/

noncomputable section

namespace InfoGeometry.Twistor.Pin55PurePinorMinusRepresentation

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Clifford55PinPlusMinusNative
open InfoGeometry.Twistor.Pin55PurePinorVacuum

abbrev PinMinus55 :=
  InfoGeometry.Twistor.Pin55PurePinorVacuum.TransportedPinMinus55
abbrev SpinorMatrix5 := InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5

/-! The Clifford representation transported from `-Q55` to `Q55`. -/
noncomputable def pinMinus55CliffordRepresentation :
    Cl55Opposite →ₐ[ℝ] SpinorMatrix5 :=
  cl55SpinorRepresentation.comp
    InfoGeometry.Clifford.Clifford55PinPlusMinusNative.cl55OppositeToQ55.toAlgHom

@[simp] theorem pinMinus55CliffordRepresentation_ι (v : V55) :
    pinMinus55CliffordRepresentation (CliffordAlgebra.ι Q55Opposite v) =
      cl55SpinorRepresentation (CliffordAlgebra.ι Q55 (swap55 v)) := by
  simp [pinMinus55CliffordRepresentation,
    InfoGeometry.Clifford.Clifford55PinPlusMinusNative.cl55OppositeToQ55_ι]

/-! The corresponding multiplicative representation on units. -/
noncomputable def pinMinus55SpinorUnitRepresentation :
    PinMinus55 →* SpinorMatrix5ˣ :=
  (Units.map pinMinus55CliffordRepresentation.toRingHom).comp
    InfoGeometry.Twistor.Pin55PurePinorVacuum.TransportedPinMinus55.subtype

@[simp] theorem pinMinus55SpinorUnitRepresentation_one :
    pinMinus55SpinorUnitRepresentation (1 : PinMinus55) = 1 := by
  simp [pinMinus55SpinorUnitRepresentation]

theorem pinMinus55SpinorUnitRepresentation_mul
    (g h : PinMinus55) :
    pinMinus55SpinorUnitRepresentation (g * h) =
      pinMinus55SpinorUnitRepresentation g *
        pinMinus55SpinorUnitRepresentation h := by
  exact map_mul pinMinus55SpinorUnitRepresentation g h

theorem pinMinus55_vacuum_unit_readout :
    pinMinus55SpinorUnitRepresentation (1 : PinMinus55) = 1 :=
  pinMinus55SpinorUnitRepresentation_one

end InfoGeometry.Twistor.Pin55PurePinorMinusRepresentation
