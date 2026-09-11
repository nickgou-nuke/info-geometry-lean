import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitClifford55ExteriorParity
import InfoGeometry.Clifford.Cl55RealSplitPin
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.Cl55PinPlusMinusNative
import InfoGeometry.Topology.Pin55TopologicalGroups
import InfoGeometry.Twistor.Pin55ExteriorSpinorNativeAction
import InfoGeometry.Twistor.Pin55ProjectivePureSpinorGrassmannianEquivariance

/-!
# Pure pinor vacuum conventions for the split `(5,5)` carrier

The annihilator condition is a property of a vector in a Clifford module; it
is not a property of a Pin-group element.  Accordingly, this file keeps the
existing `IsPureSpinor` predicate and gives it the precise Pinor reading:
the vacuum is a pure Clifford-module vector on which a Pin action may act.

The two signs are kept as distinct Clifford presentations.  The plus vacuum
uses the repository's full real split Pin subgroup for `Q55`.  The minus
vacuum below uses the transported subgroup of units for the opposite form
`-Q55`; it is transported through the explicit quadratic isometry rather than
silently identified with the native `pinGroup` submonoid.
-/

noncomputable section

namespace InfoGeometry.Twistor.Pin55PurePinorVacuum

open CliffordAlgebra
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.Clifford55PinPlusMinusNative
open InfoGeometry.Topology.Pin55TopologicalGroups
open InfoGeometry.Twistor.Pin55ExteriorSpinorNativeAction
open InfoGeometry.Twistor.Pin55ProjectivePureSpinorGrassmannianEquivariance

/-! ## The pure-pinor vacuum and the sheet involution -/

/-- The native exterior-grade involution is the sheet twist on pinors. -/
noncomputable def pinorSheetTwist : Spinor →ₗ[ℝ] Spinor :=
  InfoGeometry.Clifford.SplitClifford55ExteriorParity.gradeLinear

@[simp] theorem pinorSheetTwist_apply (ψ : Spinor) :
    pinorSheetTwist ψ =
      InfoGeometry.Clifford.SplitClifford55ExteriorParity.gradeInvolution ψ := rfl

theorem pinorSheetTwist_involutive (ψ : Spinor) :
    pinorSheetTwist (pinorSheetTwist ψ) = ψ := by
  exact InfoGeometry.Clifford.SplitClifford55ExteriorParity.gradeInvolution_involutive ψ

@[simp] theorem pinorSheetTwist_vacuum :
    pinorSheetTwist (1 : Spinor) = 1 := by
  simp [pinorSheetTwist,
    InfoGeometry.Clifford.SplitClifford55ExteriorParity.gradeLinear]

/-! ## The carrier-level pure pinor vacuum -/

def purePinorVacuum : Spinor := 1

theorem purePinorVacuum_isPure : IsPureSpinor purePinorVacuum := by
  exact vacuum_isPureSpinor

def PurePinorVacuum : Set Spinor := {ψ | IsPureSpinor ψ}

theorem purePinorVacuum_mem : purePinorVacuum ∈ PurePinorVacuum :=
  purePinorVacuum_isPure

/-! ## The plus Pin action preserves the vacuum locus -/

theorem realPin55_maps_purePinorVacuum
    (g : RealPin55) {ψ : Spinor} (hψ : ψ ∈ PurePinorVacuum) :
    realPin55ExteriorSpinorLinearEquiv g ψ ∈ PurePinorVacuum := by
  exact realPin55_isPureSpinor g hψ

theorem realPin55_vacuum_readout
    (g : RealPin55) :
    realPin55ExteriorSpinorLinearEquiv g purePinorVacuum ∈ PurePinorVacuum := by
  exact realPin55_maps_purePinorVacuum g purePinorVacuum_mem

/-! ## The minus Pin carrier remains separate from the plus module -/

abbrev TransportedPinMinus55 :=
  InfoGeometry.Topology.Pin55TopologicalGroups.PinMinus55

def pinMinus55Vacuum : TransportedPinMinus55 := 1

@[simp] theorem pinMinus55Vacuum_coe :
    ((pinMinus55Vacuum :
        InfoGeometry.Topology.Pin55TopologicalGroups.Cl55Oppositeˣ) :
      InfoGeometry.Topology.Pin55TopologicalGroups.Cl55Opposite) = 1 := rfl

theorem pinMinus55Vacuum_property :
    ((pinMinus55Vacuum :
        InfoGeometry.Topology.Pin55TopologicalGroups.PinMinus55) :
      InfoGeometry.Topology.Pin55TopologicalGroups.Cl55Oppositeˣ) ∈
      InfoGeometry.Topology.Pin55TopologicalGroups.PinMinus55 :=
  pinMinus55Vacuum.property

/-!
A module action for `PinMinus55` on the pure-pinor carrier requires an
explicit representation of `CliffordAlgebra (-Q55)` on that carrier.  The
definition above therefore records the opposite-sign vacuum unit without
silently identifying it with the plus-sign exterior representation.
-/

end InfoGeometry.Twistor.Pin55PurePinorVacuum
