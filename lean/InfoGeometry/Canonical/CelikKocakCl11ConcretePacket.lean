import InfoGeometry.Canonical.CelikKocakCantorOperators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
import InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge
import InfoGeometry.Canonical.CelikKocakPaperFormalism

/-!
# InfoGeometry.Canonical.CelikKocakCl11ConcretePacket

Concrete finite owner packet for the `n = 1` Çelik--Koçak source lane.

This file records only concrete theorem-backed source facts already exported by
existing owner modules:

* the canonical finite tilt/switch system at depth `1`;
* the concrete `Cl(1,1)` Pauli matrix bridge at `n = 1`;
* the explicit generator readback `ψ₀ = Eplus`, `ψ₁ = J1`.

This file does not claim:

* a doubled real/Hestenes realization;
* a Bogoliubov construction;
* a Cantor-boundary limit;
* or a charge/Hestenes concrete instance.

It is the smallest truthful concrete source packet that a later bridge can
specialize against.
-/

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.CelikKocakCantorOperators
open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
open InfoGeometry.Clifford.Cl11Matrix

/--
Concrete `n = 1` Çelik--Koçak owner packet.

This bundles the already-exported finite tilt/switch source and the already-
exported `Cl(1,1)` matrix bridge without asserting any new identification
between them.
-/
@[rep_depth operator]
structure CelikKocakCl11ConcretePacket where
  tiltSwitch : CelikKocakCantorOperators.FunctionSpace.TiltSwitchSystem (n := 1)
  pauliBridge : CantorTiltSwitchCliffordBridge.FiniteCantorPauliBridge 1 Mat2

namespace CelikKocakCl11ConcretePacket

/-- The canonical theorem-backed finite tilt/switch system at depth `1`. -/
@[rep_depth operator]
def canonical : CelikKocakCl11ConcretePacket where
  tiltSwitch := CelikKocakCantorOperators.FunctionSpace.canonicalTiltSwitchSystem (n := 1)
  pauliBridge := InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge

/-- In the canonical base case, the first Clifford generator is `Eplus`. -/
@[rep_depth operator]
theorem canonical_psiGamma_zero :
    canonical.pauliBridge.psiGamma ⟨0, by decide⟩ = Eplus :=
  InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge_psiGamma_zero

/-- In the canonical base case, the second Clifford generator is `J1`. -/
@[rep_depth operator]
theorem canonical_psiGamma_one :
    canonical.pauliBridge.psiGamma ⟨1, by decide⟩ = J1 :=
  InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge_psiGamma_one

/-- The first canonical generator squares to one. -/
@[rep_depth operator]
theorem canonical_psiGamma_zero_sq :
    canonical.pauliBridge.psiGamma ⟨0, by decide⟩ *
      canonical.pauliBridge.psiGamma ⟨0, by decide⟩ = 1 := by
  exact canonical.pauliBridge.clifford_sq ⟨0, by decide⟩

/-- The second canonical generator squares to one. -/
@[rep_depth operator]
theorem canonical_psiGamma_one_sq :
    canonical.pauliBridge.psiGamma ⟨1, by decide⟩ *
      canonical.pauliBridge.psiGamma ⟨1, by decide⟩ = 1 := by
  exact canonical.pauliBridge.clifford_sq ⟨1, by decide⟩

/-- The two canonical generators anticommute. -/
@[rep_depth operator]
theorem canonical_psiGamma_anticomm :
    canonical.pauliBridge.psiGamma ⟨0, by decide⟩ * canonical.pauliBridge.psiGamma ⟨1, by decide⟩ +
      canonical.pauliBridge.psiGamma ⟨1, by decide⟩ * canonical.pauliBridge.psiGamma ⟨0, by decide⟩ = 0 := by
  exact canonical.pauliBridge.gamma_anticomm (i := ⟨0, by decide⟩) (j := ⟨1, by decide⟩) (by decide)

/-- The canonical finite tilt at slot `0` squares to one. -/
@[rep_depth operator]
theorem canonical_tilt_sq :
    canonical.tiltSwitch.T ⟨0, by decide⟩ * canonical.tiltSwitch.T ⟨0, by decide⟩ = 1 := by
  exact canonical.tiltSwitch.T_sq ⟨0, by decide⟩

/-- The canonical finite switch at slot `0` squares to one. -/
@[rep_depth operator]
theorem canonical_switch_sq :
    canonical.tiltSwitch.S ⟨0, by decide⟩ * canonical.tiltSwitch.S ⟨0, by decide⟩ = 1 := by
  exact canonical.tiltSwitch.S_sq ⟨0, by decide⟩

/-- The canonical finite tilt/switch pair anticommutes at slot `0`. -/
@[rep_depth operator]
theorem canonical_tilt_switch_anticomm :
    canonical.tiltSwitch.T ⟨0, by decide⟩ * canonical.tiltSwitch.S ⟨0, by decide⟩ =
      - (canonical.tiltSwitch.S ⟨0, by decide⟩ * canonical.tiltSwitch.T ⟨0, by decide⟩) := by
  exact canonical.tiltSwitch.T_S_anticomm ⟨0, by decide⟩

end CelikKocakCl11ConcretePacket

end InfoGeometry.Canonical
