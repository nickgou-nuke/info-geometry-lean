import InfoGeometry.Canonical.CelikKocakCantorOperators
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

namespace CelikKocakCl11ConcretePacket

/-- The canonical theorem-backed finite tilt/switch system at depth `1`. -/
@[rep_depth operator]
def canonicalTiltSwitch :
    CelikKocakCantorOperators.FunctionSpace.TiltSwitchSystem (n := 1) :=
  CelikKocakCantorOperators.FunctionSpace.canonicalTiltSwitchSystem (n := 1)

@[rep_depth operator]
def canonicalPauliGamma : Fin 2 → Mat2 :=
  InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge

/-- In the canonical base case, the first Clifford generator is `Eplus`. -/
@[rep_depth operator]
theorem canonical_psiGamma_zero :
    canonicalPauliGamma ⟨0, by decide⟩ = Eplus :=
  rfl

/-- In the canonical base case, the second Clifford generator is `J1`. -/
@[rep_depth operator]
theorem canonical_psiGamma_one :
    canonicalPauliGamma ⟨1, by decide⟩ = J1 :=
  rfl

/-- The first canonical generator squares to one. -/
@[rep_depth operator]
theorem canonical_psiGamma_zero_sq :
    canonicalPauliGamma ⟨0, by decide⟩ *
      canonicalPauliGamma ⟨0, by decide⟩ = 1 := by
  exact InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge_sq
    ⟨0, by decide⟩

/-- The second canonical generator squares to one. -/
@[rep_depth operator]
theorem canonical_psiGamma_one_sq :
    canonicalPauliGamma ⟨1, by decide⟩ *
      canonicalPauliGamma ⟨1, by decide⟩ = 1 := by
  exact InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge_sq
    ⟨1, by decide⟩

/-- The two canonical generators anticommute. -/
@[rep_depth operator]
theorem canonical_psiGamma_anticomm :
    canonicalPauliGamma ⟨0, by decide⟩ * canonicalPauliGamma ⟨1, by decide⟩ +
      canonicalPauliGamma ⟨1, by decide⟩ * canonicalPauliGamma ⟨0, by decide⟩ = 0 := by
  unfold canonicalPauliGamma
  rw [InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge.cl11PauliBridge_anticomm
    (by decide : (⟨0, by decide⟩ : Fin 2) ≠ ⟨1, by decide⟩)]
  simp

/-- The canonical finite tilt at slot `0` squares to one. -/
@[rep_depth operator]
theorem canonical_tilt_sq :
    canonicalTiltSwitch.T ⟨0, by decide⟩ * canonicalTiltSwitch.T ⟨0, by decide⟩ = 1 := by
  exact canonicalTiltSwitch.T_sq ⟨0, by decide⟩

/-- The canonical finite switch at slot `0` squares to one. -/
@[rep_depth operator]
theorem canonical_switch_sq :
    canonicalTiltSwitch.S ⟨0, by decide⟩ * canonicalTiltSwitch.S ⟨0, by decide⟩ = 1 := by
  exact canonicalTiltSwitch.S_sq ⟨0, by decide⟩

/-- The canonical finite tilt/switch pair anticommutes at slot `0`. -/
@[rep_depth operator]
theorem canonical_tilt_switch_anticomm :
    canonicalTiltSwitch.T ⟨0, by decide⟩ * canonicalTiltSwitch.S ⟨0, by decide⟩ =
      - (canonicalTiltSwitch.S ⟨0, by decide⟩ * canonicalTiltSwitch.T ⟨0, by decide⟩) := by
  exact canonicalTiltSwitch.T_S_anticomm ⟨0, by decide⟩

end CelikKocakCl11ConcretePacket

end InfoGeometry.Canonical
