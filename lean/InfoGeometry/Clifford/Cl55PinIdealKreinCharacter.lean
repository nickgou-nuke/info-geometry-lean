import InfoGeometry.Canonical.Cl55SuperTKKKreinRepresentation
import InfoGeometry.Clifford.Cl55SouriauKreinTraceBridge
import InfoGeometry.Clifford.Clifford55
import Mathlib.LinearAlgebra.Trace

/-!
# Pin action and character readout on the Cl(5,5) vacuum ideal

The native Pin subgroup acts on the already-constructed vacuum ideal by the
owner's Clifford left action.  The vacuum ideal is linearly equivalent to the
doubled Krein carrier, so this file transports that group representation and
its trace character to the Krein presentation.  This is a finite-dimensional
character readout; it does not assert that `Pin55` is finite, average over it,
or construct a Souriau exponential partition function.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55PinIdealKreinCharacter

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.Cl55SuperTKKKreinRepresentation
open InfoGeometry.Clifford.Cl55SuperTKK

/-- The Pin(5,5) action on the Cl(5,5) vacuum ideal, by left multiplication. -/
def pinIdealAction (g : Pin55) : EndV :=
  cl55VacuumIdealAction (pinToUnits g : Cl55)

@[simp] theorem pinIdealAction_apply (g : Pin55) (x : V) :
    pinIdealAction g x = cl55VacuumIdealAction (pinToUnits g : Cl55) x := rfl

/-- The ideal action respects Pin multiplication. -/
theorem pinIdealAction_mul (g h : Pin55) :
    pinIdealAction (g * h) = pinIdealAction g * pinIdealAction h := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (pinToUnits (g * h) : Cl55) * x.1 =
    (pinToUnits g : Cl55) * ((pinToUnits h : Cl55) * x.1)
  rw [map_mul pinToUnits g h]
  simp only [Units.val_mul]
  exact Semigroup.mul_assoc (pinToUnits g : Cl55) (pinToUnits h : Cl55) x.1

/-- The identity Pin element acts as the identity on the vacuum ideal. -/
@[simp] theorem pinIdealAction_one :
    pinIdealAction (1 : Pin55) = (1 : EndV) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (pinToUnits (1 : Pin55) : Cl55) * x.1 = x.1
  simp [pinToUnits]

/-- The Pin action transported to the doubled Krein carrier. -/
def pinKreinAction (g : Pin55) : Module.End ℝ KreinDouble :=
  (idealKreinEquiv.conjAlgEquiv ℝ) (pinIdealAction g)

/-- Pin multiplication is respected after transport to the Krein carrier. -/
theorem pinKreinAction_mul (g h : Pin55) :
    pinKreinAction (g * h) = pinKreinAction g * pinKreinAction h := by
  rw [pinKreinAction, pinKreinAction, pinKreinAction, pinIdealAction_mul]
  exact map_mul (idealKreinEquiv.conjAlgEquiv ℝ) _ _

@[simp] theorem pinKreinAction_one :
    pinKreinAction (1 : Pin55) = (1 : Module.End ℝ KreinDouble) := by
  rw [pinKreinAction, pinIdealAction_one]
  exact map_one (idealKreinEquiv.conjAlgEquiv ℝ)

/-- The finite-dimensional trace character of the Pin action on the vacuum
ideal. -/
def pinIdealCharacter (g : Pin55) : ℝ :=
  LinearMap.trace ℝ V (pinIdealAction g)

/-- The same Pin character is obtained from the transported doubled-Krein
operator. -/
theorem pinIdealCharacter_eq_kreinTrace (g : Pin55) :
    pinIdealCharacter g =
      LinearMap.trace ℝ KreinDouble (pinKreinAction g) := by
  symm
  exact InfoGeometry.Clifford.Cl55SouriauKreinTraceBridge.idealTrace_eq_kreinTrace
    (pinIdealAction g)

end InfoGeometry.Clifford.Cl55PinIdealKreinCharacter

end
