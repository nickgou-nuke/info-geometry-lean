import Mathlib.Data.ZMod.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.NoncommutativeModularSignum

namespace InfoGeometry.Canonical.WittenParityAnomalyBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.NoncommutativeModularSignum

-- Edward Witten, 2016: The "Parity" Anomaly On An Unorientable Manifold
-- The Pin+ structure corresponds to the complexified Hestenes-Krein structure where T^2 = -1
-- The unorientable swap is identified with the real modular swap J

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- The Pin+ structure is realized when the time-reversal/parity operator squares to -1.
In the real doubled space, the complex structure `complex_i` serves this role. -/
@[rep_depth krein]
def IsPinPlus (T : EndH) : Prop :=
  T * T = -(1 : EndH)

/-- The Pin- structure is realized when the operator squares to +1.
The real modular swap `J` serves this role. -/
@[rep_depth krein]
def IsPinMinus (T : EndH) : Prop :=
  T * T = (1 : EndH)

set_option linter.unusedSectionVars false

/-- The real modular swap generates a Pin- structure. -/
@[rep_depth krein]
theorem modular_j_is_pin_minus [CompleteSpace E] : 
    IsPinMinus (modular_j (E := E)) := by
  dsimp [IsPinMinus]
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [modular_j]

/-- The emergent complex structure generates a Pin+ structure. -/
@[rep_depth krein]
theorem complex_i_is_pin_plus [CompleteSpace E] : 
    IsPinPlus (complex_i (E := E)) := by
  dsimp [IsPinPlus]
  exact complex_i_sq (E := E)

/--
The Witten parity anomaly cancellation on the unorientable Klein Bottle 
requires the number of Majorana fermions `nu` to be a multiple of 16.
-/
def AnomalyFree (nu : ℕ) : Prop :=
  nu % 16 = 0

end InfoGeometry.Canonical.WittenParityAnomalyBridge
