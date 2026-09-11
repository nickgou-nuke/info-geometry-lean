import InfoGeometry.Canonical.RelativeModularScaleShapeSplit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Abel

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.NontracialModularBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelativeModularScaleShapeSplit

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Noncommutative centering of a relative modular owner around the unit. -/
def centeredRelativeModular (R : EndH) : EndH :=
  R - (1 : EndH)

@[simp] theorem centeredRelativeModular_self :
    centeredRelativeModular (E := E) (1 : EndH) = 0 := by
  simp [centeredRelativeModular]

@[simp] theorem centeredRelativeModular_eq_zero_iff (R : EndH) :
    centeredRelativeModular (E := E) R = 0 ↔ R = (1 : EndH) := by
  unfold centeredRelativeModular
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

/--
Nontracial owner decomposition: `Δ - I` is the centered operator, and if
`Δ` admits the CP-002 split then `Δ - I` is exactly that split minus identity.
-/
theorem centeredRelativeModular_of_scaleShapeSplit
    {CIK : CertifiedInverseKernel H₂}
    {R : EndH}
    (hComm : Commute CIK.spectralProjector R) :
    centeredRelativeModular (E := E) R
      =
      (CIK.spectralComplementaryProjector * (R * CIK.spectralComplementaryProjector)
        + CIK.spectralProjector * (R * CIK.spectralProjector))
        - (1 : EndH) := by
  have hsplit :=
    relativeModular_scaleShapeSplit (E := E) (CIK := CIK) (R := R) hComm
  exact congrArg (fun T : EndH => T - (1 : EndH)) hsplit

end Core

end InfoGeometry.Canonical.NontracialModularBridge
