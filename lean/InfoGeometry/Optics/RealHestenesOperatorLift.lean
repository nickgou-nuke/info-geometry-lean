import InfoGeometry.Optics.OperatorLiftCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BilingualRealHestenesDictionary

/-!
# Real Hestenes operators on the doubled sheet carrier

This is the real specialization of the generic operator-entry carrier.  It
does not introduce a second matrix/action construction: the matrix action is
the owner in `OperatorLiftCarrier`, while the phase-axis matrix below is the
real Hestenes/Krein readout.
-/

noncomputable section

namespace InfoGeometry.Optics.RealHestenesOperatorLift

open InfoGeometry.Krein
open InfoGeometry.Canonical.BilingualRealHestenesDictionary
open InfoGeometry.Optics.OperatorLiftCarrier

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH₂" => Module.End ℝ H₂
local notation "M₂H₂" => OperatorMatrix (R := ℝ) (W := H₂)

/-- The real-linear phase axis underlying the doubled Hestenes space. -/
def phaseAxis : EndH₂ := (clockAxis (E := E)).toLinearMap

@[simp]
theorem phaseAxis_sq :
    phaseAxis (E := E) * phaseAxis (E := E) = -(1 : EndH₂) := by
  apply LinearMap.ext
  intro x
  change ((clockAxis (E := E)).comp (clockAxis (E := E))) x =
    (-(ContinuousLinearMap.id ℝ H₂)) x
  exact congrArg (fun T : H₂ →L[ℝ] H₂ => T x)
    (realPhaseAxis_sq (E := E))

/-- The diagonal phase-axis operator on two real Hestenes sheets. -/
def phaseAxisMatrix : M₂H₂ := Matrix.diagonal (fun _ : Fin 2 => phaseAxis (E := E))

@[simp]
theorem phaseAxisMatrix_apply (v : Fin 2 → H₂) (i : Fin 2) :
    matrixAction (phaseAxisMatrix (E := E)) v i = phaseAxis (E := E) (v i) := by
  fin_cases i <;> simp [phaseAxisMatrix, matrixAction_apply]

/-- The diagonal lift acts sheetwise by the real phase axis. -/
theorem phaseAxisMatrix_action_eq (v : Fin 2 → H₂) :
    matrixAction (phaseAxisMatrix (E := E)) v = fun i => phaseAxis (E := E) (v i) := by
  funext i
  exact phaseAxisMatrix_apply (E := E) v i

/-- The lifted real phase axis has the same square as the Hestenes phase axis. -/
theorem phaseAxisMatrix_sq :
    phaseAxisMatrix (E := E) * phaseAxisMatrix (E := E) =
      -(1 : M₂H₂) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseAxisMatrix, phaseAxis_sq]

end InfoGeometry.Optics.RealHestenesOperatorLift
