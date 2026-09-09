import InfoGeometry.Physics.NuclearTwoModeCARFiveGrade
import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

/-!
# Finite CAR boundary readout

The repository has two distinct ladder models: `O55Contact.boson_CCR` is the
countable bosonic model, while `NuclearTwoModeCARFiveGrade` is a four-state
finite fermionic model.  This file records the exact two-boundary consequence
for the latter without identifying the two theories.
-/

noncomputable section

namespace InfoGeometry.Physics.FiniteCARBoundaryReadout

open InfoGeometry.Physics.NuclearTwoModeCARFiveGrade
open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

/-- The finite two-boundary weak functional preserves the first-mode CAR. -/
theorem weakValue_first_mode_CAR
    (p : RegularBoundaryPair (Fin 4)) :
    weakValue p (annihilationOne * creationOne) +
        weakValue p (creationOne * annihilationOne) = 1 := by
  have h := congrArg (fun A : Op => weakValueLinear p A) CAR_one
  simpa only [map_add, weakValueLinear_apply, weakValue_one] using h

end InfoGeometry.Physics.FiniteCARBoundaryReadout
