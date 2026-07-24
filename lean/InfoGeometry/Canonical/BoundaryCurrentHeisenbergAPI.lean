import InfoGeometry.Canonical.BosonizationConstructiveCurrent

/-!
# InfoGeometry.Canonical.BoundaryCurrentHeisenbergAPI

Importable canonical boundary surface for the completed current Heisenberg law.

This file does not construct a new current algebra. It re-exports the owner
completed-current theorem from `BosonizationConstructiveCurrent` under a
boundary-facing canonical name.
-/

namespace InfoGeometry.Canonical.BoundaryCurrentHeisenbergAPI

open InfoGeometry.Canonical.BosonizationConstructiveCurrent

section CanonicalCurrent

variable {A : Type*} [Ring A]

/-- Boundary current Heisenberg law in canonical circuit form. -/
theorem boundaryCurrentHeisenberg
    (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 := by
  simpa using normalOrderedCurrent_heisenberg_from_matrixUnit C m n

end CanonicalCurrent

end InfoGeometry.Canonical.BoundaryCurrentHeisenbergAPI
