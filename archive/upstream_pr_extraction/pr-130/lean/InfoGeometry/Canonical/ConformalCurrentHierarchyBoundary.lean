import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Canonical.BosonizationConstructiveCurrent

/-!
# InfoGeometry.Canonical.ConformalCurrentHierarchyBoundary

Direct canonical boundary between the five-grade conformal inversion layer and
the current/anomaly layer.

This file does not prove that the conformal inversion generates the current
algebra.  It records the two independently owned surfaces side by side:

* the five-grade conformal inversion and its grade-zero fixed sector;
* the completed CAR-to-current Heisenberg law with its Wick/Schwinger
  correction.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConformalCurrentHierarchyBoundary

open InfoGeometry.Canonical.ConformalFiveGradeInversion

universe u

/--
Boundary packet between the five-grade conformal inversion and the current
hierarchy.
-/
abbrev ConformalCurrentBoundary
    (L : Type*) (A : Type*) [Ring A] :=
  FiveGradedConformalInversion L ×
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra A

namespace ConformalCurrentBoundary

abbrev inversion
    {L A : Type*} [Ring A]
    (B : ConformalCurrentBoundary L A) : FiveGradedConformalInversion L := B.1

abbrev rawCAR
    {L A : Type*} [Ring A]
    (B : ConformalCurrentBoundary L A) :
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra A := B.2

variable {L A : Type*} [Ring A]
variable (B : ConformalCurrentBoundary L A)

/-- The grade-zero sector survives the inversion. -/
@[simp] theorem grade_zero_survives
    {x : L}
    (hx : B.inversion.grade x = ConformalGrade.zero) :
    B.inversion.grade (B.inversion.theta x) = ConformalGrade.zero :=
  B.inversion.zero_grade_survives_setwise hx

/--
The completed current Heisenberg law is available at the boundary surface.
This is the current side of the circuit diagram; it is imported directly from
the constructive CAR-to-Wick current layer.
-/
theorem boundary_current_heisenberg
    (hK : B.rawCAR.central = 1)
    (m n : Int) :
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra.CCRBracketCompleted
      B.rawCAR hK
      (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra.normalOrderedCurrent
        B.rawCAR hK m)
      (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra.normalOrderedCurrent
        B.rawCAR hK n) =
      if m + n = 0 then
        m • InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra.completedCentral
          B.rawCAR
      else
        0 := by
  simpa using
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra.normalOrderedCurrent_heisenberg_from_matrixUnit
      (C := B.rawCAR) (hK := hK) m n

end ConformalCurrentBoundary

end InfoGeometry.Canonical.ConformalCurrentHierarchyBoundary
