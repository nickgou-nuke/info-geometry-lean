import InfoGeometry.Canonical.ConformalCurrentHierarchyBoundary

/-!
# InfoGeometry.Canonical.ConformalProjectiveClosure

Direct canonical projective closure for the conformal engine.

This file packages the two independently owned direct canonical layers:

* the five-grade conformal inversion and its grade-zero fixed sector;
* the boundary current hierarchy with its completed Heisenberg law.

It does not assert that the conformal inversion derives the current algebra.
It records the combined projective closure as explicit canonical data.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConformalProjectiveClosure

open InfoGeometry.Canonical.ConformalCurrentHierarchyBoundary
open InfoGeometry.Canonical.ConformalFiveGradeInversion

universe u

/--
Direct canonical projective closure packet.

The inversion side and the boundary-current side are both present, but their
relationship is recorded as witness data rather than forced derivation.
-/
structure ProjectiveClosurePacket
    (L A : Type*) [Ring A] where
  inversionBoundary : ConformalCurrentBoundary L A

namespace ProjectiveClosure

variable {L A : Type*} [Ring A]
variable (C : ProjectiveClosurePacket L A)

/-- The conformal grade-zero sector survives the inversion. -/
@[simp] theorem grade_zero_survives
    {x : L}
    (hx : C.inversionBoundary.inversion.grade x = ConformalGrade.zero) :
    C.inversionBoundary.inversion.grade (C.inversionBoundary.inversion.theta x) =
      ConformalGrade.zero :=
  C.inversionBoundary.grade_zero_survives hx

/-- The positive/negative extremal grades are swapped by the inversion. -/
theorem extremal_grades_swapped
    {x : L}
    (hx : C.inversionBoundary.inversion.grade x = ConformalGrade.negTwo) :
    C.inversionBoundary.inversion.grade (C.inversionBoundary.inversion.theta x) =
      ConformalGrade.posTwo :=
  C.inversionBoundary.inversion.fixed_negTwo_mem_posTwo hx

/-- The boundary current Heisenberg law is available on the projective closure. -/
theorem boundary_current_heisenberg
    (m n : Int) :
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra.CCRBracketCompleted
      C.inversionBoundary.rawCAR C.inversionBoundary.hK
      (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra.normalOrderedCurrent
        C.inversionBoundary.rawCAR C.inversionBoundary.hK m)
      (InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra.normalOrderedCurrent
        C.inversionBoundary.rawCAR C.inversionBoundary.hK n) =
      if m + n = 0 then
        m • InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra.completedCentral
          C.inversionBoundary.rawCAR
      else
        0 :=
  C.inversionBoundary.boundary_current_heisenberg m n

end ProjectiveClosure

end InfoGeometry.Canonical.ConformalProjectiveClosure
