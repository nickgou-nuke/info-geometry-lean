import InfoGeometry.Canonical.NormalOrderedCurrent
import InfoGeometry.Canonical.BosonizationConstructiveCurrent

/-!
# InfoGeometry.Canonical.BoundaryMatrixUnitWick

Importable canonical boundary surface for the finite matrix-unit Wick commutator.

This file does not construct a new current algebra. It re-exports the owner
theorems from `NormalOrderedCurrent` and `BosonizationConstructiveCurrent`
under circuit-facing boundary names.
-/

namespace InfoGeometry.Canonical.BoundaryMatrixUnitWick

open InfoGeometry.Canonical.NormalOrderedCurrent

section CanonicalMatrixUnits

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Boundary matrix-unit Wick commutator in canonical circuit form. -/
theorem boundaryMatrixUnitWick_commutator
    (occ : ι → ℤ) (a b c d : ι) :
    algebraCommutator
        (normalOrderedMatrixUnit (R := R) occ a b)
        (normalOrderedMatrixUnit (R := R) occ c d)
      =
      (if b = c then normalOrderedMatrixUnit (R := R) occ a d else 0)
        - (if a = d then normalOrderedMatrixUnit (R := R) occ c b else 0)
        + wickCorrection (R := R) occ a b c d := by
  simpa using
    normalOrdered_matrixUnit_commutator (R := R) occ a b c d

end CanonicalMatrixUnits

section RawCARBoundaryCurrent

variable {A : Type*} [Ring A]

/--
Boundary matrix-unit Wick commutator from normalized raw CAR modes.

This exports the owner theorem with the central Wick correction
`(occ a - occ b) • K`, where the normalized mode-completion has `K = 1`.
-/
theorem boundaryMatrixUnitWick_commutator_from_rawCAR
    (C : InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeAlgebra A)
    (a b c d : Int) :
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.comm
        (C.matrixUnit a b) (C.matrixUnit c d) =
      (if b = c then C.matrixUnit a d else 0) -
        (if a = d then C.matrixUnit c b else 0) +
        (if b = c ∧ a = d then
          (InfoGeometry.Canonical.BosonizationConstructiveCurrent.occ a -
            InfoGeometry.Canonical.BosonizationConstructiveCurrent.occ b) • C.central
        else 0) :=
  C.boundaryMatrixUnitWick_commutator_from_rawCAR a b c d

/--
Completed boundary current Heisenberg law derived from matrix-unit Wick normal
ordering and the polarization crossing count.
-/
theorem boundaryCurrent_heisenberg_from_matrixUnit
    (C : InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARModeAlgebra A)
    (m n : Int) :
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.CCRBracketCompleted C
        (InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C m)
        (InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent C n) =
      if m + n = 0 then
        m • InfoGeometry.Canonical.BosonizationConstructiveCurrent.completedCentral C
      else 0 :=
  InfoGeometry.Canonical.BosonizationConstructiveCurrent.normalOrderedCurrent_heisenberg_from_matrixUnit
    C m n

/--
Explicit-central boundary matrix-unit Wick commutator, specialized to the
normalized branch `central = 1`.
-/
theorem boundaryMatrixUnitWick_commutator_from_explicitRawCAR
    (C : InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra A)
    (hK : C.central = 1) (a b c d : Int) :
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.comm
        (C.matrixUnit a b) (C.matrixUnit c d) =
      (if b = c then C.matrixUnit a d else 0) -
        (if a = d then C.matrixUnit c b else 0) +
        (if b = c ∧ a = d then
          (InfoGeometry.Canonical.BosonizationConstructiveCurrent.occ a -
            InfoGeometry.Canonical.BosonizationConstructiveCurrent.occ b) • C.central
        else 0) :=
  C.normalOrdered_matrixUnit_commutator_from_rawCAR a b c d hK

/--
Explicit-central completed boundary current Heisenberg law on the normalized
central branch.
-/
theorem boundaryCurrent_heisenberg_from_explicitRawCAR
    (C : InfoGeometry.Canonical.BosonizationConstructiveCurrent.RawCARAlgebra A)
    (hK : C.central = 1) (m n : Int) :
    C.CCRBracketCompleted hK (C.normalOrderedCurrent hK m) (C.normalOrderedCurrent hK n) =
      if m + n = 0 then m • C.completedCentral else 0 :=
  C.normalOrderedCurrent_heisenberg_from_matrixUnit hK m n

end RawCARBoundaryCurrent

end InfoGeometry.Canonical.BoundaryMatrixUnitWick
