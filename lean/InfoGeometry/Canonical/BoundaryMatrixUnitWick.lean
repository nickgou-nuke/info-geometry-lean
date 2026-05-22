import InfoGeometry.Canonical.NormalOrderedCurrent

/-!
# InfoGeometry.Canonical.BoundaryMatrixUnitWick

Importable canonical boundary surface for the finite matrix-unit Wick commutator.

This file does not construct a new current algebra. It re-exports the owner
theorem from `NormalOrderedCurrent` under a circuit-facing boundary name.
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

end InfoGeometry.Canonical.BoundaryMatrixUnitWick
