import InfoGeometry.Tessellation.WilsonLoop
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import Mathlib.Algebra.Algebra.Basic

/-!
# Current curvature bridge API

This file contains the adapter that reads the completed Heisenberg current
coefficient as current curvature, together with the Wilson-loop defect
interface that can carry such scalar curvature.

The Wick/Schwinger current algebra theorems live in the canonical branch.  This
module does not reprove normal ordering or Heisenberg current identities; it
imports the already-proved completed-current theorem and renames its central
coefficient as current curvature.
-/

namespace InfoGeometry.Tessellation

namespace CurrentCurvature

open InfoGeometry.Canonical.BosonizationConstructiveCurrent

/--
The quantum Ricci scalar exposed by the completed current extension.

This is a naming adapter for the already constructed completed central carrier.
-/
def quantumRicciScalar {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) : A :=
  completedCentral C

/-- The Heisenberg/Ricci mode coefficient `m δ_{m+n,0}`. -/
def ricciModeCoefficient (m n : Int) : Int :=
  if m + n = 0 then m else 0

/--
Completed current curvature theorem.

This is the existing Heisenberg current theorem read as the central
current-curvature/Ricci anomaly.  It does not reprove Wick ordering.
-/
theorem currentCurvature_is_centralRicciAnomaly
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C
        (normalOrderedCurrent C m)
        (normalOrderedCurrent C n)
      =
      ricciModeCoefficient m n • quantumRicciScalar C := by
  rw [normalOrderedCurrent_heisenberg_from_matrixUnit C m n]
  unfold quantumRicciScalar ricciModeCoefficient
  by_cases hmn : m + n = 0 <;> simp [hmn]

/--
Expanded Heisenberg form of the current-curvature theorem.
-/
theorem currentCurvature_is_centralRicciAnomaly_if
    {A : Type*} [Ring A]
    (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C
        (normalOrderedCurrent C m)
        (normalOrderedCurrent C n)
      =
      if m + n = 0 then m • quantumRicciScalar C else 0 := by
  unfold quantumRicciScalar
  exact normalOrderedCurrent_heisenberg_from_matrixUnit C m n

end CurrentCurvature

/-- The identity sector as a tessellation diamond. -/
def unitDiamond (A : Type*) [Semiring A] : Diamond A where
  P := 1
  idem := by simp

/--
A Wilson loop at the identity sector whose defect is the prescribed integer
multiple of the identity.
-/
def centralDefectLoop (A : Type*) [Ring A] (k : Int) :
    WilsonLoop A (unitDiamond A) where
  holonomy := 1 + k • (1 : A)
  left_support := by simp [unitDiamond]
  right_support := by simp [unitDiamond]

/-- The defect of `centralDefectLoop` is exactly `k • 1`. -/
theorem centralDefectLoop_defect (A : Type*) [Ring A] (k : Int) :
    WilsonLoop.defect (centralDefectLoop A k) = k • (1 : A) := by
  simp [WilsonLoop.defect, centralDefectLoop, unitDiamond]

/--
A Wilson-loop defect realized as a scalar central curvature on the base sector.

The equation says that the holonomy defect is the scalar `scalar`, embedded in
the operator algebra, acting on the base idempotent.
-/
structure CentralDefectRealization
    (A R : Type*) [Ring A] [CommRing R] [Algebra R A]
    {base : Diamond A} (L : WilsonLoop A base) where
  /-- Scalar curvature coefficient. -/
  scalar : R
  /-- The Wilson-loop defect is the scalar curvature on the base sector. -/
  defect_eq :
    WilsonLoop.defect L = algebraMap R A scalar * base.P

namespace CentralDefectRealization

variable {A R : Type*} [Ring A] [CommRing R] [Algebra R A]
variable {base : Diamond A} {L : WilsonLoop A base}

/-- Read back the central-defect equation. -/
theorem defect_eq_scalar_base
    (C : CentralDefectRealization A R L) :
    WilsonLoop.defect L = algebraMap R A C.scalar * base.P :=
  C.defect_eq

/--
If the scalar base contribution vanishes, the Wilson loop is flat.

This is only the formal consequence of the defect interface; it does not assert
that any particular current-theoretic coefficient vanishes.
-/
theorem flat_of_scalar_base_eq_zero
    (C : CentralDefectRealization A R L)
    (hC : algebraMap R A C.scalar * base.P = 0) :
    WilsonLoop.Flat L :=
  WilsonLoop.flat_of_defect_eq_zero (by rw [C.defect_eq, hC])

end CentralDefectRealization

/-- Integer central loops realize their own integer scalar defect at the identity sector. -/
def centralDefectLoop_realization (A : Type*) [Ring A] (k : Int) :
    CentralDefectRealization A ℤ (centralDefectLoop A k) where
  scalar := k
  defect_eq := by
    simp [centralDefectLoop_defect, unitDiamond]

end InfoGeometry.Tessellation
