import InfoGeometry.Canonical.BoundaryMatrixUnitWick
import InfoGeometry.Tessellation.CurrentCurvature

/-!
# Wilson defects and Wick/Schwinger central terms

This file is a narrow bridge from the tessellation Wilson-loop interface to the
already-proved boundary matrix-unit Wick theorem.

The bridge does not reprove normal ordering and does not identify arbitrary
Wilson defects with current-algebra anomalies.  It only packages the scalar
central summand from `BoundaryMatrixUnitWick` as the defect of a Wilson loop
based at the identity diamond.
-/

namespace WilsonSchwingerBridge

open InfoGeometry.Tessellation

/--
The Wilson loop carrying the Wick/Schwinger coefficient
`occ a - occ c`.
-/
def schwingerWilsonLoop (A : Type*) [Ring A] (a c : Int) :
    WilsonLoop A (unitDiamond A) :=
  centralDefectLoop A
    (InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ a -
      InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ c)

/-- The defect of the Schwinger Wilson loop is the Wick central coefficient. -/
theorem schwingerWilsonLoop_defect (A : Type*) [Ring A] (a c : Int) :
    WilsonLoop.defect (schwingerWilsonLoop A a c) =
      (InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ a -
        InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ c) • (1 : A) := by
  simp [schwingerWilsonLoop, centralDefectLoop_defect]

/--
The Wick/Schwinger Wilson loop as a central-defect realization over `ℤ`.
-/
def schwingerCentralDefectRealization
    (A : Type*) [Ring A] (a c : Int) :
    CentralDefectRealization A ℤ (schwingerWilsonLoop A a c) where
  scalar :=
    InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ a -
      InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ c
  defect_eq := by
    simp [schwingerWilsonLoop, centralDefectLoop_defect, unitDiamond]

/--
The conditional Wick/Schwinger central term can be read as a Wilson-loop
defect at the identity sector.
-/
theorem wickCentralTerm_eq_wilsonDefect
    {A : Type*} [Ring A] (a b c d : Int) :
    (if b = c ∧ a = d then
        (InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ a -
          InfoGeometry.Canonical.BoundaryMatrixUnitWick.occ c) • (1 : A)
      else 0) =
      (if b = c ∧ a = d then
          WilsonLoop.defect (schwingerWilsonLoop A a c)
        else 0) := by
  by_cases h : b = c ∧ a = d
  · simp [h, schwingerWilsonLoop_defect]
  · simp [h]

/--
Boundary matrix-unit Wick commutators with the central summand represented as a
Wilson-loop defect.
-/
theorem normalOrdered_matrixUnit_commutator_with_wilsonDefect
    {A : Type*} [Ring A] (psiPlus psiMinus : Int → A)
    (car_minus_plus :
      ∀ b c : Int,
        psiMinus (-b) * psiPlus c + psiPlus c * psiMinus (-b) =
          if b = c then 1 else 0)
    (car_plus_plus :
      ∀ a c : Int, psiPlus a * psiPlus c + psiPlus c * psiPlus a = 0)
    (car_minus_minus :
      ∀ b d : Int,
        psiMinus (-b) * psiMinus (-d) + psiMinus (-d) * psiMinus (-b) = 0)
    (a b c d : Int) :
    InfoGeometry.Canonical.BoundaryMatrixUnitWick.comm
        (InfoGeometry.Canonical.BoundaryMatrixUnitWick.matrixUnit psiPlus psiMinus a b)
        (InfoGeometry.Canonical.BoundaryMatrixUnitWick.matrixUnit psiPlus psiMinus c d) =
      (if b = c then
          InfoGeometry.Canonical.BoundaryMatrixUnitWick.matrixUnit psiPlus psiMinus a d
        else 0) -
        (if a = d then
          InfoGeometry.Canonical.BoundaryMatrixUnitWick.matrixUnit psiPlus psiMinus c b
        else 0) +
        (if b = c ∧ a = d then
          WilsonLoop.defect (schwingerWilsonLoop A a c)
        else 0) := by
  rw [
    InfoGeometry.Canonical.BoundaryMatrixUnitWick.normalOrdered_matrixUnit_commutator_from_rawCAR
      psiPlus psiMinus car_minus_plus car_plus_plus car_minus_minus a b c d]
  rw [← wickCentralTerm_eq_wilsonDefect (A := A) a b c d]

end WilsonSchwingerBridge
