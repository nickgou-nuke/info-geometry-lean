import InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
import InfoGeometry.Clifford.Cl55SuperTKK
import InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
import InfoGeometry.Algebra.SupergradedBracket

noncomputable section

namespace InfoGeometry.Clifford.SuperGrassmannianTKK

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.Cl55SuperTKK
open InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
open InfoGeometry.Algebra.SupergradedBracket

def cl55VacuumIdealActionRingHom : Cl55 →+* EndV where
  toFun := cl55VacuumIdealLeftAction
  map_one' := by
    ext x
    simp [cl55VacuumIdealLeftAction]
  map_mul' a b := by
    ext x
    simp [cl55VacuumIdealLeftAction, mul_assoc]
  map_zero' := by
    ext x
    simp [cl55VacuumIdealLeftAction]
  map_add' a b := by
    ext x
    change (a + b) * x.1 = a * x.1 + b * x.1
    rw [add_mul]

noncomputable def exteriorToVacuumTKK : Exterior55 →+* EndV :=
  cl55VacuumIdealActionRingHom.comp twistorMapAlgHom.toRingHom

def positiveGrassmannianBladeTKKAction
    (C : Matrix (Fin 2) (Fin 4) ℝ) : EndV :=
  exteriorToVacuumTKK (positiveGrassmannianBlade C)

@[simp] theorem positiveGrassmannianBladeTKKAction_eq
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    positiveGrassmannianBladeTKKAction C =
      cl55VacuumIdealLeftAction
        (twistorMapAlgHom (positiveGrassmannianBlade C)) := rfl

theorem exteriorToVacuumTKK_superBracket
    (px py : Bool) (x y : Exterior55) :
    exteriorToVacuumTKK (superBracket px py x y) =
      superBracket px py (exteriorToVacuumTKK x) (exteriorToVacuumTKK y) :=
  InfoGeometry.Algebra.SupergradedBracket.map_superBracket
    (A := Exterior55) (B := EndV) (φ := exteriorToVacuumTKK) px py x y

theorem positiveGrassmannianBladeTKKAction_bracket
    (C D : Matrix (Fin 2) (Fin 4) ℝ) :
    tkkBracket (positiveGrassmannianBladeTKKAction C)
        (positiveGrassmannianBladeTKKAction D) =
      exteriorToVacuumTKK
        (commutator (positiveGrassmannianBlade C)
          (positiveGrassmannianBlade D)) := by
  change superBracket false false
    (exteriorToVacuumTKK (positiveGrassmannianBlade C))
    (exteriorToVacuumTKK (positiveGrassmannianBlade D)) = _
  calc
    _ = exteriorToVacuumTKK
        (superBracket false false (positiveGrassmannianBlade C)
          (positiveGrassmannianBlade D)) := by
      exact (InfoGeometry.Algebra.SupergradedBracket.map_superBracket
        (A := Exterior55) (B := EndV) (φ := exteriorToVacuumTKK)
        false false (positiveGrassmannianBlade C) (positiveGrassmannianBlade D)).symm
    _ = exteriorToVacuumTKK
        (InfoGeometry.Algebra.SupergradedBracket.commutator
          (positiveGrassmannianBlade C) (positiveGrassmannianBlade D)) := by
      simp [superBracket, InfoGeometry.Algebra.SupergradedBracket.commutator]

/-- The actual `Gr(2,4)` blade action on the Cl(5,5) vacuum ideal decomposes
into the five eigenspaces of the repository's TKK grading. -/
theorem positiveGrassmannianBladeTKKAction_grade_decomposition
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    ∃ xNeg2 xNeg1 x0 x1 x2 : EndV,
      xNeg2 ∈ tkkGrade (-2) ∧ xNeg1 ∈ tkkGrade (-1) ∧
      x0 ∈ tkkGrade 0 ∧ x1 ∈ tkkGrade 1 ∧
      x2 ∈ tkkGrade 2 ∧
      positiveGrassmannianBladeTKKAction C =
        xNeg2 + xNeg1 + x0 + x1 + x2 :=
  tkkFiveGrade_decomposition (positiveGrassmannianBladeTKKAction C)

end InfoGeometry.Clifford.SuperGrassmannianTKK

end noncomputable section
