import InfoGeometry.Physics.TKKZorn

open InfoGeometry.Physics.TKKZorn
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

namespace Scratch

noncomputable section

abbrev QZ := ZornMatrix ℚ

def qcp : CrossProduct3 ℚ := {
  dot := fun x y => x 0 * y 0 + x 1 * y 1 + x 2 * y 2
  cross := fun x y => ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]
  dot_zero_left := by intro v; ring
  dot_zero_right := by intro v; ring
  cross_zero_left := by intro v; ext i <;> fin_cases i <;> simp
  cross_zero_right := by intro v; ext i <;> fin_cases i <;> simp }

def up0 : QZ := { a := 0, b := 0, x := ![1,0,0], y := 0 }

example : fermi_operator qcp (0 : QZ) up0 = 0 := by
  ext i <;> fin_cases i <;> simp [fermi_operator, qcp, up0, zMul,
    InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]

end Scratch
