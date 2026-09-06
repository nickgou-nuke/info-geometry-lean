import Mathlib
import InfoGeometry.Canonical.ZornSpinor

open InfoGeometry.Canonical

namespace Scratch

abbrev ConcreteZorn := InfoGeometry.Canonical.ZornMatrix ℚ

def concreteTrialityProjector : ConcreteZorn →ₗ[ℚ] ConcreteZorn where
  toFun Z := { a := Z.b, b := Z.a, x := Z.y, y := Z.x }
  map_add' := by
    intro X Y
    ext <;> rfl
  map_smul' := by
    intro c X
    ext <;> rfl

def ePlus : ConcreteZorn := { a := 1, b := 0, x := 0, y := 0 }
def up0 : ConcreteZorn := { a := 0, b := 0, x := ![1, 0, 0], y := 0 }
def down0 : ConcreteZorn := { a := 0, b := 0, x := 0, y := ![1, 0, 0] }

def commutator (X Y : ConcreteZorn) : ConcreteZorn := X * Y - Y * X

example : concreteTrialityProjector up0 = down0 := by
  ext i <;> simp [concreteTrialityProjector, up0, down0]

example : commutator ePlus up0 = up0 := by
  ext i <;> simp [commutator, ePlus, up0, InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]

example : commutator ePlus down0 = -down0 := by
  ext i <;> fin_cases i <;> simp [commutator, ePlus, down0, InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross]

example : concreteTrialityProjector (commutator ePlus up0) ≠ commutator ePlus (concreteTrialityProjector up0) := by
  intro h
  have h0 := congrArg (fun Z => Z.y 0) h
  simp [commutator, ePlus, up0, down0, concreteTrialityProjector,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross] at h0
  norm_num at h0

end Scratch
