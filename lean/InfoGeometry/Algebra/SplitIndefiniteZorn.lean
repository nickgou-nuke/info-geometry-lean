import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Split-indefinite Zorn coordinates

The vector block carries the diagonal split metric of signature `(2,1)`.
This owner is deliberately independent of the finite-field F₂ specialization:
it records only the coordinate identities needed before any finite-group
specialization is attempted.
-/

namespace InfoGeometry.Algebra.SplitIndefiniteZorn

variable {R : Type*} [CommRing R]

abbrev SplitVec3 (R : Type*) := Fin 3 → R

def splitDot (x y : SplitVec3 R) : R :=
  x 0 * y 0 + x 1 * y 1 - x 2 * y 2

def splitCross (x y : SplitVec3 R) : SplitVec3 R :=
  ![x 1 * y 2 - x 2 * y 1,
    x 2 * y 0 - x 0 * y 2,
    -(x 0 * y 1 - x 1 * y 0)]

def splitDet (x y z : SplitVec3 R) : R :=
  x 0 * (y 1 * z 2 - y 2 * z 1)
    - x 1 * (y 0 * z 2 - y 2 * z 0)
    + x 2 * (y 0 * z 1 - y 1 * z 0)

@[simp] theorem splitDot_comm (x y : SplitVec3 R) :
    splitDot x y = splitDot y x := by
  simp [splitDot]
  ring

@[simp] theorem splitCross_self (x : SplitVec3 R) :
    splitCross x x = 0 := by
  funext i
  fin_cases i <;> simp [splitCross] <;> ring

theorem splitDot_cross (x y z : SplitVec3 R) :
    splitDot (splitCross x y) z = splitDet x y z := by
  simp [splitDot, splitCross, splitDet]
  ring

theorem splitCross_orthogonal_left (x y : SplitVec3 R) :
    splitDot (splitCross x y) x = 0 := by
  rw [splitDot_cross]
  simp [splitDet]
  ring

theorem splitCross_orthogonal_right (x y : SplitVec3 R) :
    splitDot (splitCross x y) y = 0 := by
  rw [splitDot_cross]
  simp [splitDet]
  ring

theorem splitMetric_basis :
    splitDot (fun i => if i = 0 then (1 : R) else 0)
      (fun i => if i = 0 then (1 : R) else 0) = 1 ∧
    splitDot (fun i => if i = 1 then (1 : R) else 0)
      (fun i => if i = 1 then (1 : R) else 0) = 1 ∧
    splitDot (fun i => if i = 2 then (1 : R) else 0)
      (fun i => if i = 2 then (1 : R) else 0) = -1 := by
  simp [splitDot]

structure SplitZornMatrix (R : Type*) [CommRing R] where
  a : R
  x : SplitVec3 R
  y : SplitVec3 R
  b : R

def splitZornNorm (X : SplitZornMatrix R) : R :=
  X.a * X.b - splitDot X.x X.y

end InfoGeometry.Algebra.SplitIndefiniteZorn
