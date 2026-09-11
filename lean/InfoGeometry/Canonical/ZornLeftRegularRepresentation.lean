import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornAlternativeLaws
import Mathlib.Tactic

/-! Associative linearization of left multiplication on the eight-coordinate
carrier of the explicit Zorn product. -/

namespace InfoGeometry.Canonical.ZornLeftRegularRepresentation

open InfoGeometry.Algebra

abbrev ZM := ZornVectorMatrix ℝ
abbrev Coord := InfoGeometry.Algebra.FiniteSpin.Vec8R

def coordToZorn (x : Coord) : ZM :=
  ⟨x 0, ![x 1, x 2, x 3], ![x 4, x 5, x 6], x 7⟩

def zornToCoord (X : ZM) : Coord :=
  ![X.a, X.v 0, X.v 1, X.v 2, X.w 0, X.w 1, X.w 2, X.b]

theorem zornToCoord_coordToZorn (x : Coord) :
    zornToCoord (coordToZorn x) = x := by
  funext i
  fin_cases i <;> simp [zornToCoord, coordToZorn]

theorem coordToZorn_zornToCoord (X : ZM) :
    coordToZorn (zornToCoord X) = X := by
  rcases X with ⟨a, v, w, b⟩
  apply ZornVectorMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem zornToCoord_add (X Y : ZM) :
    zornToCoord (ZornVectorMatrix.add X Y) =
      zornToCoord X + zornToCoord Y := by
  funext i
  fin_cases i <;> simp [zornToCoord, ZornVectorMatrix.add]

theorem zornToCoord_smul (r : ℝ) (X : ZM) :
    zornToCoord (ZornVectorMatrix.smul r X) = r • zornToCoord X := by
  funext i
  fin_cases i <;> simp [zornToCoord, ZornVectorMatrix.smul]

theorem coordToZorn_add (x y : Coord) :
    coordToZorn (x + y) =
      ZornVectorMatrix.add (coordToZorn x) (coordToZorn y) := by
  rw [← coordToZorn_zornToCoord (ZornVectorMatrix.add (coordToZorn x) (coordToZorn y))]
  rw [zornToCoord_add, zornToCoord_coordToZorn, zornToCoord_coordToZorn]

theorem coordToZorn_smul (r : ℝ) (x : Coord) :
    coordToZorn (r • x) =
      ZornVectorMatrix.smul r (coordToZorn x) := by
  rw [← coordToZorn_zornToCoord (ZornVectorMatrix.smul r (coordToZorn x))]
  rw [zornToCoord_smul, zornToCoord_coordToZorn]

def leftRegular (F : ZM) : Coord →ₗ[ℝ] Coord where
  toFun x := zornToCoord (ZornVectorMatrix.mul F (coordToZorn x))
  map_add' x y := by
    rw [coordToZorn_add, ZornVectorMatrix.mul_add, zornToCoord_add]
  map_smul' r x := by
    rw [coordToZorn_smul, ZornVectorMatrix.mul_smul, zornToCoord_smul]
    rfl

@[simp] theorem leftRegular_apply (F : ZM) (x : Coord) :
    leftRegular F x =
      zornToCoord (ZornVectorMatrix.mul F (coordToZorn x)) := rfl

theorem leftRegular_comp_self (F : ZM) :
    (leftRegular F).comp (leftRegular F) = leftRegular (ZornVectorMatrix.mul F F) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply]
  change zornToCoord (ZornVectorMatrix.mul F
      (ZornVectorMatrix.mul F (coordToZorn x))) =
    zornToCoord (ZornVectorMatrix.mul (ZornVectorMatrix.mul F F)
      (coordToZorn x))
  have h := ZornVectorMatrix.associator_left_alternative F (coordToZorn x)
  have h' : ZornVectorMatrix.mul F (ZornVectorMatrix.mul F (coordToZorn x)) =
      ZornVectorMatrix.mul (ZornVectorMatrix.mul F F) (coordToZorn x) := by
    exact (sub_eq_zero.mp h).symm
  rw [h']

end InfoGeometry.Canonical.ZornLeftRegularRepresentation
