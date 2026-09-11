import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.Concrete
import InfoGeometry.Quantum.CircularPauliCausalCone

noncomputable section

namespace InfoGeometry.Canonical.ZornLeftActionLinearization

open InfoGeometry.Algebra.Zorn.Concrete
open InfoGeometry.Quantum.CircularPauliCausalCone

abbrev Coord8 := InfoGeometry.Algebra.FiniteSpin.Vec8C
abbrev Zorn8 := ZornCell ℂ

def coordOfZorn (X : Zorn8) : Coord8 :=
  ![X.r, X.s, X.x1, X.x2, X.x3, X.y1, X.y2, X.y3]

def zornOfCoord (c : Coord8) : Zorn8 where
  r := c 0
  s := c 1
  x1 := c 2
  x2 := c 3
  x3 := c 4
  y1 := c 5
  y2 := c 6
  y3 := c 7

@[simp] theorem coordOfZorn_zornOfCoord (c : Coord8) :
    coordOfZorn (zornOfCoord c) = c := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem zornOfCoord_coordOfZorn (X : Zorn8) :
    zornOfCoord (coordOfZorn X) = X := by
  cases X
  rfl

theorem coordOfZorn_injective : Function.Injective coordOfZorn := by
  intro X Y h
  rw [← zornOfCoord_coordOfZorn X, ← zornOfCoord_coordOfZorn Y, h]

def leftMulLinear (X : Zorn8) : Coord8 →ₗ[ℂ] Coord8 where
  toFun c := coordOfZorn (ZornCell.mulZ X (zornOfCoord c))
  map_add' c d := by
    funext i
    fin_cases i <;>
    simp [coordOfZorn, zornOfCoord, ZornCell.mulZ,
        add_mul, mul_add]
      <;> ring

  map_smul' a c := by
    funext i
    fin_cases i <;>
      simp [coordOfZorn, zornOfCoord, ZornCell.mulZ,
        smul_eq_mul]
      <;> ring

noncomputable def leftMulMatrix (X : Zorn8) : Matrix (Fin 8) (Fin 8) ℂ :=
  LinearMap.toMatrix (Pi.basisFun ℂ (Fin 8)) (Pi.basisFun ℂ (Fin 8))
    (leftMulLinear X)

theorem leftMulMatrix_mulVec_repr (X : Zorn8) (c : Coord8) :
    Matrix.mulVec (leftMulMatrix X)
        (⇑((Pi.basisFun ℂ (Fin 8)).repr c)) =
      ⇑((Pi.basisFun ℂ (Fin 8)).repr (leftMulLinear X c)) := by
  simpa [leftMulMatrix] using
    (LinearMap.toMatrix_mulVec_repr
      (Pi.basisFun ℂ (Fin 8)) (Pi.basisFun ℂ (Fin 8))
      (leftMulLinear X) c)

theorem leftMulMatrix_mulVec (X : Zorn8) (c : Coord8) :
    Matrix.mulVec (leftMulMatrix X) c =
      coordOfZorn (ZornCell.mulZ X (zornOfCoord c)) := by
  have h := leftMulMatrix_mulVec_repr X c
  simpa [leftMulLinear, coordOfZorn, zornOfCoord] using h

theorem leftMulMatrix_mulVec_eq_pauliCorrelation (X : Zorn8) (c : Coord8) :
    Matrix.mulVec (leftMulMatrix X) c =
      coordOfZorn (zornCorrelationReadout X (zornOfCoord c)) := by
  rw [leftMulMatrix_mulVec, zornCorrelationReadout_eq_zornMul]

@[simp] theorem leftMulLinear_apply (X : Zorn8) (c : Coord8) :
    leftMulLinear X c = coordOfZorn (X * zornOfCoord c) := rfl

theorem leftMulLinear_coord (X : Zorn8) (Y : Zorn8) :
    leftMulLinear X (coordOfZorn Y) = coordOfZorn (X * Y) := by
  rw [leftMulLinear_apply, zornOfCoord_coordOfZorn]

theorem leftMulLinear_coord_eq_pauliCorrelation (X Y : Zorn8) :
    leftMulLinear X (coordOfZorn Y) =
      coordOfZorn (zornCorrelationReadout X Y) := by
  rw [leftMulLinear_coord, zornCorrelationReadout_eq_zornMul]
  rfl

end InfoGeometry.Canonical.ZornLeftActionLinearization

end noncomputable section
