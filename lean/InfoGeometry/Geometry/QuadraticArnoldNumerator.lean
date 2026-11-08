/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.External.Auto.NonIsoConf3LogWedgeObstruction

/-! Full ambient numerator of the quadratic logarithmic Arnold expression.
This polynomial uses the original obstruction's carrier and gradients.
No cohomological quotient relation or division by a quadric is asserted. -/
namespace InfoGeometry.Geometry.QuadraticArnoldNumerator
open NonIsoConf3LogWedgeObstruction

abbrev Coordinate := Fin 3 × Fin 4

def edgeGradient (X Y : Vec4) (a b : Fin 3) (α : Coordinate) : ℤ :=
  if α.1 = a then gradFirst X Y α.2
  else if α.1 = b then gradSecond X Y α.2 else 0

def numerator (X Y Z : Vec4) (α β : Coordinate) : ℤ :=
  wedgeCoeff (edgeGradient X Y 0 1 α) (edgeGradient X Y 0 1 β)
    (edgeGradient Y Z 1 2 α) (edgeGradient Y Z 1 2 β) * q4 (sub X Z) -
  wedgeCoeff (edgeGradient X Y 0 1 α) (edgeGradient X Y 0 1 β)
    (edgeGradient X Z 0 2 α) (edgeGradient X Z 0 2 β) * q4 (sub Y Z) +
  wedgeCoeff (edgeGradient Y Z 1 2 α) (edgeGradient Y Z 1 2 β)
    (edgeGradient X Z 0 2 α) (edgeGradient X Z 0 2 β) * q4 (sub X Y)

def displacementMinor (X Y Z : Vec4) (i j : Fin 4) : ℤ :=
  coord (sub X Y) i * coord (sub Y Z) j -
    coord (sub X Y) j * coord (sub Y Z) i

@[simp] theorem coord_sub (X Y : Vec4) (i : Fin 4) :
    coord (sub X Y) i = coord X i - coord Y i := by
  fin_cases i <;> rfl

theorem sig_ne_zero (i : Fin 4) : sig i ≠ 0 := by
  fin_cases i <;> norm_num [sig]

theorem numerator_skew (X Y Z : Vec4) (α β : Coordinate) :
    numerator X Y Z α β = -numerator X Y Z β α := by
  unfold numerator wedgeCoeff
  ring

@[simp] theorem numerator_diagonal (X Y Z : Vec4) (α : Coordinate) :
    numerator X Y Z α α = 0 := by
  simp [numerator, wedgeCoeff]

theorem numerator_dx0dy0 :
    numerator pointX pointY pointZ (0, 0) (1, 0) =
      arnoldDlogNumerator_dx0dy0 := by rfl

theorem numerator_counterexample :
    numerator pointX pointY pointZ (0, 0) (1, 0) = 52 := by
  rw [numerator_dx0dy0]
  exact naive_dlog_arnold_relation_obstructed.1

theorem numerator_xx (X Y Z : Vec4) (i j : Fin 4) :
    numerator X Y Z (0, i) (0, j) =
      ((-4 : ℤ) * q4 (sub Y Z) * sig i * sig j) *
        displacementMinor X Y Z i j := by
  simp [numerator, edgeGradient, wedgeCoeff, gradFirst,
    displacementMinor, coord_sub]
  ring

theorem displacementMinor_zero_of_numerator_zero (X Y Z : Vec4)
    (hq : q4 (sub Y Z) ≠ 0) (hzero : ∀ α β, numerator X Y Z α β = 0)
    (i j : Fin 4) : displacementMinor X Y Z i j = 0 := by
  have hc : (-4 : ℤ) * q4 (sub Y Z) * sig i * sig j ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hq)
      (sig_ne_zero i)) (sig_ne_zero j)
  have hmul := hzero (0, i) (0, j)
  rw [numerator_xx] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hc

theorem displacement_minors_of_numerator_zero (X Y Z : Vec4)
    (hq : q4 (sub Y Z) ≠ 0) (hzero : ∀ α β, numerator X Y Z α β = 0) :
    ∀ i j : Fin 4, coord (sub X Y) i * coord (sub Y Z) j =
      coord (sub X Y) j * coord (sub Y Z) i := by
  intro i j
  exact sub_eq_zero.mp
    (displacementMinor_zero_of_numerator_zero X Y Z hq hzero i j)

end InfoGeometry.Geometry.QuadraticArnoldNumerator
