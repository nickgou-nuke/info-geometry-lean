/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.QuadraticArnoldNumerator

/-! Division-free sufficiency for the literal quadratic Arnold numerator. -/
namespace InfoGeometry.Geometry.QuadraticArnoldNumerator
open NonIsoConf3LogWedgeObstruction

def polar (u v : Vec4) : ℤ := u.t*v.t-u.x*v.x-u.y*v.y-u.z*v.z

theorem polar_symm (u v : Vec4) : polar u v = polar v u := by
  unfold polar
  ring

theorem polar_mul_coord (u v : Vec4)
    (h : ∀ i j, coord u i * coord v j = coord u j * coord v i) (i : Fin 4) :
    polar u v * coord u i = q4 u * coord v i := by
  have h0 := h 0 i
  have h1 := h 1 i
  have h2 := h 2 i
  have h3 := h 3 i
  simp only [coord] at h0 h1 h2 h3
  unfold polar q4
  simp only [coord]
  linear_combination -u.t*h0 + u.x*h1 + u.y*h2 + u.z*h3

theorem polar_mul_coord_right (u v : Vec4)
    (h : ∀ i j, coord u i * coord v j = coord u j * coord v i) (i : Fin 4) :
    polar u v * coord v i = q4 v * coord u i := by
  rw [polar_symm]
  apply polar_mul_coord
  intro k l
  simpa only [mul_comm] using (h k l).symm

theorem quadric_displacement_sum (X Y Z : Vec4) :
    q4 (sub X Z) = q4 (sub X Y) + q4 (sub Y Z) +
      2 * polar (sub X Y) (sub Y Z) := by
  unfold q4 sub polar
  ring

def mixedCore (u v : Vec4) (i j : Fin 4) : ℤ :=
  2 * polar u v * coord u i * coord v j -
    q4 v * coord u i * coord u j - q4 u * coord v i * coord v j

theorem mixedCore_zero (u v : Vec4)
    (h : ∀ i j, coord u i * coord v j = coord u j * coord v i) (i j : Fin 4) :
    mixedCore u v i j = 0 := by
  have hl := polar_mul_coord u v h i
  have hr := polar_mul_coord_right u v h j
  unfold mixedCore
  linear_combination coord v j * hl + coord u i * hr

theorem numerator_xy (X Y Z : Vec4) (i j : Fin 4) :
    numerator X Y Z (0,i) (1,j) = 4 * sig i * sig j *
      (mixedCore (sub X Y) (sub Y Z) i j +
        q4 (sub Y Z) * displacementMinor X Y Z i j) := by
  simp only [numerator, edgeGradient, gradFirst, gradSecond, wedgeCoeff,
    show (0 : Fin 3) ≠ 1 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide, ite_true, ite_false]
  rw [quadric_displacement_sum]
  simp only [mixedCore, displacementMinor, coord_sub]
  ring

theorem numerator_xz (X Y Z : Vec4) (i j : Fin 4) :
    numerator X Y Z (0,i) (2,j) =
      -(4 * sig i * sig j) * mixedCore (sub X Y) (sub Y Z) i j := by
  simp [numerator, edgeGradient, gradFirst, gradSecond, wedgeCoeff,
    mixedCore, coord_sub]
  rw [quadric_displacement_sum X Y Z]
  ring

theorem numerator_yy (X Y Z : Vec4) (i j : Fin 4) :
    numerator X Y Z (1,i) (1,j) =
      -(4 * sig i * sig j) * q4 (sub X Z) * displacementMinor X Y Z i j := by
  simp [numerator, edgeGradient, gradFirst, gradSecond, wedgeCoeff,
    displacementMinor, coord_sub]
  ring

theorem numerator_yz (X Y Z : Vec4) (i j : Fin 4) :
    numerator X Y Z (1,i) (2,j) = 4 * sig i * sig j *
      (mixedCore (sub X Y) (sub Y Z) i j +
        q4 (sub X Y) * displacementMinor X Y Z i j) := by
  simp [numerator, edgeGradient, gradFirst, gradSecond, wedgeCoeff,
    mixedCore, displacementMinor, coord_sub]
  rw [quadric_displacement_sum X Y Z]
  ring

theorem numerator_zz (X Y Z : Vec4) (i j : Fin 4) :
    numerator X Y Z (2,i) (2,j) =
      -(4 * sig i * sig j) * q4 (sub X Y) * displacementMinor X Y Z i j := by
  simp [numerator, edgeGradient, gradFirst, gradSecond, wedgeCoeff,
    displacementMinor, coord_sub]
  ring

theorem numerator_zero_of_displacement_minors (X Y Z : Vec4)
    (h : ∀ i j, coord (sub X Y) i * coord (sub Y Z) j =
      coord (sub X Y) j * coord (sub Y Z) i) :
    ∀ α β, numerator X Y Z α β = 0 := by
  have hm (i j) : displacementMinor X Y Z i j = 0 := sub_eq_zero.mpr (h i j)
  have hc := mixedCore_zero (sub X Y) (sub Y Z) h
  rintro ⟨a,i⟩ ⟨b,j⟩
  fin_cases a <;> fin_cases b
  · change numerator X Y Z (0, i) (0, j) = 0
    rw [numerator_xx, hm, mul_zero]
  · change numerator X Y Z (0, i) (1, j) = 0
    rw [numerator_xy, hc, hm]; simp
  · change numerator X Y Z (0, i) (2, j) = 0
    rw [numerator_xz, hc, mul_zero]
  · change numerator X Y Z (1, i) (0, j) = 0
    rw [numerator_skew, numerator_xy, hc, hm]; simp
  · change numerator X Y Z (1, i) (1, j) = 0
    rw [numerator_yy, hm, mul_zero]
  · change numerator X Y Z (1, i) (2, j) = 0
    rw [numerator_yz, hc, hm]; simp
  · change numerator X Y Z (2, i) (0, j) = 0
    rw [numerator_skew, numerator_xz, hc, mul_zero, neg_zero]
  · change numerator X Y Z (2, i) (1, j) = 0
    rw [numerator_skew, numerator_yz, hc, hm]; simp
  · change numerator X Y Z (2, i) (2, j) = 0
    rw [numerator_zz, hm, mul_zero]

theorem numerator_vanishes_iff (X Y Z : Vec4) (hq : q4 (sub Y Z) ≠ 0) :
    (∀ α β, numerator X Y Z α β = 0) ↔
      ∀ i j, coord (sub X Y) i * coord (sub Y Z) j =
        coord (sub X Y) j * coord (sub Y Z) i :=
  ⟨displacement_minors_of_numerator_zero X Y Z hq,
    numerator_zero_of_displacement_minors X Y Z⟩

end InfoGeometry.Geometry.QuadraticArnoldNumerator
