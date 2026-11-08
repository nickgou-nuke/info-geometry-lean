/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import InfoGeometry.Twistor.NullProjective

/-!
# A projective affine chart of the split-signature null quadric

The spacetime carrier is the real `2 × 2` matrix space with determinant form
`x₀₀x₁₁ - x₀₁x₁₀`. The ambient carrier is the genuine six-dimensional real vector
space `Fin 6 → ℝ`, equipped with the Mathlib quadratic form
`X₀X₁ - X₂X₃ + X₄² - X₅²`. The normalized lift
`(x₀₀,x₁₁,x₀₁,x₁₀,(1-q(x))/2,(1+q(x))/2)` is null and defines a point of the
native projective null cone. Its last two coordinates sum to one, which proves
injectivity on projective rays. This theorem does not claim that the chart covers
the entire projective null quadric.

Incidence is expressed by the residual `ω - xπ`; its zero set is exactly
`ω = xπ`. It is not identified with the kernel of `xπ`.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization BigOperators

namespace InfoGeometry.Twistor.SplitSignatureConformalChart

abbrev Spacetime22 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Split63 := Fin 6 → ℝ

/-- Determinant quadratic polynomial on real `2 × 2` spacetime matrices. -/
def spacetimeQuadratic (x : Spacetime22) : ℝ :=
  x 0 0 * x 1 1 - x 0 1 * x 1 0

/-- Coordinate polynomial of signature `(3,3)` on `Fin 6 → ℝ`. -/
def splitQuadraticFun (X : Split63) : ℝ :=
  X 0 * X 1 - X 2 * X 3 + X 4 ^ 2 - X 5 ^ 2

/-- Coordinates that diagonalize the two determinant hyperbolic planes. -/
def splitDiagonalCoordinates (X : Split63) : Split63 :=
  ![(X 0 + X 1) / 2, (X 0 - X 1) / 2,
    (X 2 + X 3) / 2, (X 2 - X 3) / 2, X 4, X 5]

/-- The genuine Mathlib quadratic form with coordinate signature `(3,3)`. -/
def splitQuadratic : QuadraticForm ℝ Split63 :=
  QuadraticMap.ofPolar splitQuadraticFun
    (by intro c X; simp [splitQuadraticFun]; ring)
    (by intro X Y Z; simp [QuadraticMap.polar, splitQuadraticFun]; ring)
    (by intro c X Y; simp [QuadraticMap.polar, splitQuadraticFun]; ring)

@[simp] theorem splitQuadratic_apply (X : Split63) :
    splitQuadratic X = splitQuadraticFun X := rfl

/-- In diagonal coordinates, the form has three positive and three negative square terms. -/
theorem splitQuadratic_diagonal (X : Split63) :
    splitQuadratic X =
      (splitDiagonalCoordinates X 0) ^ 2 - (splitDiagonalCoordinates X 1) ^ 2 -
      (splitDiagonalCoordinates X 2) ^ 2 + (splitDiagonalCoordinates X 3) ^ 2 +
      (splitDiagonalCoordinates X 4) ^ 2 - (splitDiagonalCoordinates X 5) ^ 2 := by
  simp [splitQuadratic_apply, splitQuadraticFun, splitDiagonalCoordinates]
  ring

/-- Scalar identity behind the conformal null lift. -/
theorem splitChart_scalar_null (q : ℝ) :
    q + ((1 - q) / 2) ^ 2 - ((1 + q) / 2) ^ 2 = 0 := by
  ring

/-- The two added coordinates normalize to one. -/
theorem splitChart_scalar_normalized (q : ℝ) :
    (1 - q) / 2 + (1 + q) / 2 = 1 := by
  ring

/-- The normalized affine representative associated with a spacetime matrix. -/
def conformalChart (x : Spacetime22) : Split63 :=
  ![x 0 0, x 1 1, x 0 1, x 1 0,
    (1 - spacetimeQuadratic x) / 2, (1 + spacetimeQuadratic x) / 2]

/-- Recover the four spacetime coordinates from the first four split coordinates. -/
def spacetimeFromSplit (X : Split63) : Spacetime22 := fun i j =>
  if i = 0 then (if j = 0 then X 0 else X 2) else (if j = 0 then X 3 else X 1)

@[simp] theorem spacetimeFromSplit_apply_00 (X : Split63) :
    spacetimeFromSplit X 0 0 = X 0 := by simp [spacetimeFromSplit]

@[simp] theorem spacetimeFromSplit_apply_11 (X : Split63) :
    spacetimeFromSplit X 1 1 = X 1 := by simp [spacetimeFromSplit]

@[simp] theorem spacetimeFromSplit_apply_01 (X : Split63) :
    spacetimeFromSplit X 0 1 = X 2 := by simp [spacetimeFromSplit]

@[simp] theorem spacetimeFromSplit_apply_10 (X : Split63) :
    spacetimeFromSplit X 1 0 = X 3 := by simp [spacetimeFromSplit]

@[simp] theorem conformalChart_apply_zero (x : Spacetime22) :
    conformalChart x 0 = x 0 0 := rfl

@[simp] theorem conformalChart_apply_one (x : Spacetime22) :
    conformalChart x 1 = x 1 1 := rfl

@[simp] theorem conformalChart_apply_two (x : Spacetime22) :
    conformalChart x 2 = x 0 1 := rfl

@[simp] theorem conformalChart_apply_three (x : Spacetime22) :
    conformalChart x 3 = x 1 0 := rfl

@[simp] theorem conformalChart_normalized (x : Spacetime22) :
    conformalChart x 4 + conformalChart x 5 = 1 := by
  simpa [conformalChart] using splitChart_scalar_normalized (spacetimeQuadratic x)

/-- The conformal lift is a null vector for the native `(3,3)` quadratic form. -/
theorem conformalChart_isNull (x : Spacetime22) :
    splitQuadratic (conformalChart x) = 0 := by
  change splitQuadraticFun (conformalChart x) = 0
  simpa [splitQuadraticFun, conformalChart, spacetimeQuadratic] using
    splitChart_scalar_null (spacetimeQuadratic x)

/-- The chart vector is nonzero, witnessed by its normalized last-coordinate sum. -/
theorem conformalChart_ne_zero (x : Spacetime22) : conformalChart x ≠ 0 := by
  intro h
  have hsum := congrArg (fun X : Split63 => X 4 + X 5) h
  simp only [Pi.zero_apply, zero_add] at hsum
  rw [conformalChart_normalized] at hsum
  norm_num at hsum

/-- A point of the Mathlib-native projective null cone associated with the split form. -/
def conformalChartPoint (x : Spacetime22) : InfoGeometry.Twistor.TwistorSpace splitQuadratic :=
  InfoGeometry.Twistor.twistorMk splitQuadratic (conformalChart x)
    (conformalChart_ne_zero x) (conformalChart_isNull x)

/-- The normalized affine chart is injective as a map into the projective null quadric. -/
theorem conformalChartPoint_injective : Function.Injective conformalChartPoint := by
  intro x y hxy
  have hproj :
      Projectivization.mk ℝ (conformalChart x) (conformalChart_ne_zero x) =
        Projectivization.mk ℝ (conformalChart y) (conformalChart_ne_zero y) :=
    congrArg Subtype.val hxy
  rcases (Projectivization.mk_eq_mk_iff ℝ
      (conformalChart x) (conformalChart y)
      (conformalChart_ne_zero x) (conformalChart_ne_zero y)).1 hproj with
    ⟨c, hc⟩
  rw [Units.smul_def] at hc
  have hsum := congrArg (fun X : Split63 => X 4 + X 5) hc
  have hx := conformalChart_normalized x
  have hy := conformalChart_normalized y
  have hc_one : (c : ℝ) = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul] at hsum
    nlinarith
  have hvec : conformalChart x = conformalChart y := by
    simpa [hc_one] using hc.symm
  have h00 : x 0 0 = y 0 0 := by simpa using congrFun hvec 0
  have h11 : x 1 1 = y 1 1 := by simpa using congrFun hvec 1
  have h01 : x 0 1 = y 0 1 := by simpa using congrFun hvec 2
  have h10 : x 1 0 = y 1 0 := by simpa using congrFun hvec 3
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- Every null vector normalized by `X₄ + X₅ = 1` is represented by this chart. -/
theorem conformalChart_surjective_on_normalized_null (X : Split63)
    (hnull : splitQuadratic X = 0) (hnorm : X 4 + X 5 = 1) :
    ∃ x, conformalChart x = X := by
  have hnull' : X 0 * X 1 - X 2 * X 3 + X 4 ^ 2 - X 5 ^ 2 = 0 := by
    simpa [splitQuadratic_apply, splitQuadraticFun] using hnull
  have hlast : X 4 ^ 2 - X 5 ^ 2 = X 4 - X 5 := by
    calc
      X 4 ^ 2 - X 5 ^ 2 = (X 4 - X 5) * (X 4 + X 5) := by ring
      _ = X 4 - X 5 := by rw [hnorm, mul_one]
  have hdet : spacetimeQuadratic (spacetimeFromSplit X) = X 5 - X 4 := by
    change X 0 * X 1 - X 2 * X 3 = X 5 - X 4
    nlinarith [hnull', hlast]
  refine ⟨spacetimeFromSplit X, ?_⟩
  funext i
  fin_cases i <;>
    simp [conformalChart, spacetimeFromSplit, hdet] <;>
    nlinarith [hnorm]

/-- Incidence residual for real split-signature twistor coordinates. -/
def incidenceResidual (x : Fin 2 → Fin 2 → ℝ) (ω π : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun A => ω A - ∑ A', x A A' * π A'

/-- Incidence `ω = xπ` is precisely the kernel condition for the residual map. -/
theorem incidenceResidual_eq_zero_iff (x : Fin 2 → Fin 2 → ℝ) (ω π : Fin 2 → ℝ) :
    incidenceResidual x ω π = 0 ↔ ∀ A, ω A = ∑ A', x A A' * π A' := by
  constructor
  · intro h A
    exact sub_eq_zero.mp (congrFun h A)
  · intro h
    funext A
    exact sub_eq_zero.mpr (h A)

/-- The linear incidence residual map on real twistor pairs `(ω, π)`. -/
def incidenceResidualLMap (x : Fin 2 → Fin 2 → ℝ) :
    ((Fin 2 → ℝ) × (Fin 2 → ℝ)) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun z := incidenceResidual x z.1 z.2
  map_add' z w := by
    funext A
    simp [incidenceResidual, Fin.sum_univ_succ]
    ring
  map_smul' c z := by
    funext A
    simp [incidenceResidual, smul_eq_mul, Fin.sum_univ_succ]
    ring

/-- The incidence graph is the actual kernel of the linear residual map. -/
theorem incidenceResidualLMap_mem_ker_iff (x : Fin 2 → Fin 2 → ℝ)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    z ∈ LinearMap.ker (incidenceResidualLMap x) ↔
      ∀ A, z.1 A = ∑ A', x A A' * z.2 A' := by
  rw [LinearMap.mem_ker]
  exact incidenceResidual_eq_zero_iff x z.1 z.2

end InfoGeometry.Twistor.SplitSignatureConformalChart
