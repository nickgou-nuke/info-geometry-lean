import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Matrix

/-!
# Split Octonions (Zorn Matrices) in Native Mathlib

This module defines the non-associative algebra of Split Octonions 𝕆ₛ 
using Zorn matrices, formulated natively with `Fin 3 → ℝ` vectors.
-/

abbrev Vec3 := Fin 3 → ℝ

/-- Standard 3D dot product natively over `Fin 3` -/
def dotProd (u v : Vec3) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Standard 3D cross product natively over `Fin 3` -/
def crossProd (u v : Vec3) : Vec3 :=
  ![ u 1 * v 2 - u 2 * v 1,
     u 2 * v 0 - u 0 * v 2,
     u 0 * v 1 - u 1 * v 0 ]

/-- Zorn Matrix representation of a Split Octonion -/
@[ext]
structure Zorn where
  a : ℝ
  b : ℝ
  u : Vec3
  v : Vec3

/-- Zorn Matrix Multiplication (Non-associative due to crossProd) -/
def zornMul (X Y : Zorn) : Zorn :=
  { a := X.a * Y.a + dotProd X.u Y.v,
    b := X.b * Y.b + dotProd X.v Y.u,
    u := ![ X.a * Y.u 0 + Y.b * X.u 0 + (crossProd X.v Y.v) 0,
            X.a * Y.u 1 + Y.b * X.u 1 + (crossProd X.v Y.v) 1,
            X.a * Y.u 2 + Y.b * X.u 2 + (crossProd X.v Y.v) 2 ],
    v := ![ X.b * Y.v 0 + Y.a * X.v 0 - (crossProd X.u Y.u) 0,
            X.b * Y.v 1 + Y.a * X.v 1 - (crossProd X.u Y.u) 1,
            X.b * Y.v 2 + Y.a * X.v 2 - (crossProd X.u Y.u) 2 ] }

/-- The quadratic form N(Z) = a*b - u·v -/
def zornNorm (Z : Zorn) : ℝ :=
  Z.a * Z.b - dotProd Z.u Z.v

theorem zornNorm_mul (X Y : Zorn) :
    zornNorm (zornMul X Y) = zornNorm X * zornNorm Y := by
  dsimp [zornNorm, zornMul, dotProd, crossProd]
  ring

theorem explicit_nonzero_null : ∃ (Z : Zorn), (Z.a ≠ 0) ∧ zornNorm Z = 0 := by
  let Z_null : Zorn := { a := 1, b := 1, u := ![1, 0, 0], v := ![1, 0, 0] }
  use Z_null
  constructor
  · norm_num
  · simp [zornNorm, dotProd, Z_null]

/-- Zorn conjugation splits the algebra -/
def zornConjugate (Z : Zorn) : Zorn :=
  { a := Z.b,
    b := Z.a,
    u := fun i => - Z.u i,
    v := fun i => - Z.v i }

/-- Z * Z_bar = N(Z) * I -/
theorem involution_decomposition (Z : Zorn) :
    zornMul Z (zornConjugate Z) = {a := zornNorm Z, b := zornNorm Z, u := 0, v := 0} := by
  dsimp [zornMul, zornConjugate, zornNorm, dotProd, crossProd]
  ext1
  · ring
  · ring
  · ext i; fin_cases i <;> (simp; ring)
  · ext i; fin_cases i <;> (simp; ring)
