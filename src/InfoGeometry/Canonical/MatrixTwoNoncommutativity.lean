/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! Noncommutativity of the full two-by-two source algebra over every
nontrivial commutative ring, witnessed by opposite off-diagonal matrix units. -/
namespace InfoGeometry.Canonical.MatrixTwoNoncommutativity

/-- Forward off-diagonal matrix unit. -/
def upperUnit {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

/-- Reverse off-diagonal matrix unit. -/
def lowerUnit {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]

theorem matrix_two_noncommutative {R : Type*} [CommRing R] [Nontrivial R] :
    upperUnit (R := R) * lowerUnit ≠ lowerUnit * upperUnit := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  norm_num [upperUnit, lowerUnit, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at he

end InfoGeometry.Canonical.MatrixTwoNoncommutativity
