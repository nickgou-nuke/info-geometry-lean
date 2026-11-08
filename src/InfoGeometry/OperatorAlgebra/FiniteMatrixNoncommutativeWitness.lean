import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Concrete noncommutativity witness for the real two-by-two operator algebra

This file provides one explicit matrix-algebra witness that can be reused by
finite operator models. It makes no claim about arbitrary matrix carriers.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness

open scoped Matrix

/-- The first off-diagonal matrix unit in `M₂(ℝ)`. -/
def matrixUnit01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- The second off-diagonal matrix unit in `M₂(ℝ)`. -/
def matrixUnit10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- These matrix units witness that multiplication in `M₂(ℝ)` is
noncommutative. -/
theorem matrix_units_noncommute :
    matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The upper matrix unit in `M₂(R)`. -/
def matrixUnit01Over {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 0, 0]

/-- The lower matrix unit in `M₂(R)`. -/
def matrixUnit10Over {R : Type*} [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 1, 0]

/-- Matrix multiplication on `M₂(R)` is noncommutative whenever `R` is a
nontrivial ring. The nontriviality assumption is essential because the two
products agree over the zero ring. -/
theorem matrix_units_noncommute_of_nontrivial {R : Type*} [Ring R] [Nontrivial R] :
    matrixUnit01Over (R := R) * matrixUnit10Over (R := R) ≠
      matrixUnit10Over (R := R) * matrixUnit01Over (R := R) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  have h10 : (1 : R) = 0 := by
    simpa [matrixUnit01Over, matrixUnit10Over, Matrix.mul_apply, Fin.sum_univ_two] using h00
  exact one_ne_zero h10

end InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
