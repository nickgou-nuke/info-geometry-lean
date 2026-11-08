/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! # The actual adjugate and trace-one projective matrices

These identities concern arbitrary three-by-three matrices, without symmetry,
diagonality, characteristic restrictions, or a separately supplied quadratic
trace parameter. They do not identify this special Jordan algebra with Albert's
exceptional algebra.
-/

namespace InfoGeometry.OperatorAlgebra.MatrixThreeAdjugate

variable {R : Type*} [CommRing R]

/-- Upper off-diagonal matrix unit in `M₃(R)`. -/
def mat3Unit01 : Matrix (Fin 3) (Fin 3) R :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- Lower off-diagonal matrix unit in `M₃(R)`. -/
def mat3Unit10 : Matrix (Fin 3) (Fin 3) R :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- Matrix multiplication on `M₃(R)` is noncommutative over any nontrivial ring. -/
theorem mat3_units_noncommute [Nontrivial R] :
    mat3Unit01 (R := R) * mat3Unit10 (R := R) ≠
      mat3Unit10 (R := R) * mat3Unit01 (R := R) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M 0 0) h
  have h10 : (1 : R) = 0 := by
    simpa [mat3Unit01, mat3Unit10, Matrix.mul_apply, Fin.sum_univ_three] using h00
  exact one_ne_zero h10

/-- Division-free quadratic adjugate identity in dimension three. -/
theorem adjugate_eq_quadratic (X : Matrix (Fin 3) (Fin 3) R) :
    X.adjugate = X * X - Matrix.trace X • X + Matrix.trace X.adjugate • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.trace,
      Matrix.diag, Fin.sum_univ_three] <;> ring

/-- Vanishing of the actual adjugate forces the quadratic relation. -/
theorem mul_self_eq_trace_smul_of_adjugate_zero
    (X : Matrix (Fin 3) (Fin 3) R) (h : X.adjugate = 0) :
    X * X = Matrix.trace X • X := by
  have hx := adjugate_eq_quadratic X
  rw [h] at hx
  simpa using (sub_eq_zero.mp (by simpa using hx.symm) :
    X * X = Matrix.trace X • X)

/-- Trace one and adjugate zero suffice; no extra `s₂ = 0` assumption is needed. -/
theorem idempotent_of_trace_one_adjugate_zero
    (X : Matrix (Fin 3) (Fin 3) R)
    (ht : Matrix.trace X = 1) (ha : X.adjugate = 0) :
    IsIdempotentElem X := by
  change X * X = X
  simpa [ht] using mul_self_eq_trace_smul_of_adjugate_zero X ha

end InfoGeometry.OperatorAlgebra.MatrixThreeAdjugate
