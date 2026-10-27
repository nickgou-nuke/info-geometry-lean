/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NoncommRing

/-! Semantic regressions on the full three-by-three real matrix algebra.
The potential source and both generating matrices have zero diagonal. Both
the coefficient matrices and the induced base derivations fail to commute. -/

noncomputable section

namespace InfoGeometryTests.DerivationMatrixGeometry

open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry

private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
private abbrev K := matrixDerivationsLane ℝ (Fin 3)

private def X : Mat := !![0, 1, 0; -1, 0, 0; 0, 0, 0]
private def Y : Mat := !![0, 0, 0; 0, 0, 1; 0, -1, 0]
private def P : Mat := !![0, 0, 1; 0, 0, 0; -1, 0, 0]
private def DX : InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ Mat := matrixInnerLieHom ℝ (Fin 3) X
private def DY : InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ Mat := matrixInnerLieHom ℝ (Fin 3) Y

/-- Every input matrix is off-diagonal. -/
theorem inputs_zero_diagonal (i : Fin 3) :
    X i i = 0 ∧ Y i i = 0 ∧ P i i = 0 := by
  fin_cases i <;> norm_num [X, Y, P]

/-- The two direction generators have a nonzero off-diagonal commutator. -/
theorem generator_commutator : X * Y - Y * X = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, Y, P, Matrix.mul_apply, Fin.sum_univ_three]

theorem source_directionX : (DX : Module.End ℝ Mat) P = -Y := by
  change X * P - P * X = -Y
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, Y, P, Matrix.mul_apply, Fin.sum_univ_three]

theorem source_directionY : (DY : Module.End ℝ Mat) P = X := by
  change Y * P - P * Y = X
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, Y, P, Matrix.mul_apply, Fin.sum_univ_three]

/-- Curvature of the actual native exact one-cochain equals a nonzero
matrix, even though its ordinary CE exterior derivative vanishes. -/
theorem native_exact_curvature_value :
    connectionCurvature K (exteriorDerivativeZero K P) DX DY = P := by
  rw [matrixExactOneForm_curvature, source_directionX, source_directionY,
    ← generator_commutator]
  noncomm_ring

theorem native_exact_curvature_value_ne_zero :
    connectionCurvature K (exteriorDerivativeZero K P) DX DY ≠ 0 := by
  rw [native_exact_curvature_value]
  intro h
  have hentry := congrArg (fun M : Mat => M 0 2) h
  norm_num [P] at hentry

/-- The two base derivations themselves are noncommuting operators. -/
theorem base_derivation_compositions_ne :
    (DX : Module.End ℝ Mat) * (DY : Module.End ℝ Mat) ≠
      (DY : Module.End ℝ Mat) * (DX : Module.End ℝ Mat) := by
  intro h
  have hentry := congrArg (fun T : Module.End ℝ Mat => T X 1 2) h
  change (X * (Y * X - X * Y) - (Y * X - X * Y) * X) 1 2 =
    (Y * (X * X - X * X) - (X * X - X * X) * Y) 1 2 at hentry
  norm_num [X, Y, Matrix.mul_apply, Fin.sum_univ_three] at hentry

/-- The resulting curvature also has zero diagonal. -/
theorem native_exact_curvature_zero_diagonal (i : Fin 3) :
    connectionCurvature K (exteriorDerivativeZero K P) DX DY i i = 0 := by
  rw [native_exact_curvature_value]
  exact (inputs_zero_diagonal i).2.2

end InfoGeometryTests.DerivationMatrixGeometry
