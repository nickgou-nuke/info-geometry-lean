/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGeometry.EulerDerivationCriterion
import InfoGeometry.OperatorAlgebra.NoncommutativeOperatorFiveGrade

namespace InfoGeometry.OperatorAlgebra

open _root_.InfoGeometry.OperatorAlgebra.ExteriorAlgebra

private abbrev M := Matrix (Fin 2) (Fin 2) ℝ
private def H : M := !![1, 0; 0, 0]
private def Y : M := !![0, 1; 1, 0]
private def Z : M := !![0, -1; 1, 0]

theorem weightedDerivation_matrix_noncommutative : H * Y ≠ Y * H := by
  intro h
  have h01 := congrArg (fun a : M => a 0 1) h
  norm_num [H, Y, Matrix.mul_apply, Fin.sum_univ_two] at h01

-- The image contains a right-invertible element in a genuinely noncommuting algebra.
example : innerOperatorDerivation H Y * Z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [innerOperatorDerivation_apply, H, Y, Z, Matrix.mul_apply,
      Fin.sum_univ_two]

example : ∀ x y : M,
    (1 : M) * innerOperatorDerivation H (x * y) =
      (1 * innerOperatorDerivation H x) * y + x * (1 * innerOperatorDerivation H y) := by
  intro x y
  simp only [one_mul, (innerOperatorDerivation H).leibniz]

-- A noncentral weight really fails the Leibniz law, rather than merely lacking a proof.
example : ¬ ∀ x y : M,
    H * innerOperatorDerivation H (x * y) =
      (H * innerOperatorDerivation H x) * y + x * (H * innerOperatorDerivation H y) := by
  intro h
  have hYY := congrArg (fun a : M => a 0 0) (h Y Y)
  norm_num [innerOperatorDerivation_apply, H, Y, Matrix.mul_apply,
    Fin.sum_univ_two] at hYY

#print axioms OpDerivation.left_weight_leibniz_iff
#print axioms OpDerivation.left_weight_leibniz_iff_central
#print axioms OpDerivation.leftWeighted
#print axioms OpDerivation.leftWeighted_apply
#print axioms InfoGeometry.QuantumGeometry.BerryKeating.opEuler_leibniz_iff_central
#print axioms weightedDerivation_matrix_noncommutative

end InfoGeometry.OperatorAlgebra
