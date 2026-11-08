/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveDoubleShear
import InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability

namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows
open GrassmannianBundleCyclotomicOrientability

example : matD * matB ≠ matB * matD :=
  mat2Z_noncommutative_cyclotomic_witness.1

example : doubleShear matD matB * doubleShear matD matB =
    (!![-1, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [doubleShear, matD, matB, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat2_wrong_doubleShear_square :
    doubleShear matD matB * doubleShear matD matB ≠
      complement matD matB + matD - matB - matB * matD := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  norm_num [doubleShear, complement, support, matD, matB,
    Matrix.mul_apply, Fin.sum_univ_two] at he

#print axioms doubleShear_square
#print axioms doubleShear_wrong_square_iff
#print axioms mat2_wrong_doubleShear_square

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
