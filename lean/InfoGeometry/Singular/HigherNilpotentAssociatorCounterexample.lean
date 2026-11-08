/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenroseSectorExamples
import InfoGeometry.Core.JordanAssociatorRing

/-! The native noncommuting length-three shift has commuting MP supports.
Thus nonzero square does not force a nonzero projector Jordan associator. -/
namespace InfoGeometry.Singular.MoorePenroseSectorExamples

open Matrix

theorem chain3_cube_zero : chain3 ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chain3, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem chain3_square_ne_zero : chain3 * chain3 ≠ 0 := by
  intro hz
  have he := congrArg (fun C : Matrix (Fin 3) (Fin 3) ℝ => C 0 2) hz
  norm_num [chain3, Matrix.mul_apply, Fin.sum_univ_succ] at he

theorem chain3_supports_commute :
    (chain3 * chain3.transpose) * (chain3.transpose * chain3) =
      (chain3.transpose * chain3) * (chain3 * chain3.transpose) := by
  rw [chain3_supports.1, chain3_supports.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]

/-- The exact replacement for the naive implication from nilpotency to a
nonzero support associator: vanishing for every middle input is equivalent to
commutation of the two support idempotents. -/
theorem chain3_support_associator_zero_iff :
    (∀ z : Matrix (Fin 3) (Fin 3) ℝ,
      let p := chain3 * chain3.transpose
      let q := chain3.transpose * chain3
      ((p * z + z * p) * q + q * (p * z + z * p)) -
        (p * (z * q + q * z) + (z * q + q * z) * p) = 0) ↔
      (chain3 * chain3.transpose) * (chain3.transpose * chain3) =
        (chain3.transpose * chain3) * (chain3 * chain3.transpose) := by
  let p := chain3 * chain3.transpose
  let q := chain3.transpose * chain3
  have hp : p * p = p := by
    change (chain3 * chain3.transpose) * (chain3 * chain3.transpose) =
      chain3 * chain3.transpose
    rw [chain3_supports.1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ]
  simpa [p, q] using
    (InfoGeometry.Core.JordanAssociator.idempotent_all_associators_zero_iff hp)

/-- Every middle input gives zero support associator; the iff above explains
that this comes from commuting supports, independently of chain length. -/
theorem chain3_support_associator_zero (z : Matrix (Fin 3) (Fin 3) ℝ) :
    let p := chain3 * chain3.transpose
    let q := chain3.transpose * chain3
    ((p * z + z * p) * q + q * (p * z + z * p)) -
      (p * (z * q + q * z) + (z * q + q * z) * p) = 0 := by
  dsimp
  rw [InfoGeometry.Core.JordanAssociator.symm_associator_eq_double_commutator,
    chain3_supports_commute, sub_self, mul_zero, zero_mul, sub_self]

#print axioms chain3_support_associator_zero
#print axioms InfoGeometry.Core.JordanAssociator.idempotent_double_commutator_zero_iff

end InfoGeometry.Singular.MoorePenroseSectorExamples
