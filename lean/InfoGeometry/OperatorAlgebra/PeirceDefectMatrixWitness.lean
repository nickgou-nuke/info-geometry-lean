/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# A noncommuting matrix witness for the Peirce defect bridge

The example lives in the full matrix algebra `M₂(ℚ)`.  The cut is a
nontrivial idempotent and the state has nonzero entries in both off-diagonal
corners; its pinching defect is therefore nonzero.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceDefectMatrixWitness

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian

abbrev Op := Matrix (Fin 2) (Fin 2) ℚ

/-- The coordinate cut onto the first summand of the two-site module. -/
def cut : Op := !![1, 0; 0, 0]

/-- A self-adjoint idempotent with coherence across the cut. -/
def state : Op := !![(1 : ℚ) / 2, 1 / 2; 1 / 2, 1 / 2]

/-- The cut is idempotent. -/
theorem cut_idempotent : cut * cut = cut := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cut, Matrix.mul_apply, Fin.sum_univ_two]

/-- The full matrix state is idempotent. -/
theorem state_idempotent : state * state = state := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [state, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix state is self-adjoint under the standard matrix star operation. -/
theorem state_selfAdjoint : star state = state := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [state]

/-- The state fails to commute with the cut, witnessed by its `(0,1)` entry. -/
theorem cut_state_noncommute : comm cut state ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Op => M 0 1) h
  norm_num [PeirceSpine.comm, cut, state, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Direct multiplication-order witness for noncommutativity of the cut and
the state operator. -/
theorem cut_state_mul_ne_swap : cut * state ≠ state * cut := by
  intro h
  apply cut_state_noncommute
  unfold PeirceSpine.comm
  rw [h]
  simp

/-- The quadratic boundary term is one quarter of the identity matrix. -/
theorem boundary_metric_value : genV cut state state = (1 / 4 : ℚ) • (1 : Op) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genV, anticomm, conePlus, coneMinus, cut, state,
      Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two]

/-- The pinched state has nonzero idempotency defect, exactly the negative
of its boundary metric. This is a concrete instance of the general theorem. -/
theorem pinched_state_defect_value :
    idempotencyDefect (evenGrade cut state) = -((1 / 4 : ℚ) • (1 : Op)) := by
  rw [idempotencyDefect_evenGrade_of_idempotent cut state cut_idempotent
    state_idempotent, boundary_metric_value]

/-- The purity defect in the preceding theorem is genuinely nonzero. -/
theorem pinched_state_defect_ne_zero :
    idempotencyDefect (evenGrade cut state) ≠ 0 := by
  rw [pinched_state_defect_value]
  intro h
  have h00 := congrArg (fun M : Op => M 0 0) h
  norm_num at h00

end InfoGeometry.OperatorAlgebra.PeirceDefectMatrixWitness
