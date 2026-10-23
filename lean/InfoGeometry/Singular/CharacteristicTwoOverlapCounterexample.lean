/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Core.IdempotentSymmetricOverlap
import Mathlib

/-! A noncommuting MP pair of nilpotency index three whose symmetric
support overlap vanishes in characteristic two. -/
namespace InfoGeometry.Singular.CharacteristicTwoOverlapCounterexample
open Matrix MoorePenrose

local instance : StarRing (ZMod 2) := starRingOfComm
local instance : TrivialStar (ZMod 2) := ⟨fun _ => rfl⟩

def shift : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
def backward : Matrix (Fin 3) (Fin 3) (ZMod 2) := shift.transpose

theorem penrose_pair : IsMoorePenroseInverse shift backward := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [shift, backward, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, star_trivial]

theorem pair_noncommuting : shift * backward ≠ backward * shift := by
  intro h
  have he := congrArg (fun C : Matrix (Fin 3) (Fin 3) (ZMod 2) => C 0 0) h
  norm_num [shift, backward, Matrix.mul_apply, Fin.sum_univ_succ] at he

theorem shift_cube_zero : shift ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shift, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem shift_square_nonzero : shift * shift ≠ 0 := by
  intro h
  have he := congrArg (fun C : Matrix (Fin 3) (Fin 3) (ZMod 2) => C 0 2) h
  norm_num [shift, Matrix.mul_apply, Fin.sum_univ_succ] at he

theorem symmetric_support_overlap_zero :
    (shift * backward) * (backward * shift) +
      (backward * shift) * (shift * backward) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shift, backward, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Fin.sum_univ_succ]
  decide

#print axioms penrose_pair
#print axioms symmetric_support_overlap_zero
#print axioms InfoGeometry.Core.IdempotentSymmetricOverlap.symmetric_overlap_zero_iff

end InfoGeometry.Singular.CharacteristicTwoOverlapCounterexample
