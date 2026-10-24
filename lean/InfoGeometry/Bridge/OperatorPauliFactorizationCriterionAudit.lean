/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Bridge.OperatorPauliFactorizationCriterion

namespace InfoGeometry.Bridge.OperatorPauliFactorizationDefect

-- The channel is 2t-1, while u need not commute with t.
example (t u : Matrix (Fin 2) (Fin 2) ℤ) :
    operatorSigma t (1 - t) u 0 * operatorBarSigma t (1 - t) u 0 =
      diagonalBlock (orderedQuadratic t (1 - t) u 0) := by
  apply (operator_factorization_iff _ _ _ _).mpr
  constructor
  · change t * (1 - t) = (1 - t) * t
    noncomm_ring
  refine ⟨?_, ?_, ?_⟩
  · change u * 0 = 0 * u
    simp
  · change u * (t + (1 - t)) = (t + (1 - t)) * u
    noncomm_ring
  · change 0 * (t - (1 - t)) = (t - (1 - t)) * 0
    simp

example : ¬ Commute (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ)
    !![1, 0; 0, 0] := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h.eq
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at he

example :
    operatorSigma (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℤ) 0 !![0, 1; 0, 0] 0 *
      operatorBarSigma !![1, 0; 0, 0] 0 !![0, 1; 0, 0] 0 ≠
      diagonalBlock (orderedQuadratic !![1, 0; 0, 0] 0 !![0, 1; 0, 0] 0) := by
  intro h
  have hc := (operator_factorization_iff _ _ _ _).mp h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hc.2.2.1.eq
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at he

#print axioms factorizationDefect_eq_zero_iff
#print axioms operator_factorization_iff
#print axioms operator_factorization_with_defect

end InfoGeometry.Bridge.OperatorPauliFactorizationDefect
