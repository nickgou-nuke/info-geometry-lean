/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.OperatorExtensionExamples
import InfoGeometry.OperatorAlgebra.PeircePairExamples
import InfoGeometry.OperatorAlgebra.MatrixLieJordanOperators
import InfoGeometry.OperatorAlgebra.PeirceGradedTraceGeometry
import InfoGeometry.OperatorAlgebra.PeirceInnerAction

/-!
# Noncommuting witnesses for the superoperator corrections

The existing nondiagonal projections give noncommuting opposite corners.
They witness the missing mixed-composition defect and the nonvanishing of
ordinary repeated Lie and Jordan action. A further full nondiagonal input
has a strictly negative quadratic trace for the commutator by a positive
matrix. All coordinate calculations certify statements about full operators.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorSuperoperatorExamples

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.IdempotentCartan
open InfoGeometry.Core.JordanMultiplicationClosure
open OperatorExtensionExamples PeirceChiralGeometry MatrixLieJordanOperators
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The adjoint corner is obtained from the already-checked forward matrix. -/
theorem component01_P_Q_matrix : component01 P Q =
    !![80 / 729, 160 / 729, 160 / 729;
       -56 / 729, -112 / 729, -112 / 729;
       16 / 729, 32 / 729, 32 / 729] := by
  have h : star (component10 P Q) = component01 P Q := by
    rw [star_component10 P_isStarProjection.isSelfAdjoint,
      Q_isStarProjection.isSelfAdjoint.star_eq]
  rw [← h, component10_P_Q]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.star_apply]

/-- The omitted defect is nonzero at a nondiagonal projection input. -/
theorem mixed_difference_defect_entry :
    ((⁅component10 P Q, component01 P Q * P + P * component01 P Q⁆ -
        ⁅component01 P Q, component10 P Q * P + P * component10 P Q⁆) -
      (⁅component10 P Q, component01 P Q⁆ * P +
        P * ⁅component10 P Q, component01 P Q⁆)) 0 0 = (-12800 / 59049 : ℂ) := by
  have h := congrArg
    (fun f : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) => f P)
    (ad_jordan_sub_swap (component10 P Q) (component01 P Q))
  change ⁅component10 P Q, component01 P Q * P + P * component01 P Q⁆ -
      ⁅component01 P Q, component10 P Q * P + P * component10 P Q⁆ =
    (⁅component10 P Q, component01 P Q⁆ * P + P * ⁅component10 P Q, component01 P Q⁆) +
      (2 : ℂ) • (component10 P Q * P * component01 P Q -
        component01 P Q * P * component10 P Q) at h
  have hu : component10 P Q * P = 0 := by
    change P * Q * (1 - P) * P = 0
    rw [mul_assoc, sub_mul, one_mul, P_isStarProjection.isIdempotentElem.eq,
      sub_self, mul_zero]
  have hv : component01 P Q * P = component01 P Q :=
    peirceCorner_absorb_right P_isStarProjection.isIdempotentElem.eq
  rw [h, add_sub_cancel_left, hu, hv, zero_mul, zero_sub,
    component10_P_Q, component01_P_Q_matrix]
  norm_num [two_smul, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mixed_difference_not_jordan_lie :
    ⁅component10 P Q, component01 P Q * P + P * component01 P Q⁆ -
        ⁅component01 P Q, component10 P Q * P + P * component10 P Q⁆ ≠
      ⁅component10 P Q, component01 P Q⁆ * P + P * ⁅component10 P Q, component01 P Q⁆ := by
  intro h
  have he := mixed_difference_defect_entry
  rw [h, sub_self] at he
  norm_num at he

/-- Even an odd square-zero input does not annihilate the ordinary Lie square. -/
theorem ordinary_lie_square_entry :
    (⁅component10 P Q, ⁅component10 P Q, component01 P Q⁆⁆) 0 0 =
      (-174080 / 4782969 : ℂ) := by
  have h := congrArg
    (fun f : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) => f (component01 P Q))
    (ad_mul_self_of_mul_self_eq_zero
      (corners_square_zero P_isStarProjection.isIdempotentElem.eq Q).1)
  change ⁅component10 P Q, ⁅component10 P Q, component01 P Q⁆⁆ =
    -((2 : ℂ) • (component10 P Q * component01 P Q * component10 P Q)) at h
  rw [h, component10_P_Q, component01_P_Q_matrix]
  norm_num [two_smul, Matrix.mul_apply, Fin.sum_univ_succ]

theorem ordinary_lie_square_ne_zero :
    ⁅component10 P Q, ⁅component10 P Q, component01 P Q⁆⁆ ≠ 0 := by
  intro h
  have he := ordinary_lie_square_entry
  rw [h] at he
  norm_num at he

theorem ordinary_jordan_square_entry :
    (jordanLeft (R := ℂ) (component10 P Q)
      (jordanLeft (R := ℂ) (component10 P Q) (component01 P Q))) 0 0 =
        (174080 / 4782969 : ℂ) := by
  have h := congrArg
    (fun f : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ) => f (component01 P Q))
    (jordan_mul_self_of_mul_self_eq_zero
      (corners_square_zero P_isStarProjection.isIdempotentElem.eq Q).1)
  change jordanLeft (R := ℂ) (component10 P Q)
      (jordanLeft (R := ℂ) (component10 P Q) (component01 P Q)) =
    (2 : ℂ) • (component10 P Q * component01 P Q * component10 P Q) at h
  rw [h, component10_P_Q, component01_P_Q_matrix]
  norm_num [two_smul, Matrix.mul_apply, Fin.sum_univ_succ]

theorem ordinary_jordan_square_ne_zero :
    jordanLeft (R := ℂ) (component10 P Q)
      (jordanLeft (R := ℂ) (component10 P Q) (component01 P Q)) ≠ 0 := by
  intro h
  have he := ordinary_jordan_square_entry
  rw [h] at he
  norm_num at he

/-- The positive square annihilates this full nondiagonal matrix on the left. -/
theorem chiral_square_mul_dense :
    (oddPart P Q * oddPart P Q) * !![2, 4, 4; 2, 4, 4; -3, -6, -6] = 0 := by
  rw [chiral_square_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Its right action on the same matrix is nonzero. -/
theorem dense_mul_chiral_square :
    !![2, 4, 4; 2, 4, 4; -3, -6, -6] * (oddPart P Q * oddPart P Q) =
      (1088 / 6561 : ℂ) • !![2, 4, 4; 2, 4, 4; -3, -6, -6] := by
  rw [chiral_square_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The commutator by a positive matrix can have a negative quadratic trace. -/
theorem dense_trace_lie :
    trace (star (!![2, 4, 4; 2, 4, 4; -3, -6, -6] : Matrix (Fin 3) (Fin 3) ℂ) *
      ⁅oddPart P Q * oddPart P Q, !![2, 4, 4; 2, 4, 4; -3, -6, -6]⁆) =
        (-18496 / 729 : ℂ) := by
  rw [Ring.lie_def, chiral_square_mul_dense, dense_mul_chiral_square,
    zero_sub, mul_neg, mul_smul_comm, trace_neg, trace_smul]
  norm_num [Matrix.trace, Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_succ,
    map_ofNat]

/-- Thus the commutator action cannot be substituted for the positive Jordan action. -/
theorem dense_trace_lie_not_nonneg :
    ¬ 0 ≤ trace (star (!![2, 4, 4; 2, 4, 4; -3, -6, -6] : Matrix (Fin 3) (Fin 3) ℂ) *
      ⁅oddPart P Q * oddPart P Q, !![2, 4, 4; 2, 4, 4; -3, -6, -6]⁆) := by
  rw [dense_trace_lie]
  intro h
  have hre := (Complex.nonneg_iff.mp h).1
  norm_num at hre

end InfoGeometry.OperatorAlgebra.OperatorSuperoperatorExamples
