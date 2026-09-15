import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace InfoGeometry.Exceptional.CyclotomicNeutralBoundary

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

theorem neutral_pairing_contragredient_invariant
    {Space : Type*} [AddCommGroup Space] [Module ℝ Space]
    (change : Space ≃ₗ[ℝ] Space) (left right : PhaseSpaceCarrier Space) :
    canonicalNeutralBilin
        (change left.1, left.2.comp change.symm.toLinearMap)
        (change right.1, right.2.comp change.symm.toLinearMap) =
      canonicalNeutralBilin left right := by
  simp

theorem para_twisted_self_pairing_zero
    {Space : Type*} [AddCommGroup Space] [Module ℝ Space]
    (vector : PhaseSpaceCarrier Space) :
    canonicalNeutralBilin vector (neutralParaInvolution vector) = 0 := by
  simp

theorem trace_discriminant_trichotomy (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace matrix ^ 2 - 4 < 0 ∨
    Matrix.trace matrix ^ 2 - 4 = 0 ∨
    0 < Matrix.trace matrix ^ 2 - 4 :=
  lt_trichotomy (Matrix.trace matrix ^ 2 - 4) 0

theorem negative_discriminant_iff (trace : ℝ) :
    trace ^ 2 - 4 < 0 ↔ |trace| < 2 := by
  rw [abs_lt]
  constructor
  · intro negative
    constructor <;> nlinarith [sq_nonneg (trace - 2), sq_nonneg (trace + 2)]
  · rintro ⟨lower, upper⟩
    nlinarith [mul_pos (show 0 < trace + 2 by linarith)
      (show 0 < 2 - trace by linarith)]

theorem zero_discriminant_iff (trace : ℝ) :
    trace ^ 2 - 4 = 0 ↔ trace = 2 ∨ trace = -2 := by
  constructor
  · intro vanishes
    have product_zero : (trace - 2) * (trace + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp product_zero with positive | negative
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

theorem positive_discriminant_iff (trace : ℝ) :
    0 < trace ^ 2 - 4 ↔ 2 < |trace| := by
  have square : |trace| ^ 2 = trace ^ 2 := sq_abs trace
  have nonnegative : 0 ≤ |trace| := abs_nonneg trace
  constructor <;> intro comparison <;> nlinarith

theorem real_elliptic_not_necessarily_period_twelve :
    ∃ matrix : Matrix (Fin 2) (Fin 2) ℝ,
      matrix.det = 1 ∧ Matrix.trace matrix ^ 2 - 4 < 0 ∧ matrix ^ 12 ≠ 1 := by
  refine ⟨!![0, -1; 1, 1 / 2], ?_, ?_, ?_⟩
  · norm_num [Matrix.det_fin_two]
  · norm_num [Matrix.trace, Fin.sum_univ_two]
  · intro periodic
    have entry := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix 0 1) periodic
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at entry

theorem square_root_three_discriminant :
    (Real.sqrt 3) ^ 2 - 4 = -1 := by
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

end InfoGeometry.Exceptional.CyclotomicNeutralBoundary
