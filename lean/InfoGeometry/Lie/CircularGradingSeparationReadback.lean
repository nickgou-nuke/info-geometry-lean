import InfoGeometry.Lie.SplitOctonionCircularAxialGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow

noncomputable section

namespace InfoGeometry.Lie.CircularGradingSeparationReadback

open InfoGeometry.Lie.SplitOctonionCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

theorem axialWeight_mem_three_values (i : Fin 8) :
    axialWeight i = -1 ∨ axialWeight i = 0 ∨ axialWeight i = 1 := by
  fin_cases i <;> simp [axialWeight]

theorem axialWeight_sq_eq_zero_or_one (i : Fin 8) :
    axialWeight i ^ 2 = 0 ∨ axialWeight i ^ 2 = 1 := by
  rcases axialWeight_mem_three_values i with h | h | h
  · right
    rw [h]
    norm_num
  · left
    rw [h]
    norm_num
  · right
    rw [h]
    norm_num

theorem circular_basis_has_distinct_cartan_weights (i : Fin 8) :
    axialGrading (circularPeirceBasis i) =
      axialWeight i • circularPeirceBasis i :=
  axialGrading_basis i

theorem axialWeight_opposite_sheet (i : Fin 4) :
    axialWeight ⟨i.val + 4, by omega⟩ =
      -axialWeight ⟨i.val, by omega⟩ := by
  fin_cases i <;> norm_num [axialWeight]

theorem opposite_sheet_flow_factors_multiply_to_one (t : ℝ) (i : Fin 4) :
    Real.exp (t * axialWeight ⟨i.val, by omega⟩) *
        Real.exp (t * axialWeight ⟨i.val + 4, by omega⟩) = 1 := by
  rw [axialWeight_opposite_sheet]
  rw [show t * -axialWeight ⟨i.val, by omega⟩ =
      -(t * axialWeight ⟨i.val, by omega⟩) by ring]
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem zero_weight_flow_factor (t : ℝ) (i : Fin 2) :
    Real.exp (t * axialWeight ⟨4 * i.val, by omega⟩) = 1 := by
  fin_cases i <;> norm_num [axialWeight]

theorem axialWeight_signed_readout :
    axialWeight (1 : Fin 8) = 1 ∧
      axialWeight (5 : Fin 8) = -1 ∧
      axialWeight (1 : Fin 8) ≠ axialWeight (5 : Fin 8) := by
  norm_num [axialWeight]

end InfoGeometry.Lie.CircularGradingSeparationReadback
