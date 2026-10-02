import InfoGeometry.Synthesis.CuntzKleinPropagation

noncomputable section

namespace InfoGeometry.Synthesis.CuntzDoubledHopping

open InfoGeometry.Topology.CantorBoundaryCuntzO2
open InfoGeometry.Topology.CantorBoundaryRealClockShift
open InfoGeometry.Synthesis.CuntzKleinPropagation

def corner (operator : BoundaryOperator ℝ) (row column : Fin 2) : BoundaryOperator ℝ :=
  S row * operator * T column

theorem corner_one (row column : Fin 2) : corner 1 row column = matrixUnit row column := by
  simp only [corner, matrixUnit, mul_one]

theorem corner_mul (first second : BoundaryOperator ℝ) (row middle next column : Fin 2) :
    corner first row middle * corner second next column =
      if middle = next then corner (first * second) row column else 0 := by
  unfold corner
  calc
    S row * first * T middle * (S next * second * T column) =
        S row * first * (T middle * S next) * second * T column := by
      simp only [mul_assoc]
    _ = if middle = next then S row * (first * second) * T column else 0 := by
      rw [ortho]
      split <;> simp [mul_assoc]

theorem corner_readout (operator : BoundaryOperator ℝ) (row column left right : Fin 2) :
    T row * corner operator left right * S column =
      if row = left ∧ right = column then operator else 0 := by
  have regroup : T row * corner operator left right * S column =
      (T row * S left) * operator * (T right * S column) := by
    simp only [corner, mul_assoc]
  rw [regroup, ortho, ortho]
  by_cases first : row = left <;> by_cases second : right = column <;> simp [first, second]

def doubledDifference : BoundaryOperator ℝ :=
  corner branchDifference 0 1 + corner branchDifference 1 0

theorem doubledDifference_readout : T 0 * doubledDifference * S 1 = branchDifference := by
  simp [doubledDifference, mul_add, add_mul, corner_readout]

theorem doubledDifference_anticommutes_clock :
    doubledDifference * clock = -(clock * doubledDifference) := by
  simp only [doubledDifference, clock, ← corner_one, add_mul, mul_add, sub_mul, mul_sub]
  simp [corner_mul] <;> abel

theorem doubledDifference_commutes_shift : Commute shift doubledDifference := by
  change shift * doubledDifference = doubledDifference * shift
  simp only [doubledDifference, shift, ← corner_one, add_mul, mul_add]
  simp [corner_mul] <;> abel

theorem doubledDifference_square :
    doubledDifference * doubledDifference =
      corner (branchDifference * branchDifference) 0 0 +
        corner (branchDifference * branchDifference) 1 1 := by
  simp [doubledDifference, add_mul, mul_add, corner_mul]

end InfoGeometry.Synthesis.CuntzDoubledHopping
