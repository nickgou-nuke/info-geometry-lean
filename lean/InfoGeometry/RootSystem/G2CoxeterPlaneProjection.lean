import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The Euclidean `G₂` double-hexagon readout

This file records the coordinate projection of the standard short and long
root representatives.  It is deliberately a finite coordinate carrier: no
claim about a Coxeter eigenspace or a planar drawing is hidden in the
definitions.
-/

namespace InfoGeometry.RootSystem.G2

noncomputable section

abbrev Euclidean3 := InfoGeometry.Algebra.FiniteSpin.Vec3R
abbrev Euclidean2 := InfoGeometry.Algebra.FiniteSpin.Vec2R

noncomputable def projection : Matrix (Fin 2) (Fin 3) ℝ :=
  !![(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹, 0;
     (Real.sqrt 6)⁻¹, (Real.sqrt 6)⁻¹, -2 * (Real.sqrt 6)⁻¹]

noncomputable def project (x : Euclidean3) : Euclidean2 := Matrix.mulVec projection x

def shortRoot : Euclidean3 := ![1, -1, 0]
def longRoot : Euclidean3 := ![2, -1, -1]

def shortRootAt : Fin 6 → Euclidean3
  | 0 => ![1, -1, 0]
  | 1 => ![1, 0, -1]
  | 2 => ![-1, 1, 0]
  | 3 => ![-1, 0, 1]
  | 4 => ![0, 1, -1]
  | 5 => ![0, -1, 1]

def longRootAt : Fin 6 → Euclidean3
  | 0 => ![2, -1, -1]
  | 1 => ![-1, 2, -1]
  | 2 => ![-1, -1, 2]
  | 3 => ![-2, 1, 1]
  | 4 => ![1, -2, 1]
  | 5 => ![1, 1, -2]

theorem shortRootAt_injective : Function.Injective shortRootAt := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [shortRootAt] at h ⊢ <;>
      norm_num at h

theorem longRootAt_injective : Function.Injective longRootAt := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [longRootAt] at h ⊢ <;>
      norm_num at h

theorem shortRootAt_zero_sum (i : Fin 6) :
    ∑ j : Fin 3, shortRootAt i j = 0 := by
  fin_cases i <;>
    norm_num [shortRootAt, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem longRootAt_zero_sum (i : Fin 6) :
    ∑ j : Fin 3, longRootAt i j = 0 := by
  fin_cases i <;>
    norm_num [longRootAt, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem shortRootAt_squared_norm (i : Fin 6) :
    ∑ j : Fin 3, shortRootAt i j * shortRootAt i j = 2 := by
  fin_cases i <;>
    norm_num [shortRootAt, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem longRootAt_squared_norm (i : Fin 6) :
    ∑ j : Fin 3, longRootAt i j * longRootAt i j = 6 := by
  fin_cases i <;>
    norm_num [longRootAt, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

theorem sqrt_six_sq : (Real.sqrt 6) ^ 2 = (6 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

theorem projection_preserves_zero_sum_squared_norm
    (x : Euclidean3) (hsum : ∑ j : Fin 3, x j = 0) :
    ∑ i : Fin 2, project x i * project x i =
      ∑ j : Fin 3, x j * x j := by
  have hx : x 2 = -(x 0 + x 1) := by
    have hsum' : x 0 + x 1 + x 2 = 0 := by
      simpa [Fin.sum_univ_three] using hsum
    linarith
  simp [project, Matrix.mulVec, projection, dotProduct, Fin.sum_univ_three]
  rw [hx]
  have h2 : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    field_simp [show Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [sqrt_two_sq]
  have h6 : ((Real.sqrt 6)⁻¹ : ℝ) ^ 2 = 1 / 6 := by
    field_simp [show Real.sqrt 6 ≠ 0 by positivity]
    nlinarith [sqrt_six_sq]
  ring_nf
  rw [h2, h6]
  ring

theorem shortRootAt_projected_squared_norm (i : Fin 6) :
    ∑ j : Fin 2, project (shortRootAt i) j * project (shortRootAt i) j = 2 := by
  rw [projection_preserves_zero_sum_squared_norm (shortRootAt i)
    (shortRootAt_zero_sum i)]
  exact shortRootAt_squared_norm i

theorem longRootAt_projected_squared_norm (i : Fin 6) :
    ∑ j : Fin 2, project (longRootAt i) j * project (longRootAt i) j = 6 := by
  rw [projection_preserves_zero_sum_squared_norm (longRootAt i)
    (longRootAt_zero_sum i)]
  exact longRootAt_squared_norm i

def shortCoxeterOrder : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 2
  | 4 => 3
  | 5 => 5

def longCoxeterOrder : Fin 6 → Fin 6
  | 0 => 0
  | 1 => 5
  | 2 => 1
  | 3 => 3
  | 4 => 2
  | 5 => 4

def shortHexagonPoint : Fin 6 → Euclidean2
  | 0 => ![Real.sqrt 2, 0]
  | 1 => ![(Real.sqrt 2)⁻¹, 3 * (Real.sqrt 6)⁻¹]
  | 2 => ![-(Real.sqrt 2)⁻¹, 3 * (Real.sqrt 6)⁻¹]
  | 3 => ![-Real.sqrt 2, 0]
  | 4 => ![-(Real.sqrt 2)⁻¹, -3 * (Real.sqrt 6)⁻¹]
  | 5 => ![(Real.sqrt 2)⁻¹, -3 * (Real.sqrt 6)⁻¹]

def longHexagonPoint : Fin 6 → Euclidean2
  | 0 => ![3 * (Real.sqrt 2)⁻¹, 3 * (Real.sqrt 6)⁻¹]
  | 1 => ![0, 6 * (Real.sqrt 6)⁻¹]
  | 2 => ![-3 * (Real.sqrt 2)⁻¹, 3 * (Real.sqrt 6)⁻¹]
  | 3 => ![-3 * (Real.sqrt 2)⁻¹, -3 * (Real.sqrt 6)⁻¹]
  | 4 => ![0, -6 * (Real.sqrt 6)⁻¹]
  | 5 => ![3 * (Real.sqrt 2)⁻¹, -3 * (Real.sqrt 6)⁻¹]

theorem shortCoxeterProjection_table (i : Fin 6) :
    project (shortRootAt (shortCoxeterOrder i)) = shortHexagonPoint i := by
  have h2 : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
    field_simp [show Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [sqrt_two_sq]
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [project, shortRootAt, shortCoxeterOrder, shortHexagonPoint,
      projection, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  all_goals field_simp [show Real.sqrt 2 ≠ 0 by positivity]
  all_goals nlinarith [sqrt_two_sq]

theorem longCoxeterProjection_table (i : Fin 6) :
    project (longRootAt (longCoxeterOrder i)) = longHexagonPoint i := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [project, longRootAt, longCoxeterOrder, longHexagonPoint,
      projection, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

theorem projection_row_zero_unit :
    ∑ j : Fin 3, projection 0 j * projection 0 j = 1 := by
  simp [projection, Fin.sum_univ_three]
  field_simp [show Real.sqrt 2 ≠ 0 by positivity]
  nlinarith [sqrt_two_sq]

theorem projection_row_one_unit :
    ∑ j : Fin 3, projection 1 j * projection 1 j = 1 := by
  simp [projection, Fin.sum_univ_three]
  field_simp [show Real.sqrt 6 ≠ 0 by positivity]
  nlinarith [sqrt_six_sq]

theorem projection_rows_orthogonal :
    ∑ j : Fin 3, projection 0 j * projection 1 j = 0 := by
  simp [projection, Fin.sum_univ_three]

theorem shortRoot_projection :
    project shortRoot = ![Real.sqrt 2, 0] := by
  funext i
  fin_cases i
  · simp [project, shortRoot, projection, dotProduct, Fin.sum_univ_three]
    field_simp [show Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [sqrt_two_sq]
  · simp [project, shortRoot, projection, dotProduct, Fin.sum_univ_three]

theorem longRoot_projection :
    project longRoot =
      ![(3 : ℝ) / Real.sqrt 2, (3 : ℝ) / Real.sqrt 6] := by
  funext i
  fin_cases i
  · simp [project, longRoot, projection, dotProduct, Fin.sum_univ_three]
    field_simp [show Real.sqrt 2 ≠ 0 by positivity]
    ring
  · simp [project, longRoot, projection, dotProduct, Fin.sum_univ_three]
    field_simp [show Real.sqrt 6 ≠ 0 by positivity]
    ring

theorem shortRoot_projection_norm_sq :
    (project shortRoot 0) ^ 2 + (project shortRoot 1) ^ 2 = 2 := by
  rw [shortRoot_projection]
  change (Real.sqrt 2) ^ 2 + 0 ^ 2 = 2
  simpa using sqrt_two_sq

theorem longRoot_projection_norm_sq :
    (project longRoot 0) ^ 2 + (project longRoot 1) ^ 2 = 6 := by
  rw [longRoot_projection]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := sqrt_two_sq
  have hs6 : (Real.sqrt 6) ^ 2 = (6 : ℝ) := sqrt_six_sq
  field_simp [show Real.sqrt 2 ≠ 0 by positivity]
  field_simp [show Real.sqrt 6 ≠ 0 by positivity]
  nlinarith

theorem projection_radius_sq_ratio :
    (∑ i : Fin 2, (project longRoot i) * (project longRoot i)) =
      3 * (∑ i : Fin 2, (project shortRoot i) * (project shortRoot i)) := by
  simpa [Fin.sum_univ_two, pow_two] using
    (show (project longRoot 0) ^ 2 + (project longRoot 1) ^ 2 =
      3 * ((project shortRoot 0) ^ 2 + (project shortRoot 1) ^ 2) by
      rw [longRoot_projection_norm_sq, shortRoot_projection_norm_sq]
      norm_num)

theorem shortHexagonPoint_squared_norm (i : Fin 6) :
    ∑ j : Fin 2, shortHexagonPoint i j * shortHexagonPoint i j = 2 := by
  fin_cases i <;>
    simp [shortHexagonPoint, Fin.sum_univ_two, pow_two]
  all_goals field_simp [show Real.sqrt 2 ≠ 0 by positivity,
    show Real.sqrt 6 ≠ 0 by positivity]
  all_goals nlinarith [sqrt_two_sq, sqrt_six_sq]

theorem longHexagonPoint_squared_norm (i : Fin 6) :
    ∑ j : Fin 2, longHexagonPoint i j * longHexagonPoint i j = 6 := by
  fin_cases i <;>
    simp [longHexagonPoint, Fin.sum_univ_two, pow_two]
  all_goals field_simp [show Real.sqrt 2 ≠ 0 by positivity,
    show Real.sqrt 6 ≠ 0 by positivity]
  all_goals nlinarith [sqrt_two_sq, sqrt_six_sq]

theorem hexagon_radius_sq_ratio (i j : Fin 6) :
    (∑ k : Fin 2, longHexagonPoint i k * longHexagonPoint i k) =
      3 * (∑ k : Fin 2, shortHexagonPoint j k * shortHexagonPoint j k) := by
  rw [longHexagonPoint_squared_norm, shortHexagonPoint_squared_norm]
  norm_num

end

end InfoGeometry.RootSystem.G2
