import Mathlib

/-!
# A checked Coxeter-plane projection for the `D₄` root carrier

The repository already owns the integral `D₄` root lattice.  This file adds
only the Euclidean projection data used by the planar picture.  In
particular, it does not identify a projection with a Coxeter eigenspace
without checking the relevant linear algebra.
-/

namespace InfoGeometry.RootSystem.D4

noncomputable section

abbrev Euclidean4 := Fin 4 → ℝ
abbrev Euclidean2 := Fin 2 → ℝ

def coxeterPlaneProjection : Matrix (Fin 2) (Fin 4) ℝ :=
  !![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0, 0;
     -(Real.sqrt 6)⁻¹, (Real.sqrt 6)⁻¹, -2 * (Real.sqrt 6)⁻¹, 0]

def project (x : Euclidean4) : Euclidean2 :=
  Matrix.mulVec coxeterPlaneProjection x

def outerRoot₀ : Euclidean4 := ![1, 1, 0, 0]
def outerRoot₁ : Euclidean4 := ![0, 1, -1, 0]
def outerRoot₂ : Euclidean4 := ![1, 0, 1, 0]

def innerRoot₀ : Euclidean4 := ![1, -1, 0, 0]
def innerRoot₁ : Euclidean4 := ![0, 1, 1, 0]
def innerRoot₂ : Euclidean4 := ![1, 0, -1, 0]

/-! The complete real `D₄` root carrier.  The first twelve entries are the
roots in the first three coordinate directions; the remaining twelve are the
roots involving the fourth direction. -/

def rootAt : Fin 24 → Euclidean4
  | 0 => ![1, 1, 0, 0]
  | 1 => ![1, -1, 0, 0]
  | 2 => ![-1, 1, 0, 0]
  | 3 => ![-1, -1, 0, 0]
  | 4 => ![1, 0, 1, 0]
  | 5 => ![1, 0, -1, 0]
  | 6 => ![-1, 0, 1, 0]
  | 7 => ![-1, 0, -1, 0]
  | 8 => ![0, 1, 1, 0]
  | 9 => ![0, 1, -1, 0]
  | 10 => ![0, -1, 1, 0]
  | 11 => ![0, -1, -1, 0]
  | 12 => ![1, 0, 0, 1]
  | 13 => ![1, 0, 0, -1]
  | 14 => ![-1, 0, 0, 1]
  | 15 => ![-1, 0, 0, -1]
  | 16 => ![0, 1, 0, 1]
  | 17 => ![0, 1, 0, -1]
  | 18 => ![0, -1, 0, 1]
  | 19 => ![0, -1, 0, -1]
  | 20 => ![0, 0, 1, 1]
  | 21 => ![0, 0, 1, -1]
  | 22 => ![0, 0, -1, 1]
  | 23 => ![0, 0, -1, -1]
  | _ => ![0, 0, 0, 0]

theorem rootAt_injective : Function.Injective rootAt := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [rootAt] at h ⊢ <;>
    norm_num at h

theorem rootAt_squared_norm (i : Fin 24) :
    ∑ j : Fin 4, rootAt i j * rootAt i j = 2 := by
  fin_cases i <;>
    norm_num [rootAt, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

def outerHexagonPoint : Fin 6 → Euclidean2
  | 0 => ![Real.sqrt 2, 0]
  | 1 => ![(Real.sqrt 2)⁻¹, 3 * (Real.sqrt 6)⁻¹]
  | 2 => ![-(Real.sqrt 2)⁻¹, 3 * (Real.sqrt 6)⁻¹]
  | 3 => ![-Real.sqrt 2, 0]
  | 4 => ![-(Real.sqrt 2)⁻¹, -3 * (Real.sqrt 6)⁻¹]
  | 5 => ![(Real.sqrt 2)⁻¹, -3 * (Real.sqrt 6)⁻¹]

def innerHexagonPoint : Fin 6 → Euclidean2
  | 0 => ![0, -(2 * (Real.sqrt 6)⁻¹)]
  | 1 => ![(Real.sqrt 2)⁻¹, (Real.sqrt 6)⁻¹]
  | 2 => ![(Real.sqrt 2)⁻¹, -(Real.sqrt 6)⁻¹]
  | 3 => ![0, 2 * (Real.sqrt 6)⁻¹]
  | 4 => ![-(Real.sqrt 2)⁻¹, -(Real.sqrt 6)⁻¹]
  | 5 => ![-(Real.sqrt 2)⁻¹, (Real.sqrt 6)⁻¹]

def rootProjectionTarget : Fin 24 → Euclidean2
  | 0 => outerHexagonPoint 0
  | 1 => innerHexagonPoint 0
  | 2 => innerHexagonPoint 3
  | 3 => outerHexagonPoint 3
  | 4 => outerHexagonPoint 5
  | 5 => innerHexagonPoint 1
  | 6 => innerHexagonPoint 4
  | 7 => outerHexagonPoint 2
  | 8 => innerHexagonPoint 2
  | 9 => outerHexagonPoint 1
  | 10 => outerHexagonPoint 4
  | 11 => innerHexagonPoint 5
  | 12 => innerHexagonPoint 2
  | 13 => innerHexagonPoint 2
  | 14 => innerHexagonPoint 5
  | 15 => innerHexagonPoint 5
  | 16 => innerHexagonPoint 1
  | 17 => innerHexagonPoint 1
  | 18 => innerHexagonPoint 4
  | 19 => innerHexagonPoint 4
  | 20 => innerHexagonPoint 0
  | 21 => innerHexagonPoint 0
  | 22 => innerHexagonPoint 3
  | 23 => innerHexagonPoint 3
  | _ => ![0, 0]

theorem rootAt_projection_table (i : Fin 24) :
    project (rootAt i) = rootProjectionTarget i := by
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have hs6 : (Real.sqrt 6) ^ 2 = (6 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [project, Matrix.mulVec, rootAt, rootProjectionTarget,
      outerHexagonPoint, innerHexagonPoint, coxeterPlaneProjection,
      dotProduct, Fin.sum_univ_four]
  all_goals field_simp [show Real.sqrt 2 ≠ 0 by positivity,
    show Real.sqrt 6 ≠ 0 by positivity]
  all_goals nlinarith [hs2, hs6]

theorem rootAt_projected_squared_norm (i : Fin 24) :
    ∑ j : Fin 2, project (rootAt i) j * project (rootAt i) j =
      (if i = 0 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 9 ∨ i = 10 then
        (2 : ℝ) else 2 / 3) := by
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have hs6 : (Real.sqrt 6) ^ 2 = (6 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  rw [rootAt_projection_table]
  fin_cases i <;>
    simp [rootProjectionTarget, outerHexagonPoint, innerHexagonPoint,
      Fin.sum_univ_two, pow_two]
  all_goals field_simp [show Real.sqrt 2 ≠ 0 by positivity,
    show Real.sqrt 6 ≠ 0 by positivity]
  all_goals nlinarith [hs2, hs6]

/-! The projection table separates the six outer entries from the eighteen
inner entries.  These finite index carriers make the multiplicity statement
explicit without asserting an unproved Coxeter-orbit decomposition. -/

def outerRootIndices : Finset (Fin 24) :=
  {0, 3, 4, 7, 9, 10}

def innerRootIndices : Finset (Fin 24) :=
  Finset.univ \ outerRootIndices

@[simp] theorem outerRootIndices_card : outerRootIndices.card = 6 := by
  decide

@[simp] theorem innerRootIndices_card : innerRootIndices.card = 18 := by
  decide

theorem mem_outerRootIndices_iff (i : Fin 24) :
    i ∈ outerRootIndices ↔
      i = 0 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 9 ∨ i = 10 := by
  simp [outerRootIndices]

theorem projected_norm_eq_outer_of_mem (i : Fin 24)
    (hi : i ∈ outerRootIndices) :
    ∑ j : Fin 2, project (rootAt i) j * project (rootAt i) j = 2 := by
  rw [rootAt_projected_squared_norm]
  simp only [mem_outerRootIndices_iff] at hi
  simp [hi]

theorem projected_norm_eq_inner_of_mem (i : Fin 24)
    (hi : i ∈ innerRootIndices) :
    ∑ j : Fin 2, project (rootAt i) j * project (rootAt i) j = 2 / 3 := by
  rw [rootAt_projected_squared_norm]
  have hnot : ¬(i = 0 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 9 ∨ i = 10) := by
    intro houter
    have : i ∈ outerRootIndices := (mem_outerRootIndices_iff i).2 houter
    exact (Finset.mem_sdiff.mp hi).2 this
  simp [hnot]

theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

theorem sqrt_six_sq : (Real.sqrt 6) ^ 2 = (6 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

theorem coxeterPlaneProjection_row₀_unit :
    ∑ j : Fin 4, coxeterPlaneProjection 0 j * coxeterPlaneProjection 0 j = 1 := by
  simp [coxeterPlaneProjection, Fin.sum_univ_four]
  field_simp [show Real.sqrt 2 ≠ 0 by positivity]
  nlinarith [sqrt_two_sq]

theorem coxeterPlaneProjection_row₁_unit :
    ∑ j : Fin 4, coxeterPlaneProjection 1 j * coxeterPlaneProjection 1 j = 1 := by
  simp [coxeterPlaneProjection, Fin.sum_univ_four]
  field_simp [show Real.sqrt 6 ≠ 0 by positivity]
  nlinarith [sqrt_six_sq]

theorem coxeterPlaneProjection_rows_orthogonal :
    ∑ j : Fin 4, coxeterPlaneProjection 0 j * coxeterPlaneProjection 1 j = 0 := by
  simp [coxeterPlaneProjection, Fin.sum_univ_four]

theorem outerRoot₀_projection :
    project outerRoot₀ = ![Real.sqrt 2, 0] := by
  funext i
  fin_cases i <;>
  simp [project, Matrix.mulVec, outerRoot₀, coxeterPlaneProjection, dotProduct,
      Fin.sum_univ_four]
  · field_simp [show Real.sqrt 2 ≠ 0 by positivity]
    nlinarith [sqrt_two_sq]

theorem innerRoot₀_projection :
    project innerRoot₀ = ![0, -(2 * (Real.sqrt 6)⁻¹)] := by
  funext i
  fin_cases i <;>
    simp [project, Matrix.mulVec, innerRoot₀, coxeterPlaneProjection, dotProduct,
      Fin.sum_univ_four] <;> ring

theorem outerRoot₀_projection_squared_norm :
    ∑ i : Fin 2, (project outerRoot₀ i) * (project outerRoot₀ i) = 2 := by
  rw [outerRoot₀_projection]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, zero_mul, mul_zero, add_zero]
  simpa [pow_two] using sqrt_two_sq

theorem innerRoot₀_projection_squared_norm :
    ∑ i : Fin 2, (project innerRoot₀ i) * (project innerRoot₀ i) = 2 / 3 := by
  rw [innerRoot₀_projection]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, zero_mul, mul_zero, zero_add]
  have hs6 : (Real.sqrt 6) ^ 2 = (6 : ℝ) := sqrt_six_sq
  field_simp [show Real.sqrt 6 ≠ 0 by positivity]
  nlinarith

theorem projection_radius_sq_ratio :
    (∑ i : Fin 2, (project outerRoot₀ i) * (project outerRoot₀ i)) =
      3 * (∑ i : Fin 2, (project innerRoot₀ i) * (project innerRoot₀ i)) := by
  rw [outerRoot₀_projection_squared_norm, innerRoot₀_projection_squared_norm]
  norm_num

theorem outerHexagonPoint_squared_norm (i : Fin 6) :
    ∑ j : Fin 2, outerHexagonPoint i j * outerHexagonPoint i j = 2 := by
  fin_cases i <;>
    simp [outerHexagonPoint, Fin.sum_univ_two, pow_two]
  all_goals field_simp [show Real.sqrt 2 ≠ 0 by positivity,
    show Real.sqrt 6 ≠ 0 by positivity]
  all_goals nlinarith [sqrt_two_sq, sqrt_six_sq]

theorem innerHexagonPoint_squared_norm (i : Fin 6) :
    ∑ j : Fin 2, innerHexagonPoint i j * innerHexagonPoint i j = 2 / 3 := by
  fin_cases i <;>
    simp [innerHexagonPoint, Fin.sum_univ_two, pow_two]
  all_goals field_simp [show Real.sqrt 2 ≠ 0 by positivity,
    show Real.sqrt 6 ≠ 0 by positivity]
  all_goals nlinarith [sqrt_two_sq, sqrt_six_sq]

theorem hexagon_radius_sq_ratio (i j : Fin 6) :
    (∑ k : Fin 2, outerHexagonPoint i k * outerHexagonPoint i k) =
      3 * (∑ k : Fin 2, innerHexagonPoint j k * innerHexagonPoint j k) := by
  rw [outerHexagonPoint_squared_norm, innerHexagonPoint_squared_norm]
  norm_num

theorem e₄_projection_zero :
    project (![0, 0, 0, 1] : Euclidean4) = 0 := by
  funext i
  fin_cases i <;>
    simp [project, Matrix.mulVec, coxeterPlaneProjection, dotProduct,
      Fin.sum_univ_four]

def claimedMinusOneVector : Euclidean4 := ![1, -1, -1, 0]

theorem claimedMinusOneVector_in_projection_kernel :
    project claimedMinusOneVector = 0 := by
  funext i
  fin_cases i <;>
    simp [project, Matrix.mulVec, claimedMinusOneVector,
      coxeterPlaneProjection, dotProduct, Fin.sum_univ_four]
  <;> ring

theorem project_eq_zero_iff (x : Euclidean4) :
    project x = 0 ↔ x 1 = -x 0 ∧ x 2 = -x 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [project, Matrix.mulVec, coxeterPlaneProjection, dotProduct,
      Fin.sum_univ_four] at h0 h1
    field_simp [show Real.sqrt 2 ≠ 0 by positivity] at h0
    field_simp [show Real.sqrt 6 ≠ 0 by positivity] at h1
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i
    · simp [project, Matrix.mulVec, coxeterPlaneProjection, dotProduct,
        Fin.sum_univ_four, h1]
    · simp [project, Matrix.mulVec, coxeterPlaneProjection, dotProduct,
        Fin.sum_univ_four, h1, h2]
      ring

theorem projection_kernel_coordinates (x : Euclidean4)
    (hx : project x = 0) :
    x 1 = -x 0 ∧ x 2 = -x 0 :=
  (project_eq_zero_iff x).mp hx

end

end InfoGeometry.RootSystem.D4
