import Mathlib

noncomputable section

open Matrix

/-- An experimental feature patch represented as a `2 × 2` real matrix. -/
abbrev Patch2x2 := Matrix (Fin 2) (Fin 2) ℝ

/--
A `2 × 2` real matrix has zero determinant if and only if its rank is at most one.

The zero matrix has rank zero. A nonzero matrix satisfying either condition
therefore has rank exactly one.
-/
theorem null_patch_iff_rank_one (P : Patch2x2) :
    P.det = 0 ↔ P.rank ≤ 1 := by
  have hdet :
      P.det = 0 ↔
        LinearMap.ker (Matrix.toLin' P) ≠ ⊥ := by
    rw [← LinearMap.det_toLin' P]
    exact LinearMap.det_eq_zero_iff_ker_ne_bot

  rw [hdet]

  change
    LinearMap.ker P.mulVecLin ≠ ⊥ ↔
      Module.finrank ℝ (LinearMap.range P.mulVecLin) ≤ 1

  have hnullity :
      Module.finrank ℝ (LinearMap.range P.mulVecLin) +
          Module.finrank ℝ (LinearMap.ker P.mulVecLin) =
        2 := by
    simpa using
      (LinearMap.finrank_range_add_finrank_ker P.mulVecLin)

  constructor
  · intro hker
    have hker_ne_zero :
        Module.finrank ℝ (LinearMap.ker P.mulVecLin) ≠ 0 := by
      intro hzero
      apply hker
      exact Submodule.finrank_eq_zero.mp hzero
    omega

  · intro hrank hker
    have hker_zero :
        Module.finrank ℝ (LinearMap.ker P.mulVecLin) = 0 := by
      simp [hker]
    omega

/-- The current raw-patch feature map. -/
def patchFeature (P : Patch2x2) : Patch2x2 :=
  P

@[simp]
theorem patchFeature_apply (P : Patch2x2) :
    patchFeature P = P :=
  rfl

private theorem patch_eq_zero_of_rank_eq_zero
    (P : Patch2x2)
    (hrank : P.rank = 0) :
    P = 0 := by
  have hspan :
      Submodule.span ℝ (Set.range P.col) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [← Matrix.rank_eq_finrank_span_cols P]
    exact hrank
  ext i j
  have hmem :
      P.col j ∈ Submodule.span ℝ (Set.range P.col) :=
    Submodule.subset_span (Set.mem_range_self j)
  rw [hspan] at hmem
  have hcol : P.col j = 0 := by
    simpa using hmem
  simpa using congrFun hcol i

theorem nonzero_null_patch_rank_eq_one
    (P : Patch2x2)
    (hP : P ≠ 0)
    (hdet : P.det = 0) :
    P.rank = 1 := by
  have hrank_le : P.rank ≤ 1 :=
    (null_patch_iff_rank_one P).mp hdet
  have hrank_ne_zero : P.rank ≠ 0 := by
    intro hrank_zero
    exact hP (patch_eq_zero_of_rank_eq_zero P hrank_zero)
  omega

theorem nonzero_null_patch_outer_product
    (P : Patch2x2)
    (hP : P ≠ 0)
    (hdet : P.det = 0) :
    ∃ u v : Fin 2 → ℝ,
      u ≠ 0 ∧
      v ≠ 0 ∧
      P = Matrix.vecMulVec u v := by
  have hdet' :
      P 0 0 * P 1 1 - P 0 1 * P 1 0 = 0 := by
    simpa [Matrix.det_fin_two] using hdet

  by_cases h00 : P 0 0 = 0

  · by_cases h01 : P 0 1 = 0

    · let u : Fin 2 → ℝ := ![0, 1]
      let v : Fin 2 → ℝ := ![P 1 0, P 1 1]

      have hu : u ≠ 0 := by
        intro hu0
        have h := congrFun hu0 (1 : Fin 2)
        simpa [u] using h

      have hv : v ≠ 0 := by
        intro hv0
        have h10 : P 1 0 = 0 := by
          have h := congrFun hv0 (0 : Fin 2)
          simpa [v] using h
        have h11 : P 1 1 = 0 := by
          have h := congrFun hv0 (1 : Fin 2)
          simpa [v] using h
        apply hP
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h00, h01, h10, h11]

      refine ⟨u, v, hu, hv, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [u, v, Matrix.vecMulVec, h00, h01]

    · have hprod : P 0 1 * P 1 0 = 0 := by
        calc P 0 1 * P 1 0 = P 0 0 * P 1 1 - (P 0 0 * P 1 1 - P 0 1 * P 1 0) := by ring
        _ = P 0 0 * P 1 1 - 0 := by rw [hdet']
        _ = 0 * P 1 1 - 0 := by rw [h00]
        _ = 0 := by ring

      have h10 : P 1 0 = 0 :=
        (mul_eq_zero.mp hprod).resolve_left h01

      let u : Fin 2 → ℝ := ![P 0 1, P 1 1]
      let v : Fin 2 → ℝ := ![0, 1]

      have hu : u ≠ 0 := by
        intro hu0
        apply h01
        have h := congrFun hu0 (0 : Fin 2)
        revert h; simp [u]

      have hv : v ≠ 0 := by
        intro hv0
        have h := congrFun hv0 (1 : Fin 2)
        revert h; simp [v]

      refine ⟨u, v, hu, hv, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [u, v, Matrix.vecMulVec, h00, h10]

  · have h11 :
        P 1 1 =
          P 1 0 * (P 0 1 / P 0 0) := by
      rw [← mul_div_assoc]
      apply (eq_div_iff h00).2
      nlinarith [hdet']

    let u : Fin 2 → ℝ := ![P 0 0, P 1 0]
    let v : Fin 2 → ℝ := ![1, P 0 1 / P 0 0]

    have hu : u ≠ 0 := by
      intro hu0
      apply h00
      have h := congrFun hu0 (0 : Fin 2)
      revert h; simp [u]

    have hv : v ≠ 0 := by
      intro hv0
      have h := congrFun hv0 (0 : Fin 2)
      revert h; simp [v]

    refine ⟨u, v, hu, hv, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j

    · simp [u, v, Matrix.vecMulVec]

    · dsimp [u, v, Matrix.vecMulVec]
      field_simp [h00]

    · simp [u, v, Matrix.vecMulVec]

    · simpa [u, v, Matrix.vecMulVec] using h11

end
