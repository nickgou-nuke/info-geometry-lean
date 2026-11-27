/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SinkhornKLIteration

/-!
# KL projection identities with structural zeros

Zero reference entries are allowed only when the first argument also vanishes
there. No infinite KL penalty is encoded as a real number. The supported
identities are used for an iteration that preserves the original zero mask.
-/
noncomputable section
open scoped BigOperators
namespace InfoGeometry.Physics.AmariSinkhornAlternatingProjections
open InfoGeometry.Prequantum.JaynesKLPotential
variable {I J : Type*} [Fintype I] [Fintype J]

theorem scalarKL_nonneg_supported {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : y = 0 → x = 0) : 0 ≤ scalarKLDivergence x y := by
  by_cases h : y = 0
  · simp [scalarKLDivergence, h, hz h]
  · exact scalarKLDivergence_nonneg_left hx (lt_of_le_of_ne hy (Ne.symm h))

theorem scalarKL_eq_zero_iff_supported {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : y = 0 → x = 0) : scalarKLDivergence x y = 0 ↔ x = y := by
  by_cases h : y = 0
  · simp [scalarKLDivergence, h, hz h]
  · exact scalarKLDivergence_eq_zero_iff_nonneg hx (lt_of_le_of_ne hy (Ne.symm h))

theorem matrixKL_nonneg_supported (P Q : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hs : ∀ i j, Q i j = 0 → P i j = 0) : 0 ≤ matrixKL P Q := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    scalarKL_nonneg_supported (hP i j) (hQ i j) (hs i j)

theorem matrixKL_eq_zero_iff_supported (P Q : TransportPlan I J)
    (hP : ∀ i j, 0 ≤ P i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hs : ∀ i j, Q i j = 0 → P i j = 0) : matrixKL P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
        Finset.sum_nonneg fun j _ => scalarKL_nonneg_supported
          (hP i j) (hQ i j) (hs i j))).1 h
    funext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset J)) =>
        scalarKL_nonneg_supported (hP i j) (hQ i j) (hs i j))).1
      (hi i (Finset.mem_univ i))
    exact (scalarKL_eq_zero_iff_supported (hP i j) (hQ i j) (hs i j)).1
      (hj j (Finset.mem_univ j))
  · rintro rfl
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    exact (scalarKL_eq_zero_iff_supported (hQ i j) (hQ i j) (fun h => h)).2 rfl

theorem matrixKL_three_point_supported (P Q K : TransportPlan I J)
    (hQ : ∀ i j, 0 ≤ Q i j) (hK : ∀ i j, 0 ≤ K i j)
    (hQK : ∀ i j, Q i j = 0 ↔ K i j = 0)
    (hPK : ∀ i j, K i j = 0 → P i j = 0) :
    matrixKL P K = matrixKL P Q + matrixKL Q K +
      ∑ i, ∑ j, (P i j - Q i j) * Real.log (Q i j / K i j) := by
  have hpoint (i : I) (j : J) :
      scalarKLDivergence (P i j) (K i j) =
      scalarKLDivergence (P i j) (Q i j) + scalarKLDivergence (Q i j) (K i j) +
        (P i j - Q i j) * Real.log (Q i j / K i j) := by
    by_cases h : K i j = 0
    · simp [scalarKLDivergence, h, hPK i j h, (hQK i j).2 h]
    · exact scalarKLDivergence_three_point _ _ _
        (lt_of_le_of_ne (hQ i j) (Ne.symm (fun hq => h ((hQK i j).1 hq))))
        (lt_of_le_of_ne (hK i j) (Ne.symm h))
  unfold matrixKL
  simp_rw [hpoint, Finset.sum_add_distrib]

/-- Marginal projection remains exact on a preserved zero mask. -/
theorem matrixKL_row_pythagorean_supported (P M : TransportPlan I J) (r : I → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hr : ∀ i, 0 < r i)
    (hm : ∀ i, 0 < rowMass M i)
    (hPM : ∀ i j, M i j = 0 → P i j = 0)
    (hPr : ∀ i, rowMass P i = r i) :
    matrixKL P M = matrixKL P (sinkhornRowUpdate M r) +
      matrixKL (sinkhornRowUpdate M r) M := by
  have ha (i : I) : 0 < r i / rowMass M i := div_pos (hr i) (hm i)
  have hR : ∀ i j, 0 ≤ sinkhornRowUpdate M r i j :=
    fun i j => mul_nonneg (ha i).le (hM i j)
  have hs : ∀ i j, sinkhornRowUpdate M r i j = 0 ↔ M i j = 0 := by
    intro i j
    change (r i / rowMass M i) * M i j = 0 ↔ M i j = 0
    simp [(ha i).ne']
  rw [matrixKL_three_point_supported P _ M hR hM hs hPM]
  suffices (∑ i, ∑ j, (P i j - sinkhornRowUpdate M r i j) *
      Real.log (sinkhornRowUpdate M r i j / M i j)) = 0 by rw [this, add_zero]
  have hterm (i : I) (j : J) :
      (P i j - sinkhornRowUpdate M r i j) * Real.log (sinkhornRowUpdate M r i j / M i j) =
      (P i j - sinkhornRowUpdate M r i j) * Real.log (r i / rowMass M i) := by
    by_cases hz : M i j = 0
    · simp [hPM i j hz, (hs i j).2 hz]
    · rw [sinkhornRowUpdate, mul_div_cancel_right₀ _ hz] <;> rfl
  simp_rw [hterm]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_mul, Finset.sum_sub_distrib,
    sinkhornRowUpdate_row_sum M r i (hm i).ne']
  change (rowMass P i - r i) * _ = 0
  rw [hPr i, sub_self, zero_mul]

theorem matrixKL_col_pythagorean_supported (P M : TransportPlan I J) (c : J → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hc : ∀ j, 0 < c j)
    (hm : ∀ j, 0 < colMass M j)
    (hPM : ∀ i j, M i j = 0 → P i j = 0)
    (hPc : ∀ j, colMass P j = c j) :
    matrixKL P M = matrixKL P (sinkhornColUpdate M c) +
      matrixKL (sinkhornColUpdate M c) M := by
  have ha (j : J) : 0 < c j / colMass M j := div_pos (hc j) (hm j)
  have hR : ∀ i j, 0 ≤ sinkhornColUpdate M c i j :=
    fun i j => mul_nonneg (ha j).le (hM i j)
  have hs : ∀ i j, sinkhornColUpdate M c i j = 0 ↔ M i j = 0 := by
    intro i j
    change (c j / colMass M j) * M i j = 0 ↔ M i j = 0
    simp [(ha j).ne']
  rw [matrixKL_three_point_supported P _ M hR hM hs hPM]
  suffices (∑ i, ∑ j, (P i j - sinkhornColUpdate M c i j) *
      Real.log (sinkhornColUpdate M c i j / M i j)) = 0 by rw [this, add_zero]
  have hterm (i : I) (j : J) :
      (P i j - sinkhornColUpdate M c i j) * Real.log (sinkhornColUpdate M c i j / M i j) =
      (P i j - sinkhornColUpdate M c i j) * Real.log (c j / colMass M j) := by
    by_cases hz : M i j = 0
    · simp [hPM i j hz, (hs i j).2 hz]
    · rw [sinkhornColUpdate, mul_div_cancel_right₀ _ hz] <;> rfl
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.sum_mul, Finset.sum_sub_distrib,
    sinkhornColUpdate_col_sum M c j (hm j).ne']
  change (colMass P j - c j) * _ = 0
  rw [hPc j, sub_self, zero_mul]

/-- Row-step KL is exactly the generalized divergence of row marginals. -/
theorem matrixKL_row_gap_eq_marginal (M : TransportPlan I J) (r : I → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hr : ∀ i, 0 < r i)
    (hm : ∀ i, 0 < rowMass M i) :
    matrixKL (sinkhornRowUpdate M r) M =
      ∑ i, scalarKLDivergence (r i) (rowMass M i) := by
  unfold matrixKL
  apply Finset.sum_congr rfl
  intro i _
  let a := r i / rowMass M i
  have ha : 0 < a := div_pos (hr i) (hm i)
  have hpoint (j : J) : scalarKLDivergence (sinkhornRowUpdate M r i j) (M i j) =
      a * M i j * Real.log a - a * M i j + M i j := by
    by_cases hz : M i j = 0
    · simp [scalarKLDivergence, sinkhornRowUpdate, hz]
    · unfold scalarKLDivergence sinkhornRowUpdate
      rw [mul_div_cancel_right₀ _ hz] <;> rfl
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hac : a * rowMass M i = r i := div_mul_cancel₀ _ (hm i).ne'
  change (a * rowMass M i) * Real.log a - (a * rowMass M i) + rowMass M i = _
  rw [hac] <;> rfl

/-- Supported balanced positive scalings retain the exact KL Pythagorean law. -/
theorem matrixKL_pythagorean_scaling_supported (P K : TransportPlan I J)
    (u : I → ℝ) (v : J → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hPK : ∀ i j, K i j = 0 → P i j = 0)
    (hr : ∀ i, rowMass P i = rowMass (fun i j => u i * K i j * v j) i)
    (hc : ∀ j, colMass P j = colMass (fun i j => u i * K i j * v j) j) :
    matrixKL P K = matrixKL P (fun i j => u i * K i j * v j) +
      matrixKL (fun i j => u i * K i j * v j) K := by
  let Q : TransportPlan I J := fun i j => u i * K i j * v j
  have hQ : ∀ i j, 0 ≤ Q i j := fun i j => mul_nonneg (mul_nonneg (hu i).le (hK i j)) (hv j).le
  have hs : ∀ i j, Q i j = 0 ↔ K i j = 0 := by
    intro i j
    simp [Q, (hu i).ne', (hv j).ne']
  change matrixKL P K = matrixKL P Q + matrixKL Q K
  rw [matrixKL_three_point_supported P Q K hQ hK hs hPK]
  suffices (∑ i, ∑ j, (P i j - Q i j) * Real.log (Q i j / K i j)) = 0 by rw [this, add_zero]
  have hterm (i : I) (j : J) : (P i j - Q i j) * Real.log (Q i j / K i j) =
      (P i j - Q i j) * (Real.log (u i) + Real.log (v j)) := by
    by_cases hz : K i j = 0
    · simp [hPK i j hz, (hs i j).2 hz]
    · have hquot : Q i j / K i j = u i * v j := by
        dsimp [Q]
        field_simp [hz] <;> ring
      rw [hquot, Real.log_mul (hu i).ne' (hv j).ne']
  simp_rw [hterm]
  exact marginal_potential_pairing_zero P Q _ _ hr hc

end InfoGeometry.Physics.AmariSinkhornAlternatingProjections
