import InfoGeometry.Spectrometry.SvdClrEquivalence
import InfoGeometry.Probability.DetectorRankOneScale

namespace InfoGeometry.Spectrometry.FixedScaleLeastSquares

open scoped BigOperators
open SvdClrEquivalence

noncomputable section

variable {rowCount acquisitionCount : ℕ}

def scaleSquareSum (scales : Fin acquisitionCount → ℝ) : ℝ :=
  ∑ acquisition, scales acquisition ^ 2

def optimalProfile (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (row : Fin rowCount) : ℝ :=
  InfoGeometry.Probability.DetectorRankOneScale.originSlope scales (observed row)

theorem optimal_profile_formula
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (row : Fin rowCount) :
    optimalProfile observed scales row =
      (∑ acquisition, observed row acquisition * scales acquisition) / scaleSquareSum scales := by
  simp [optimalProfile, InfoGeometry.Probability.DetectorRankOneScale.originSlope,
    scaleSquareSum, sq, mul_comm]

theorem scale_square_sum_nonneg (scales : Fin acquisitionCount → ℝ) :
    0 ≤ scaleSquareSum scales :=
  Finset.sum_nonneg (fun acquisition _ => sq_nonneg (scales acquisition))

theorem scale_square_sum_pos (scales : Fin acquisitionCount → ℝ)
    (count_pos : 0 < acquisitionCount) (scales_pos : ∀ acquisition, 0 < scales acquisition) :
    0 < scaleSquareSum scales := by
  letI : Nonempty (Fin acquisitionCount) := ⟨⟨0, count_pos⟩⟩
  exact Finset.sum_pos (fun acquisition _ => sq_pos_of_pos (scales_pos acquisition))
    Finset.univ_nonempty

theorem optimal_profile_pos
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (row : Fin rowCount)
    (count_pos : 0 < acquisitionCount)
    (observed_pos : ∀ acquisition, 0 < observed row acquisition)
    (scales_pos : ∀ acquisition, 0 < scales acquisition) :
    0 < optimalProfile observed scales row := by
  letI : Nonempty (Fin acquisitionCount) := ⟨⟨0, count_pos⟩⟩
  rw [optimal_profile_formula]
  exact div_pos (Finset.sum_pos (fun acquisition _ =>
    mul_pos (observed_pos acquisition) (scales_pos acquisition)) Finset.univ_nonempty)
    (scale_square_sum_pos scales count_pos scales_pos)

def rowLoss (values scales : Fin acquisitionCount → ℝ) (coefficient : ℝ) : ℝ :=
  ∑ acquisition, (values acquisition - coefficient * scales acquisition) ^ 2

theorem row_loss_expansion (values scales : Fin acquisitionCount → ℝ) (coefficient : ℝ) :
    rowLoss values scales coefficient = (∑ acquisition, values acquisition ^ 2) -
      2 * coefficient * (∑ acquisition, values acquisition * scales acquisition) +
      coefficient ^ 2 * scaleSquareSum scales := by
  simp only [rowLoss, scaleSquareSum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro acquisition _
  ring

theorem profile_normal_equation
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (row : Fin rowCount)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    (∑ acquisition, (observed row acquisition -
      optimalProfile observed scales row * scales acquisition) * scales acquisition) = 0 := by
  simp_rw [sub_mul, mul_assoc, ← sq]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (∑ acquisition, observed row acquisition * scales acquisition) -
    optimalProfile observed scales row * scaleSquareSum scales = 0
  rw [optimal_profile_formula, div_mul_cancel₀ _ norm_ne, sub_self]

theorem row_loss_pythagorean
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (row : Fin rowCount) (coefficient : ℝ)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    rowLoss (observed row) scales coefficient =
      rowLoss (observed row) scales (optimalProfile observed scales row) +
        scaleSquareSum scales * (coefficient - optimalProfile observed scales row) ^ 2 := by
  rw [row_loss_expansion, row_loss_expansion, optimal_profile_formula]
  field_simp
  ring

theorem optimal_profile_minimizes
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (row : Fin rowCount)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    IsMinOn (rowLoss (observed row) scales) Set.univ (optimalProfile observed scales row) := by
  intro coefficient _
  change rowLoss (observed row) scales (optimalProfile observed scales row) ≤
    rowLoss (observed row) scales coefficient
  rw [row_loss_pythagorean observed scales row coefficient norm_ne]
  exact le_add_of_nonneg_right (mul_nonneg (scale_square_sum_nonneg scales) (sq_nonneg _))

theorem row_loss_eq_minimum_iff
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (row : Fin rowCount) (coefficient : ℝ)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    rowLoss (observed row) scales coefficient =
      rowLoss (observed row) scales (optimalProfile observed scales row) ↔
        coefficient = optimalProfile observed scales row := by
  rw [row_loss_pythagorean observed scales row coefficient norm_ne]
  simp [norm_ne, sub_eq_zero]

def reconstruction (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ :=
  responseMatrix (optimalProfile observed scales) scales

theorem optimal_profile_exact (profile : Fin rowCount → ℝ)
    (scales : Fin acquisitionCount → ℝ) (norm_ne : scaleSquareSum scales ≠ 0) :
    optimalProfile (responseMatrix profile scales) scales = profile := by
  funext row
  exact InfoGeometry.Probability.DetectorRankOneScale.originSlope_exact scales _ (profile row)
    (fun _ => rfl) (by simpa only [scaleSquareSum, sq] using norm_ne)

theorem reconstruction_exact (profile : Fin rowCount → ℝ)
    (scales : Fin acquisitionCount → ℝ) (norm_ne : scaleSquareSum scales ≠ 0) :
    reconstruction (responseMatrix profile scales) scales = responseMatrix profile scales := by
  rw [reconstruction, optimal_profile_exact profile scales norm_ne]

theorem reconstruction_idempotent
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (norm_ne : scaleSquareSum scales ≠ 0) :
    reconstruction (reconstruction observed scales) scales = reconstruction observed scales :=
  reconstruction_exact _ _ norm_ne

theorem reconstruction_rank_le_one
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) :
    (reconstruction observed scales).rank ≤ 1 :=
  response_rank_le_one _ _

end

end InfoGeometry.Spectrometry.FixedScaleLeastSquares
