import InfoGeometry.Spectrometry.GeometricMedianCore

namespace InfoGeometry.Spectrometry.GeometricMedianCore

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {Line Space : Type*} [Fintype Line]
variable [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

def weightedQuadratic (weights : Line → ℝ) (observed : Line → Space)
    (point : Space) : ℝ :=
  ∑ line, weights line * ‖point - observed line‖ ^ 2

theorem weightedCenter_score_zero (weights : Line → ℝ) (observed : Line → Space)
    (mass_ne : (∑ line, weights line) ≠ 0) :
    weightedScore weights observed (weightedCenter weights observed) = 0 :=
  (weightedScore_zero_iff_fixed weights observed _ mass_ne).mpr rfl

theorem weightedQuadratic_completed_square
    (weights : Line → ℝ) (observed : Line → Space) (point : Space)
    (mass_ne : (∑ line, weights line) ≠ 0) :
    weightedQuadratic weights observed point =
      weightedQuadratic weights observed (weightedCenter weights observed) +
        (∑ line, weights line) * ‖point - weightedCenter weights observed‖ ^ 2 := by
  let center := weightedCenter weights observed
  have cross_zero :
      (∑ line : Line, weights line *
        (inner ℝ (point - center) (center - observed line))) = 0 := by
    calc
      (∑ line : Line, weights line *
          inner ℝ (point - center) (center - observed line)) =
          inner ℝ (point - center)
            (∑ line : Line, weights line • (center - observed line)) := by
        rw [inner_sum]
        simp only [real_inner_smul_right]
      _ = 0 := by
        change inner ℝ (point - center)
          (weightedScore weights observed center) = 0
        rw [weightedCenter_score_zero weights observed mass_ne, inner_zero_right]
  have expansion (line : Line) :
      weights line * ‖point - (observed line)‖ ^ 2 =
        weights line * ‖center - (observed line)‖ ^ 2 +
        weights line * ‖point - center‖ ^ 2 +
        2 * (weights line *
          inner ℝ (point - center) (center - observed line)) := by
    have split : point - (observed line) =
        (point - center) + (center - (observed line)) := by
      abel
    rw [split, norm_add_sq_real]
    ring
  change (∑ line : Line, weights line * ‖point - (observed line)‖ ^ 2) =
    (∑ line : Line, weights line * ‖center - (observed line)‖ ^ 2) +
      (∑ line : Line, weights line) * ‖point - center‖ ^ 2
  simp_rw [expansion]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, cross_zero]
  ring

theorem weightedCenter_minimizes_quadratic
    (weights : Line → ℝ) (observed : Line → Space) (point : Space)
    (weights_nonneg : ∀ line, 0 ≤ weights line)
    (mass_ne : (∑ line, weights line) ≠ 0) :
    weightedQuadratic weights observed (weightedCenter weights observed) ≤
      weightedQuadratic weights observed point := by
  rw [weightedQuadratic_completed_square weights observed point mass_ne]
  exact le_add_of_nonneg_right
    (mul_nonneg (Finset.sum_nonneg (fun line _ => weights_nonneg line)) (sq_nonneg _))

end

end InfoGeometry.Spectrometry.GeometricMedianCore
