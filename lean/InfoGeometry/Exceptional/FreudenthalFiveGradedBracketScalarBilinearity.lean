import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketZeroSympScalar
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem fiveGradedBracket_smul_left (r : ℝ)
    (u v : FiveGradedCarrier D) :
    fiveGradedBracket D (r • u) v = r • fiveGradedBracket D u v := by
  apply FiveGradedCarrier.ext
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    ring
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    module
  · exact fiveGradedBracket_zeroSymp_smul_left D r u v
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    ring
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    module
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    ring

theorem fiveGradedBracket_smul_right (r : ℝ)
    (u v : FiveGradedCarrier D) :
    fiveGradedBracket D u (r • v) = r • fiveGradedBracket D u v := by
  apply FiveGradedCarrier.ext
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    ring
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    module
  · exact fiveGradedBracket_zeroSymp_smul_right D r u v
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    ring
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    module
  · simp [fiveGradedBracket, symplecticForm_smul_left,
      symplecticForm_smul_right]
    ring

end InfoGeometry.Exceptional.Freudenthal
