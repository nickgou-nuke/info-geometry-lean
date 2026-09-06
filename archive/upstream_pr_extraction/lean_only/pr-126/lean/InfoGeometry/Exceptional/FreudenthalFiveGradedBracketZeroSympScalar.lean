import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure
import InfoGeometry.Exceptional.FreudenthalSymplecticMixedBracket

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem fiveGradedBracket_zeroSymp_smul_left (r : ℝ)
    (u v : FiveGradedCarrier D) :
    (fiveGradedBracket D (r • u) v).zero_symp =
      (r • fiveGradedBracket D u v).zero_symp := by
  simp only [FiveGradedCarrier.smul_zero_symp]
  dsimp [fiveGradedBracket]
  rw [smul_lie, mixedSymplecticBracket_smul_left,
    mixedSymplecticBracket_smul_right]
  module

theorem fiveGradedBracket_zeroSymp_smul_right (r : ℝ)
    (u v : FiveGradedCarrier D) :
    (fiveGradedBracket D u (r • v)).zero_symp =
      (r • fiveGradedBracket D u v).zero_symp := by
  simp only [FiveGradedCarrier.smul_zero_symp]
  dsimp [fiveGradedBracket]
  rw [lie_smul, mixedSymplecticBracket_smul_right,
    mixedSymplecticBracket_smul_left]
  module

end InfoGeometry.Exceptional.Freudenthal
