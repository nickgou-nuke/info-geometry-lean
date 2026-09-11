import InfoGeometry.Exceptional.FreudenthalSymplecticMixedBracket
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure

/-!
# Bilinearity of the Five-Graded Freudenthal Lie Bracket

This module proves that `fiveGradedBracket D` is linear in both arguments under the native vector operations.
-/

namespace InfoGeometry.Exceptional.Freudenthal

noncomputable section

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem fiveGradedBracket_add_left
    (u u' v : FiveGradedCarrier D) :
    fiveGradedBracket D (u + u') v =
      fiveGradedBracket D u v + fiveGradedBracket D u' v := by
  apply FiveGradedCarrier.ext
  · simp [fiveGradedBracket]
    ring
  · simp [fiveGradedBracket, sub_eq_add_neg]
    module
  · simp only [fiveGradedBracket, FiveGradedCarrier.add_zero_symp, FiveGradedCarrier.add_minus1,
      FiveGradedCarrier.add_plus1, add_lie, mixedSymplecticBracket_add_left D,
      mixedSymplecticBracket_add_right D, smul_add]
    abel
  · simp [fiveGradedBracket]
    ring
  · simp [fiveGradedBracket, sub_eq_add_neg]
    module
  · simp [fiveGradedBracket]
    ring

theorem fiveGradedBracket_add_right
    (u v v' : FiveGradedCarrier D) :
    fiveGradedBracket D u (v + v') =
      fiveGradedBracket D u v + fiveGradedBracket D u v' := by
  apply FiveGradedCarrier.ext
  · simp [fiveGradedBracket]
    ring
  · simp [fiveGradedBracket, sub_eq_add_neg]
    module
  · simp only [fiveGradedBracket, FiveGradedCarrier.add_zero_symp, FiveGradedCarrier.add_minus1,
      FiveGradedCarrier.add_plus1, lie_add, mixedSymplecticBracket_add_left D,
      mixedSymplecticBracket_add_right D, smul_add]
    abel
  · simp [fiveGradedBracket]
    ring
  · simp [fiveGradedBracket, sub_eq_add_neg]
    module
  · simp [fiveGradedBracket]
    ring

end
end InfoGeometry.Exceptional.Freudenthal
