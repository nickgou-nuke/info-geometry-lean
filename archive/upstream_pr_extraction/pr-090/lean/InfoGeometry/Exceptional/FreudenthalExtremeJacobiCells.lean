import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem fiveGradedBracket_zero_left (u : FiveGradedCarrier D) :
    fiveGradedBracket D 0 u = 0 := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket]

theorem fiveGradedBracket_zero_right (u : FiveGradedCarrier D) :
    fiveGradedBracket D u 0 = 0 := by
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket]

theorem fiveJacobiator_zero_left (u v : FiveGradedCarrier D) :
    fiveJacobiator D 0 u v = 0 := by
  dsimp [fiveJacobiator]
  simp only [fiveGradedBracket_zero_left, fiveGradedBracket_zero_right]
  apply FiveGradedCarrier.ext <;> simp

theorem fiveJacobiator_zero_right (u v : FiveGradedCarrier D) :
    fiveJacobiator D u v 0 = 0 := by
  dsimp [fiveJacobiator]
  simp only [fiveGradedBracket_zero_left, fiveGradedBracket_zero_right]
  apply FiveGradedCarrier.ext <;> simp

theorem fiveJacobiator_diagonal (u : FiveGradedCarrier D) :
    fiveJacobiator D u u u = 0 := by
  dsimp [fiveJacobiator]
  rw [fiveGradedBracket_self]
  have h : fiveGradedBracket D u 0 = 0 := by
    apply FiveGradedCarrier.ext <;>
      simp [fiveGradedBracket]
  rw [h]
  apply FiveGradedCarrier.ext <;> simp

end InfoGeometry.Exceptional.Freudenthal
