import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure
import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketBilinear

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

set_option maxHeartbeats 1000000 in
theorem fiveJacobiator_add_left (u v w z : FiveGradedCarrier D) :
    fiveJacobiator D (u + v) w z =
      fiveJacobiator D u w z + fiveJacobiator D v w z := by
  dsimp [fiveJacobiator]
  rw [fiveGradedBracket_add_left, fiveGradedBracket_add_right,
    fiveGradedBracket_add_right]
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket]

set_option maxHeartbeats 1000000 in
theorem fiveJacobiator_add_right (u v w z : FiveGradedCarrier D) :
    fiveJacobiator D u (v + w) z =
      fiveJacobiator D u v z + fiveJacobiator D u w z := by
  dsimp [fiveJacobiator]
  rw [fiveGradedBracket_add_right, fiveGradedBracket_add_left,
    fiveGradedBracket_add_left]
  apply FiveGradedCarrier.ext <;>
    simp [fiveGradedBracket]

end InfoGeometry.Exceptional.Freudenthal
