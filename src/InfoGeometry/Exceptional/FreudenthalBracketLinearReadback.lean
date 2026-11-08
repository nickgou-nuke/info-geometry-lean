import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketLinearMaps
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem fiveGradedBracket_left_map_add
    (u v w : FiveGradedCarrier D) :
    fiveGradedBracket_left D w (u + v) =
      fiveGradedBracket_left D w u + fiveGradedBracket_left D w v := by
  exact (fiveGradedBracket_left D w).map_add u v

theorem fiveGradedBracket_right_map_add
    (u v w : FiveGradedCarrier D) :
    fiveGradedBracket_right D u (v + w) =
      fiveGradedBracket_right D u v + fiveGradedBracket_right D u w := by
  exact (fiveGradedBracket_right D u).map_add v w

end InfoGeometry.Exceptional.Freudenthal
