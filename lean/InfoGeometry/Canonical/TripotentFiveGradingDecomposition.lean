import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition

/-! Canonical compatibility export for the Physics/Algebra owner. -/

namespace InfoGeometry.Canonical

export InfoGeometry.Physics.Algebra
  (FiveGrade fiveGradeValue fiveGradeProjector fiveGradeRange
   fiveGradeComponentLinear FiveGradeCoordinates fiveGradeDecomposeLinear
   fiveGradeRecomposeLinear fiveGradeProjector_idempotent
   fiveGradeProjector_mul_eq_zero_of_ne fiveGradeProjectors_sum_eq_id
   fiveGradeProjector_apply_range_self
   fiveGradeProjector_apply_range_eq_zero_of_ne
   fiveGrade_recompose_decompose fiveGrade_decompose_recompose
   tripotentFiveGradeLinearEquiv tripotentFiveGradeLinearEquiv_apply
   TripotentFiveGradeBracketLaws tripotentFiveGrading)

end InfoGeometry.Canonical
