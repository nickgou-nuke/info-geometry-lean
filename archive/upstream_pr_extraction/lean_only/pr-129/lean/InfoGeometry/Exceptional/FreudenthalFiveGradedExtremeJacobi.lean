import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure

/-! A contact-sector homogeneous Jacobi cell for the native five-graded carrier. -/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The `(-2,-2,+1)` Jacobi orbit closes by the extreme bracket laws. -/
theorem jacobi_extremeMinus_extremeMinus_chargePlus
    (a b : ℝ) (z : FreudenthalCharge J) :
    fiveJacobiator D (genEminus D a) (genEminus D b) (injChargePlus D z) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, injChargePlus,
      FiveGradedCarrier.instAdd] <;>
    simp

end InfoGeometry.Exceptional.Freudenthal
