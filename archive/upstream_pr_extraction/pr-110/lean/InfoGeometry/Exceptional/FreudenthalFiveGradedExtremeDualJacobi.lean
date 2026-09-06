import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure

/-! The dual contact-sector homogeneous Jacobi cell. -/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The `(+2,+2,-1)` Jacobi orbit closes by the dual extreme bracket laws. -/
theorem jacobi_extremePlus_extremePlus_chargeMinus
    (a b : ℝ) (z : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D a) (genEplus D b) (injChargeMinus D z) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, injChargeMinus,
      FiveGradedCarrier.instAdd] <;>
    simp

end InfoGeometry.Exceptional.Freudenthal
