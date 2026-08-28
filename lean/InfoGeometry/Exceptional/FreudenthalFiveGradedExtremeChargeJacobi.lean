import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure

/-! Same-sign extreme/charge homogeneous Jacobi cells. -/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The `(-2,-2,-1)` orbit is zero by the negative grade bounds. -/
theorem jacobi_extremeMinus_extremeMinus_chargeMinus
    (a b : ℝ) (z : FreudenthalCharge J) :
    fiveJacobiator D (genEminus D a) (genEminus D b) (injChargeMinus D z) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, injChargeMinus,
      FiveGradedCarrier.instAdd] <;>
    simp

/-- The `(+2,+2,+1)` orbit is zero by the positive grade bounds. -/
theorem jacobi_extremePlus_extremePlus_chargePlus
    (a b : ℝ) (z : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D a) (genEplus D b) (injChargePlus D z) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, injChargePlus,
      FiveGradedCarrier.instAdd] <;>
    simp

end InfoGeometry.Exceptional.Freudenthal
