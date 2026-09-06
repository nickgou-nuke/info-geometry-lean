import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure

/-!
# Extreme/contact Jacobi readback

The `(-2,-2,+1)` homogeneous cell is closed directly on the native carrier.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem jacobi_extremeMinus_extremeMinus_chargePlus_readback
    (a b : ℝ) (z : FreudenthalCharge J) :
    fiveJacobiator D (genEminus D a) (genEminus D b) (injChargePlus D z) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, injChargePlus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_extremePlus_extremePlus_chargeMinus_readback
    (a b : ℝ) (z : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D a) (genEplus D b) (injChargeMinus D z) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, injChargeMinus,
      FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_extremeMinus_extremeMinus_extremeMinus_readback
    (a b c : ℝ) :
    fiveJacobiator D (genEminus D a) (genEminus D b) (genEminus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, FiveGradedCarrier.instAdd] <;>
    simp

theorem jacobi_extremePlus_extremePlus_extremePlus_readback
    (a b c : ℝ) :
    fiveJacobiator D (genEplus D a) (genEplus D b) (genEplus D c) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, FiveGradedCarrier.instAdd] <;>
    simp

end InfoGeometry.Exceptional.Freudenthal
