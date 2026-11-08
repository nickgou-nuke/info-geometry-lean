import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Same-sign extreme/charge homogeneous Jacobi cells. -/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The `(-2,-2,-1)` orbit is zero by the negative grade bounds. -/
theorem extremeMinus_extremeMinus_chargeMinus_eq_zero
    (a b : ℝ) (z : FreudenthalCharge J) :
    fiveJacobiator D (genEminus D a) (genEminus D b) (injChargeMinus D z) = 0 :=
  jacobi_extremeMinus_extremeMinus_chargeMinus D a b z

/-- The `(+2,+2,+1)` orbit is zero by the positive grade bounds. -/
theorem extremePlus_extremePlus_chargePlus_eq_zero
    (a b : ℝ) (z : FreudenthalCharge J) :
    fiveJacobiator D (genEplus D a) (genEplus D b) (injChargePlus D z) = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, injChargePlus,
      FiveGradedCarrier.instAdd] <;>
    simp

end InfoGeometry.Exceptional.Freudenthal
