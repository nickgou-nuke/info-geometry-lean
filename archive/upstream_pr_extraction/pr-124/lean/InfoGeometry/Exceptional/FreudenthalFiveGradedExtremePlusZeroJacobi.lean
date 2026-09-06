import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure

/-! Dual contact/zero-grade homogeneous Jacobi closure. -/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The `(+2,+2,0)` orbit closes for an arbitrary zero-grade block. -/
theorem jacobi_extremePlus_extremePlus_zeroBlock
    (a b h : ℝ) (T : SymplecticTKKZero D) :
    fiveJacobiator D (genEplus D a) (genEplus D b)
      ⟨0, 0, T, h, 0, 0⟩ = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEplus, FiveGradedCarrier.instAdd] <;>
    simp

end InfoGeometry.Exceptional.Freudenthal
