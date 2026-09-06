import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure

/-! Contact/zero-grade homogeneous Jacobi closure for the negative extreme. -/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- The `(-2,-2,0)` orbit closes for an arbitrary zero-grade block. -/
theorem jacobi_extremeMinus_extremeMinus_zeroBlock
    (a b h : ℝ) (T : SymplecticTKKZero D) :
    fiveJacobiator D (genEminus D a) (genEminus D b)
      ⟨0, 0, T, h, 0, 0⟩ = 0 := by
  dsimp [fiveJacobiator]
  apply FiveGradedCarrier.ext <;>
    dsimp [fiveGradedBracket, genEminus, FiveGradedCarrier.instAdd] <;>
    simp

end InfoGeometry.Exceptional.Freudenthal
