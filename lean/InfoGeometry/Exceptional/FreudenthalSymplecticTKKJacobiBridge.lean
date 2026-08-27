import InfoGeometry.Exceptional.FreudenthalSymplecticTKKJacobiObstruction

/-!
# Conditional mixed-Jacobi bridge

The total TKK bracket needs one additional mixed-triple symmetry.  This file
does not assume that identity globally; it proves exactly the Jacobi component
that follows when the identity is supplied for the chosen inputs.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem tkk_mixed_jacobi_plus1_component_eq_zero
    (x y z : FreudenthalCharge J)
    (htriple :
      (mixedSymplecticBracket D z y : Module.End ℝ (FreudenthalCharge J)) x =
        (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) z) :
    (tkkTotalBracket D (injMinus1 D x)
      (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).plus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).plus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).plus1 = 0 := by
  have hz : (0 : FreudenthalCharge J) =
      { alpha := 0, beta := 0, x := 0, y := 0 } := by
    apply FreudenthalCharge.ext <;> rfl
  rw [hz]
  simp [tkkTotalBracket, injMinus1, injPlus1,
    FreudenthalCharge.symplecticForm]

end InfoGeometry.Exceptional.Freudenthal
