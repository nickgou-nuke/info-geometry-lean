import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketBilinear

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem fiveGradedCarrier_decompose (u : FiveGradedCarrier D) :
    u = genEminus D u.minus2 + injChargeMinus D u.minus1 +
      injSympZero D u.zero_symp + genHscale D u.zero_scale +
      injChargePlus D u.plus1 + genEplus D u.plus2 := by
  apply FiveGradedCarrier.ext <;>
    dsimp [genEminus, injChargeMinus, injSympZero, genHscale,
      injChargePlus, genEplus, FiveGradedCarrier.instAdd]
  · abel
  · abel
  · simp
  · abel
  · abel
  · abel

end InfoGeometry.Exceptional.Freudenthal
