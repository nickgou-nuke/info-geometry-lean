import InfoGeometry.Exceptional.FreudenthalGenericJacobiClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalFiveGradedCarrierModule

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

def lanePartLinear (lane : JacobiLane) :
    FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D where
  toFun x := lanePart D lane x
  map_add' x y := by
    cases lane <;>
      apply FiveGradedCarrier.ext <;>
      simp [lanePart]
  map_smul' r x := by
    cases lane <;>
      apply FiveGradedCarrier.ext <;>
      simp [lanePart, FiveGradedCarrier.smul_minus2,
        FiveGradedCarrier.smul_minus1, FiveGradedCarrier.smul_zero_symp,
        FiveGradedCarrier.smul_zero_scale, FiveGradedCarrier.smul_plus1,
        FiveGradedCarrier.smul_plus2]

@[simp] theorem lanePartLinear_apply (lane : JacobiLane)
    (x : FiveGradedCarrier D) :
    lanePartLinear D lane x = lanePart D lane x := rfl

theorem lanePartLinear_reconstruct (x : FiveGradedCarrier D) :
    lanePartLinear D .minus2 x + lanePartLinear D .minus1 x +
      lanePartLinear D .zeroSymp x + lanePartLinear D .zeroScale x +
      lanePartLinear D .plus1 x + lanePartLinear D .plus2 x = x := by
  simpa only [lanePartLinear_apply] using sum_lanePart D x

end InfoGeometry.Exceptional.Freudenthal
