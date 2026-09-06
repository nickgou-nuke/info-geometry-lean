import InfoGeometry.Exceptional.FreudenthalFiveGradedCarrierModule
import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketScalarBilinearity
import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketBilinear

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

def fiveGradedBracket_left (v : FiveGradedCarrier D) :
    FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D where
  toFun u := fiveGradedBracket D u v
  map_add' u u' := fiveGradedBracket_add_left D u u' v
  map_smul' r u := fiveGradedBracket_smul_left D r u v

@[simp] theorem fiveGradedBracket_left_apply
    (v u : FiveGradedCarrier D) :
    fiveGradedBracket_left D v u = fiveGradedBracket D u v := rfl

def fiveGradedBracket_right (u : FiveGradedCarrier D) :
    FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D where
  toFun v := fiveGradedBracket D u v
  map_add' v v' := fiveGradedBracket_add_right D u v v'
  map_smul' r v := fiveGradedBracket_smul_right D r u v

@[simp] theorem fiveGradedBracket_right_apply
    (u v : FiveGradedCarrier D) :
    fiveGradedBracket_right D u v = fiveGradedBracket D u v := rfl

end InfoGeometry.Exceptional.Freudenthal
