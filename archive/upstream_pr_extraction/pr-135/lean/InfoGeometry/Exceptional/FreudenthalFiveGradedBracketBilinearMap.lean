import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketLinearMaps
import InfoGeometry.Exceptional.FreudenthalFiveGradedBracketBilinear

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

def fiveGradedBracketBilinear :
    FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D →ₗ[ℝ] FiveGradedCarrier D where
  toFun u := fiveGradedBracket_right D u
  map_add' u u' := by
    apply LinearMap.ext
    intro v
    exact fiveGradedBracket_add_left D u u' v
  map_smul' r u := by
    apply LinearMap.ext
    intro v
    exact fiveGradedBracket_smul_left D r u v

@[simp] theorem fiveGradedBracketBilinear_apply
    (u v : FiveGradedCarrier D) :
    fiveGradedBracketBilinear D u v = fiveGradedBracket D u v := rfl

end InfoGeometry.Exceptional.Freudenthal
