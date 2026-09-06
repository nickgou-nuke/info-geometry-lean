import InfoGeometry.Exceptional.FreudenthalJacobiLaneFiniteEncoding
import InfoGeometry.Exceptional.FreudenthalJacobiLaneLinearMaps

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

theorem lanePartLinear_fin_sum (x : FiveGradedCarrier D) :
    (∑ i : Fin 6, lanePartLinear D (laneOfFin i) x) = x := by
  rw [show (∑ i : Fin 6, lanePartLinear D (laneOfFin i) x) =
      lanePartLinear D .minus2 x + lanePartLinear D .minus1 x +
        lanePartLinear D .zeroSymp x + lanePartLinear D .zeroScale x +
        lanePartLinear D .plus1 x + lanePartLinear D .plus2 x by
      simp [Fin.sum_univ_succ, laneOfFin]
      ac_rfl]
  exact lanePartLinear_reconstruct D x

end InfoGeometry.Exceptional.Freudenthal
