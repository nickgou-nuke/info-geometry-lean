import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.OperatorAlgebra.RealProjectionMurrayVonNeumann

/-!
# Native Cuntz range projections

This owner records only algebraic consequences of the existing
`CuntzO2Carrier`: range projections, their orthogonal partition, and the
Murray--von Neumann equivalences witnessed by the two Cuntz isometries.
No C*-completion, K-theory, KMS state, or factor claim is made here.
-/

open InfoGeometry.OperatorAlgebra
namespace InfoGeometry.Topology

noncomputable section

variable {Op : Type*} [Ring Op] [StarRing Op]

namespace CuntzO2Carrier

variable (C : CuntzO2Carrier Op)

theorem unit_murrayVonNeumannEquivalent_leftRangeProjection :
    MurrayVonNeumannEquivalent (1 : Op) C.leftRangeProjection := by
  refine ⟨C.S_left, ?_, ?_⟩
  · exact C.left_isometry
  · rfl

theorem unit_murrayVonNeumannEquivalent_rightRangeProjection :
    MurrayVonNeumannEquivalent (1 : Op) C.rightRangeProjection := by
  refine ⟨C.S_right, ?_, ?_⟩
  · exact C.right_isometry
  · rfl

theorem no_normalized_additive_trace
    (C : CuntzO2Carrier Op)
    (tau : Op →+ ℝ)
    (h_one : tau 1 = 1)
    (h_trace : ∀ x y : Op, tau (x * y) = tau (y * x)) :
    False := by
  have h_left : tau C.leftRangeProjection = tau 1 := by
    calc
      tau C.leftRangeProjection =
          tau (C.S_left * star C.S_left) := by rfl
      _ = tau (star C.S_left * C.S_left) := h_trace _ _
      _ = tau 1 := by rw [C.left_isometry]
  have h_right : tau C.rightRangeProjection = tau 1 := by
    calc
      tau C.rightRangeProjection =
          tau (C.S_right * star C.S_right) := by rfl
      _ = tau (star C.S_right * C.S_right) := h_trace _ _
      _ = tau 1 := by rw [C.right_isometry]
  have h_sum : tau C.leftRangeProjection + tau C.rightRangeProjection = tau 1 := by
    rw [← tau.map_add, C.rangeProjection_sum_one]
  rw [h_left, h_right, h_one] at h_sum
  linarith

end CuntzO2Carrier

end
end InfoGeometry.Topology
