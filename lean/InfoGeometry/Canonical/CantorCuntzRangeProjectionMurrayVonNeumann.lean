import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

variable (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)

theorem unit_murrayVonNeumannEquivalent_leftRangeProjection :
    MurrayVonNeumannEquivalent (1 : Op) (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) := by
  refine ⟨InfoGeometry.Topology.CuntzO2Carrier.S_left C, ?_, ?_⟩
  · exact InfoGeometry.Topology.CuntzO2Carrier.left_isometry C
  · rfl

theorem unit_murrayVonNeumannEquivalent_rightRangeProjection :
    MurrayVonNeumannEquivalent (1 : Op) (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
  refine ⟨InfoGeometry.Topology.CuntzO2Carrier.S_right C, ?_, ?_⟩
  · exact InfoGeometry.Topology.CuntzO2Carrier.right_isometry C
  · rfl

theorem leftRangeProjection_murrayVonNeumannEquivalent_unit :
    MurrayVonNeumannEquivalent
      (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) (1 : Op) := by
  exact mvn_symm (unit_murrayVonNeumannEquivalent_leftRangeProjection C)

theorem rightRangeProjection_murrayVonNeumannEquivalent_unit :
    MurrayVonNeumannEquivalent
      (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) (1 : Op) := by
  exact mvn_symm (unit_murrayVonNeumannEquivalent_rightRangeProjection C)

theorem leftRangeProjection_murrayVonNeumannEquivalent_rightRangeProjection :
    MurrayVonNeumannEquivalent (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
  refine ⟨InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C), ?_, ?_⟩
  · change star (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
      (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) = (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C)
    rw [star_mul, star_star]
    calc
      InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) =
          InfoGeometry.Topology.CuntzO2Carrier.S_left C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
            noncomm_ring
      _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
        rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry C]
        simp
  · change (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
      star (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) = (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C)
    rw [star_mul, star_star]
    calc
      InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) =
          InfoGeometry.Topology.CuntzO2Carrier.S_right C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
            noncomm_ring
      _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
        rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry C]
        simp

theorem leftRangeProjection_idempotent_murrayVonNeumann :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C *
        InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C =
      InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) =
      InfoGeometry.Topology.CuntzO2Carrier.S_left C *
        (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
          InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
            noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
      rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry C]
      simp

theorem rightRangeProjection_idempotent_murrayVonNeumann :
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C *
        InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C =
      InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) =
      InfoGeometry.Topology.CuntzO2Carrier.S_right C *
        (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
          InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
            noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
      rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry C]
      simp

theorem leftRangeProjection_selfAdjoint_murrayVonNeumann :
    star (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) =
      InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection
  rw [star_mul, star_star]

theorem rightRangeProjection_selfAdjoint_murrayVonNeumann :
    star (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) =
      InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection
  rw [star_mul, star_star]

theorem leftRangeProjection_mul_rightRangeProjection_eq_zero_murrayVonNeumann :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C *
        InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C = 0 := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) =
      InfoGeometry.Topology.CuntzO2Carrier.S_left C *
        (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
          InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
            noncomm_ring
    _ = 0 := by
      rw [InfoGeometry.Topology.CuntzO2Carrier.orthogonal_ranges C |>.1]
      simp

theorem rightRangeProjection_mul_leftRangeProjection_eq_zero_murrayVonNeumann :
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C *
        InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C = 0 := by
  unfold InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) =
      InfoGeometry.Topology.CuntzO2Carrier.S_right C *
        (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
          InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
            noncomm_ring
    _ = 0 := by
      rw [InfoGeometry.Topology.CuntzO2Carrier.orthogonal_ranges C |>.2]
      simp

theorem leftRangeProjection_ne_zero [Nontrivial Op] :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C ≠ 0 := by
  intro hzero
  have hword := InfoGeometry.Topology.CuntzO2Carrier.left_isometry C
  have hs : InfoGeometry.Topology.CuntzO2Carrier.S_left C = 0 := by
    calc
      InfoGeometry.Topology.CuntzO2Carrier.S_left C =
          InfoGeometry.Topology.CuntzO2Carrier.S_left C * 1 := by simp
      _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C *
          (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
            InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
        rw [hword]
      _ = (InfoGeometry.Topology.CuntzO2Carrier.S_left C *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
            InfoGeometry.Topology.CuntzO2Carrier.S_left C := by
        noncomm_ring
      _ = 0 := by
        have hzero' :
            InfoGeometry.Topology.CuntzO2Carrier.S_left C *
                star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) = 0 := by
          simpa [InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection] using hzero
        rw [hzero']
        simp
  rw [hs, star_zero, zero_mul] at hword
  exact zero_ne_one hword

theorem rightRangeProjection_ne_zero [Nontrivial Op] :
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C ≠ 0 := by
  intro hzero
  have hword := InfoGeometry.Topology.CuntzO2Carrier.right_isometry C
  have hs : InfoGeometry.Topology.CuntzO2Carrier.S_right C = 0 := by
    calc
      InfoGeometry.Topology.CuntzO2Carrier.S_right C =
          InfoGeometry.Topology.CuntzO2Carrier.S_right C * 1 := by simp
      _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C *
          (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
            InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
        rw [hword]
      _ = (InfoGeometry.Topology.CuntzO2Carrier.S_right C *
          star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
            InfoGeometry.Topology.CuntzO2Carrier.S_right C := by
        noncomm_ring
      _ = 0 := by
        have hzero' :
            InfoGeometry.Topology.CuntzO2Carrier.S_right C *
                star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) = 0 := by
          simpa [InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection] using hzero
        rw [hzero']
        simp
  rw [hs, star_zero, zero_mul] at hword
  exact zero_ne_one hword

theorem leftRangeProjection_ne_one [Nontrivial Op] :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C ≠ 1 := by
  intro hone
  apply rightRangeProjection_ne_zero C
  calc
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C =
        1 * InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C := by simp
    _ = InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C *
        InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C := by
      rw [hone]
    _ = 0 := leftRangeProjection_mul_rightRangeProjection_eq_zero_murrayVonNeumann C

theorem rightRangeProjection_ne_one [Nontrivial Op] :
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C ≠ 1 := by
  intro hone
  apply leftRangeProjection_ne_zero C
  calc
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C =
        1 * InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C := by simp
    _ = InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C *
        InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C := by
      rw [hone]
    _ = 0 := rightRangeProjection_mul_leftRangeProjection_eq_zero_murrayVonNeumann C

theorem leftRangeProjection_ne_rightRangeProjection [Nontrivial Op] :
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C ≠
      InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C := by
  intro hEq
  apply leftRangeProjection_ne_zero C
  calc
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C =
        InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C := hEq
    _ = InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C *
        InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C := by
      rw [hEq, rightRangeProjection_idempotent_murrayVonNeumann]
    _ = 0 := rightRangeProjection_mul_leftRangeProjection_eq_zero_murrayVonNeumann C

theorem no_normalized_additive_trace
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (tau : Op →+ ℝ)
    (h_one : tau 1 = 1)
    (h_trace : ∀ x y : Op, tau (x * y) = tau (y * x)) :
    False := by
  have h_left : tau (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) = tau 1 := by
    calc
      tau (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) =
          tau (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) := by rfl
      _ = tau (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) := h_trace _ _
      _ = tau 1 := by rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry C]
  have h_right : tau (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = tau 1 := by
    calc
      tau (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) =
          tau (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) := by rfl
      _ = tau (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) := h_trace _ _
      _ = tau 1 := by rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry C]
  have h_sum : tau (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) + tau (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) = tau 1 := by
    rw [← tau.map_add, InfoGeometry.Topology.CuntzO2Carrier.rangeProjection_sum_one C]
  rw [h_left, h_right, h_one] at h_sum
  linarith

end CuntzO2Carrier

end
end InfoGeometry.Topology
