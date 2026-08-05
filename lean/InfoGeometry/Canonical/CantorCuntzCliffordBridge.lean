import Mathlib.Tactic
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Canonical.HodgeDrazinEnvelope
import InfoGeometry.Canonical.FierzReadout

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.Topology
open InfoGeometry.Canonical.HodgeDrazinEnvelope
open InfoGeometry.Canonical.FierzReadout

abbrev CantorSpace := ℕ → Bool
abbrev BinaryWord := List Bool
abbrev BitStream := ℕ → Bool
abbrev CantorCuntzO2Carrier
    (Op : Type*) [Ring Op] [StarRing Op] :=
  InfoGeometry.Topology.CuntzO2Carrier Op

def cantorAnticommutator
    {Op : Type*} [Add Op] [Mul Op]
    (x y : Op) : Op :=
  x * y + y * x

def carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) : Op :=
  C.S_left * star C.S_right

theorem star_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    star (carFromCuntz C) = C.S_right * star C.S_left := by
  unfold carFromCuntz
  rw [star_mul, star_star]

theorem carFromCuntz_sq_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    carFromCuntz C * carFromCuntz C = 0 := by
  unfold carFromCuntz
  calc
    (C.S_left * star C.S_right) * (C.S_left * star C.S_right)
        = C.S_left * (star C.S_right * C.S_left) * star C.S_right := by
          noncomm_ring
    _ = C.S_left * 0 * star C.S_right := by
          rw [C.orthogonal_ranges.2]
    _ = 0 := by simp

theorem carFromCuntz_anticommutator_star_eq_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    cantorAnticommutator (carFromCuntz C) (star (carFromCuntz C)) = 1 := by
  unfold cantorAnticommutator carFromCuntz
  rw [star_mul, star_star]
  calc
    (C.S_left * star C.S_right) * (C.S_right * star C.S_left)
        + (C.S_right * star C.S_left) * (C.S_left * star C.S_right)
        = C.S_left * (star C.S_right * C.S_right) * star C.S_left
          + C.S_right * (star C.S_left * C.S_left) * star C.S_right := by
            noncomm_ring
    _ = C.S_left * 1 * star C.S_left
          + C.S_right * 1 * star C.S_right := by
            rw [C.right_isometry, C.left_isometry]
    _ = C.S_left * star C.S_left + C.S_right * star C.S_right := by simp
    _ = 1 := C.range_sum

theorem carFromCuntz_mul_star_eq_leftRangeProjection
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    carFromCuntz C * star (carFromCuntz C) =
      C.S_left * star C.S_left := by
  unfold carFromCuntz
  rw [star_mul, star_star]
  calc
    (C.S_left * star C.S_right) * (C.S_right * star C.S_left) =
        C.S_left * (star C.S_right * C.S_right) * star C.S_left := by
          noncomm_ring
    _ = C.S_left * 1 * star C.S_left := by rw [C.right_isometry]
    _ = C.S_left * star C.S_left := by simp

theorem star_carFromCuntz_mul_carFromCuntz_eq_rightRangeProjection
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    star (carFromCuntz C) * carFromCuntz C =
      C.S_right * star C.S_right := by
  rw [star_carFromCuntz]
  unfold carFromCuntz
  calc
    (C.S_right * star C.S_left) * (C.S_left * star C.S_right) =
        C.S_right * (star C.S_left * C.S_left) * star C.S_right := by
          noncomm_ring
    _ = C.S_right * 1 * star C.S_right := by rw [C.left_isometry]
    _ = C.S_right * star C.S_right := by simp

theorem carFromCuntz_mul_star_mul_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    carFromCuntz C * star (carFromCuntz C) * carFromCuntz C =
      carFromCuntz C := by
  rw [carFromCuntz_mul_star_eq_leftRangeProjection]
  unfold carFromCuntz
  calc
    (C.S_left * star C.S_left) * (C.S_left * star C.S_right) =
        C.S_left * (star C.S_left * C.S_left) * star C.S_right := by
          noncomm_ring
    _ = C.S_left * 1 * star C.S_right := by rw [C.left_isometry]
    _ = C.S_left * star C.S_right := by simp

theorem star_carFromCuntz_mul_carFromCuntz_mul_star_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    star (carFromCuntz C) * carFromCuntz C * star (carFromCuntz C) =
      star (carFromCuntz C) := by
  rw [star_carFromCuntz_mul_carFromCuntz_eq_rightRangeProjection]
  rw [star_carFromCuntz]
  calc
    (C.S_right * star C.S_right) * (C.S_right * star C.S_left) =
        C.S_right * (star C.S_right * C.S_right) * star C.S_left := by
          noncomm_ring
    _ = C.S_right * 1 * star C.S_left := by rw [C.right_isometry]
    _ = C.S_right * star C.S_left := by simp

theorem star_carFromCuntz_carFromCuntz_add_carFromCuntz_star_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    star (carFromCuntz C) * carFromCuntz C +
        carFromCuntz C * star (carFromCuntz C) = 1 := by
  rw [star_carFromCuntz]
  unfold carFromCuntz
  calc
    (C.S_right * star C.S_left) * (C.S_left * star C.S_right)
        + (C.S_left * star C.S_right) * (C.S_right * star C.S_left)
        = C.S_right * (star C.S_left * C.S_left) * star C.S_right
          + C.S_left * (star C.S_right * C.S_right) * star C.S_left := by
            noncomm_ring
    _ = C.S_right * 1 * star C.S_right
          + C.S_left * 1 * star C.S_left := by
            rw [C.left_isometry, C.right_isometry]
    _ = C.S_right * star C.S_right + C.S_left * star C.S_left := by
      simp
    _ = 1 := by
      rw [add_comm]
      exact C.range_sum

namespace CuntzO2Carrier

variable {Op : Type*} [Ring Op] [StarRing Op]

theorem left_star_right_sq_zero (C : CuntzO2Carrier Op) :
    (C.S_left * star C.S_right) *
        (C.S_left * star C.S_right) = 0 := by
  calc
    (C.S_left * star C.S_right) *
        (C.S_left * star C.S_right) =
        C.S_left * (star C.S_right * C.S_left) * star C.S_right := by
          noncomm_ring
    _ = 0 := by rw [C.orthogonal_ranges.2]; simp

theorem right_star_left_sq_zero (C : CuntzO2Carrier Op) :
    (C.S_right * star C.S_left) *
        (C.S_right * star C.S_left) = 0 := by
  calc
    (C.S_right * star C.S_left) *
        (C.S_right * star C.S_left) =
        C.S_right * (star C.S_left * C.S_right) * star C.S_left := by
          noncomm_ring
    _ = 0 := by rw [C.orthogonal_ranges.1]; simp

theorem left_star_right_mul_right_star_left (C : CuntzO2Carrier Op) :
    (C.S_left * star C.S_right) *
        (C.S_right * star C.S_left) = C.leftRangeProjection := by
  calc
    (C.S_left * star C.S_right) *
        (C.S_right * star C.S_left) =
        C.S_left * (star C.S_right * C.S_right) * star C.S_left := by
          noncomm_ring
    _ = C.S_left * star C.S_left := by rw [C.right_isometry]; simp

theorem right_star_left_mul_left_star_right (C : CuntzO2Carrier Op) :
    (C.S_right * star C.S_left) *
        (C.S_left * star C.S_right) = C.rightRangeProjection := by
  calc
    (C.S_right * star C.S_left) *
        (C.S_left * star C.S_right) =
        C.S_right * (star C.S_left * C.S_left) * star C.S_right := by
          noncomm_ring
    _ = C.S_right * star C.S_right := by rw [C.left_isometry]; simp

theorem left_star_right_anticommutator (C : CuntzO2Carrier Op) :
    (C.S_left * star C.S_right) *
        (C.S_right * star C.S_left) +
      (C.S_right * star C.S_left) *
        (C.S_left * star C.S_right) = 1 := by
  calc
    (C.S_left * star C.S_right) *
        (C.S_right * star C.S_left) +
      (C.S_right * star C.S_left) *
        (C.S_left * star C.S_right) =
        C.leftRangeProjection + C.rightRangeProjection := by
          rw [left_star_right_mul_right_star_left,
            right_star_left_mul_left_star_right]
    _ = 1 := C.rangeProjection_sum_one

theorem left_star_right_mul_star_left_star_right (C : CuntzO2Carrier Op) :
    (C.S_left * star C.S_right) *
        star (C.S_left * star C.S_right) = C.leftRangeProjection := by
  rw [star_mul, star_star]
  exact left_star_right_mul_right_star_left C

theorem right_star_left_mul_star_right_star_left (C : CuntzO2Carrier Op) :
    (C.S_right * star C.S_left) *
        star (C.S_right * star C.S_left) = C.rightRangeProjection := by
  rw [star_mul, star_star]
  exact right_star_left_mul_left_star_right C

theorem left_star_right_add_star_left_star_right (C : CuntzO2Carrier Op) :
    (C.S_left * star C.S_right) *
        star (C.S_left * star C.S_right) +
      star (C.S_left * star C.S_right) *
        (C.S_left * star C.S_right) = 1 := by
  rw [star_mul, star_star]
  calc
    (C.S_left * star C.S_right) *
        (C.S_right * star C.S_left) +
      (C.S_right * star C.S_left) *
        (C.S_left * star C.S_right) = 1 :=
      left_star_right_anticommutator C

end CuntzO2Carrier

theorem carFromCuntz_star_sq_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    star (carFromCuntz C) * star (carFromCuntz C) = 0 := by
  have h := congrArg star (carFromCuntz_sq_eq_zero C)
  simpa [star_mul] using h

theorem carFromCuntz_real_generator_square
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    (carFromCuntz C + star (carFromCuntz C)) *
        (carFromCuntz C + star (carFromCuntz C)) = 1 := by
  calc
    (carFromCuntz C + star (carFromCuntz C)) *
          (carFromCuntz C + star (carFromCuntz C)) =
        carFromCuntz C * carFromCuntz C +
          carFromCuntz C * star (carFromCuntz C) +
          star (carFromCuntz C) * carFromCuntz C +
          star (carFromCuntz C) * star (carFromCuntz C) := by
            noncomm_ring
    _ = 1 := by
      rw [carFromCuntz_sq_eq_zero, carFromCuntz_star_sq_eq_zero]
      simpa [cantorAnticommutator] using
        carFromCuntz_anticommutator_star_eq_one C

theorem carFromCuntz_imaginary_generator_square
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    (carFromCuntz C - star (carFromCuntz C)) *
        (carFromCuntz C - star (carFromCuntz C)) = -1 := by
  calc
    (carFromCuntz C - star (carFromCuntz C)) *
          (carFromCuntz C - star (carFromCuntz C)) =
        carFromCuntz C * carFromCuntz C -
          carFromCuntz C * star (carFromCuntz C) -
          star (carFromCuntz C) * carFromCuntz C +
          star (carFromCuntz C) * star (carFromCuntz C) := by
            noncomm_ring
    _ = -(carFromCuntz C * star (carFromCuntz C) +
          star (carFromCuntz C) * carFromCuntz C) := by
            rw [carFromCuntz_sq_eq_zero, carFromCuntz_star_sq_eq_zero]
            noncomm_ring
    _ = -1 := by
      rw [show carFromCuntz C * star (carFromCuntz C) +
          star (carFromCuntz C) * carFromCuntz C = 1 by
            simpa [cantorAnticommutator] using
              carFromCuntz_anticommutator_star_eq_one C]

theorem carFromCuntz_real_imag_anticommutator
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    cantorAnticommutator
        (carFromCuntz C + star (carFromCuntz C))
        (carFromCuntz C - star (carFromCuntz C)) = 0 := by
  unfold cantorAnticommutator
  calc
    (carFromCuntz C + star (carFromCuntz C)) *
          (carFromCuntz C - star (carFromCuntz C)) +
        (carFromCuntz C - star (carFromCuntz C)) *
          (carFromCuntz C + star (carFromCuntz C)) =
        2 • (carFromCuntz C * carFromCuntz C) +
          -2 • (star (carFromCuntz C) * star (carFromCuntz C)) := by
            noncomm_ring
    _ = 0 := by
      rw [carFromCuntz_sq_eq_zero, carFromCuntz_star_sq_eq_zero]
      simp

theorem carFromCuntz_clifford_relations
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    ((carFromCuntz C + star (carFromCuntz C)) *
        (carFromCuntz C + star (carFromCuntz C)) = 1) ∧
    ((carFromCuntz C - star (carFromCuntz C)) *
        (carFromCuntz C - star (carFromCuntz C)) = -1) ∧
    (cantorAnticommutator
      (carFromCuntz C + star (carFromCuntz C))
      (carFromCuntz C - star (carFromCuntz C)) = 0) := by
  exact ⟨carFromCuntz_real_generator_square C,
    carFromCuntz_imaginary_generator_square C,
    carFromCuntz_real_imag_anticommutator C⟩

theorem carFromCuntz_canonical_car_clifford_generators
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    carFromCuntz C * carFromCuntz C = 0 ∧
    cantorAnticommutator (carFromCuntz C) (star (carFromCuntz C)) = 1 ∧
    ((carFromCuntz C + star (carFromCuntz C)) *
        (carFromCuntz C + star (carFromCuntz C)) = 1) ∧
    ((carFromCuntz C - star (carFromCuntz C)) *
        (carFromCuntz C - star (carFromCuntz C)) = -1) := by
  exact ⟨carFromCuntz_sq_eq_zero C,
    carFromCuntz_anticommutator_star_eq_one C,
    carFromCuntz_real_generator_square C,
    carFromCuntz_imaginary_generator_square C⟩

def cantorCliffordEnvelope
    {Op : Type*} [Ring Op] [StarRing Op]
    (D : SignalDrazinSupport Op)
    (G : FrequencyDrazinGreen Op)
    (x : Op) : Op :=
  G.P_harm * (D.p * x * D.p) * G.P_harm

def cantorFierzCoordinate
    {Op : Type*} [Ring Op] [StarRing Op]
    (D : SignalDrazinSupport Op)
    (G : FrequencyDrazinGreen Op)
    (channel : FierzChannelReadout → Op → ℝ)
    (readout : FierzChannelReadout)
    (x : Op) : ℝ :=
  channel readout (cantorCliffordEnvelope D G x)

theorem carFromCuntz_is_car_generator
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    carFromCuntz C * carFromCuntz C = 0 ∧
    cantorAnticommutator (carFromCuntz C) (star (carFromCuntz C)) = 1 := by
  exact ⟨carFromCuntz_sq_eq_zero C,
    carFromCuntz_anticommutator_star_eq_one C⟩

theorem carFromCuntz_is_clifford_pair
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    ((carFromCuntz C + star (carFromCuntz C)) *
        (carFromCuntz C + star (carFromCuntz C)) = 1) ∧
    ((carFromCuntz C - star (carFromCuntz C)) *
        (carFromCuntz C - star (carFromCuntz C)) = -1) ∧
    cantorAnticommutator
      (carFromCuntz C + star (carFromCuntz C))
      (carFromCuntz C - star (carFromCuntz C)) = 0 :=
  carFromCuntz_clifford_relations C

end InfoGeometry.Canonical
