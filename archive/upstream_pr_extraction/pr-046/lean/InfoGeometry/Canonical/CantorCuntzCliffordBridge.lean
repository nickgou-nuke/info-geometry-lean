import Mathlib.Tactic
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Canonical.HodgeDrazinEnvelope
import InfoGeometry.Canonical.FierzReadout

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.Topology
open InfoGeometry.Canonical.HodgeDrazinEnvelope
open InfoGeometry.Canonical.FierzReadout

def cantorAnticommutator
    {Op : Type*} [Add Op] [Mul Op]
    (x y : Op) : Op :=
  x * y + y * x

def carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) : Op :=
  InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)

theorem star_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    star (carFromCuntz C) = InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
  unfold carFromCuntz
  rw [star_mul, star_star]

theorem carFromCuntz_sq_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    carFromCuntz C * carFromCuntz C = 0 := by
  unfold carFromCuntz
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C))
        = InfoGeometry.Topology.CuntzO2Carrier.S_left C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
          noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C * 0 * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
          rw [(InfoGeometry.Topology.CuntzO2Carrier.orthogonal_ranges C).2]
    _ = 0 := by simp

theorem carFromCuntz_anticommutator_star_eq_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    cantorAnticommutator (carFromCuntz C) (star (carFromCuntz C)) = 1 := by
  unfold cantorAnticommutator carFromCuntz
  rw [star_mul, star_star]
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C))
        + (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C))
        = InfoGeometry.Topology.CuntzO2Carrier.S_left C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)
          + InfoGeometry.Topology.CuntzO2Carrier.S_right C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
            noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)
          + InfoGeometry.Topology.CuntzO2Carrier.S_right C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
            rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry C, InfoGeometry.Topology.CuntzO2Carrier.left_isometry C]
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) + InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by simp
    _ = 1 := InfoGeometry.Topology.CuntzO2Carrier.range_sum C

theorem carFromCuntz_mul_star_eq_leftRangeProjection
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    carFromCuntz C * star (carFromCuntz C) =
      InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
  unfold carFromCuntz
  rw [star_mul, star_star]
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) =
        InfoGeometry.Topology.CuntzO2Carrier.S_left C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
          noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry C]
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by simp

theorem star_carFromCuntz_mul_carFromCuntz_eq_rightRangeProjection
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    star (carFromCuntz C) * carFromCuntz C =
      InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
  rw [star_carFromCuntz]
  unfold carFromCuntz
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) =
        InfoGeometry.Topology.CuntzO2Carrier.S_right C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
          noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry C]
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by simp

theorem carFromCuntz_mul_star_mul_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    carFromCuntz C * star (carFromCuntz C) * carFromCuntz C =
      carFromCuntz C := by
  rw [carFromCuntz_mul_star_eq_leftRangeProjection]
  unfold carFromCuntz
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) =
        InfoGeometry.Topology.CuntzO2Carrier.S_left C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
          noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry C]
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by simp

theorem star_carFromCuntz_mul_carFromCuntz_mul_star_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    star (carFromCuntz C) * carFromCuntz C * star (carFromCuntz C) =
      star (carFromCuntz C) := by
  rw [star_carFromCuntz_mul_carFromCuntz_eq_rightRangeProjection]
  rw [star_carFromCuntz]
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) =
        InfoGeometry.Topology.CuntzO2Carrier.S_right C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
          noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry C]
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by simp

theorem star_carFromCuntz_carFromCuntz_add_carFromCuntz_star_carFromCuntz
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    star (carFromCuntz C) * carFromCuntz C +
        carFromCuntz C * star (carFromCuntz C) = 1 := by
  rw [star_carFromCuntz]
  unfold carFromCuntz
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C))
        + (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C))
        = InfoGeometry.Topology.CuntzO2Carrier.S_right C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)
          + InfoGeometry.Topology.CuntzO2Carrier.S_left C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
            noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)
          + InfoGeometry.Topology.CuntzO2Carrier.S_left C * 1 * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
            rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry C, InfoGeometry.Topology.CuntzO2Carrier.right_isometry C]
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) + InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
      simp
    _ = 1 := by
      rw [add_comm]
      exact InfoGeometry.Topology.CuntzO2Carrier.range_sum C

namespace CuntzO2Carrier

variable {Op : Type*} [Ring Op] [StarRing Op]

theorem left_star_right_sq_zero (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = 0 := by
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) =
        InfoGeometry.Topology.CuntzO2Carrier.S_left C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
          noncomm_ring
    _ = 0 := by rw [(InfoGeometry.Topology.CuntzO2Carrier.orthogonal_ranges C).2]; simp

theorem right_star_left_sq_zero (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) = 0 := by
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) =
        InfoGeometry.Topology.CuntzO2Carrier.S_right C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
          noncomm_ring
    _ = 0 := by rw [(InfoGeometry.Topology.CuntzO2Carrier.orthogonal_ranges C).1]; simp

theorem left_star_right_mul_right_star_left (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) = (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) := by
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) =
        InfoGeometry.Topology.CuntzO2Carrier.S_left C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by
          noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) := by rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry C]; simp

theorem right_star_left_mul_left_star_right (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) =
        InfoGeometry.Topology.CuntzO2Carrier.S_right C * (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
          noncomm_ring
    _ = InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry C]; simp

theorem left_star_right_anticommutator (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) +
      (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = 1 := by
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) +
      (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) =
        (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) + (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
          rw [left_star_right_mul_right_star_left,
            right_star_left_mul_left_star_right]
    _ = 1 := InfoGeometry.Topology.CuntzO2Carrier.rangeProjection_sum_one C

theorem left_star_right_mul_star_left_star_right (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) := by
  rw [star_mul, star_star]
  exact left_star_right_mul_right_star_left C

theorem right_star_left_mul_star_right_star_left (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) = (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
  rw [star_mul, star_star]
  exact right_star_left_mul_left_star_right C

theorem left_star_right_add_star_left_star_right (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) +
      star (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = 1 := by
  rw [star_mul, star_star]
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) +
      (InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = 1 :=
      left_star_right_anticommutator C

end CuntzO2Carrier

theorem carFromCuntz_star_sq_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    star (carFromCuntz C) * star (carFromCuntz C) = 0 := by
  have h := congrArg star (carFromCuntz_sq_eq_zero C)
  simpa [star_mul] using h

theorem carFromCuntz_real_generator_square
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
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
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
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
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
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

theorem carFromCuntz_isMoorePenroseInverse
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (carFromCuntz C) (star (carFromCuntz C)) := by
  refine ⟨carFromCuntz_mul_star_mul_carFromCuntz C,
    star_carFromCuntz_mul_carFromCuntz_mul_star_carFromCuntz C, ?_, ?_⟩
  · calc
      star (carFromCuntz C * star (carFromCuntz C)) =
          star (star (carFromCuntz C)) * star (carFromCuntz C) := by
            rw [star_mul]
      _ = carFromCuntz C * star (carFromCuntz C) := by rw [star_star]
  · calc
      star (star (carFromCuntz C) * carFromCuntz C) =
          star (carFromCuntz C) * star (star (carFromCuntz C)) := by
            rw [star_mul]
      _ = star (carFromCuntz C) * carFromCuntz C := by rw [star_star]

theorem star_carFromCuntz_isMoorePenroseInverse
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (star (carFromCuntz C)) (carFromCuntz C) := by
  refine ⟨star_carFromCuntz_mul_carFromCuntz_mul_star_carFromCuntz C,
    carFromCuntz_mul_star_mul_carFromCuntz C, ?_, ?_⟩
  · calc
      star (star (carFromCuntz C) * carFromCuntz C) =
          star (carFromCuntz C) * star (star (carFromCuntz C)) := by
            rw [star_mul]
      _ = star (carFromCuntz C) * carFromCuntz C := by rw [star_star]
  · calc
      star (carFromCuntz C * star (carFromCuntz C)) =
          star (star (carFromCuntz C)) * star (carFromCuntz C) := by
            rw [star_mul]
      _ = carFromCuntz C * star (carFromCuntz C) := by rw [star_star]

theorem carFromCuntz_isDrazinInverse_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    InfoGeometry.Singular.Drazin.IsDrazinInverse
      (carFromCuntz C) 0 2 := by
  refine ⟨by simp, by simp, ?_⟩
  simpa [pow_two] using carFromCuntz_sq_eq_zero C

theorem star_carFromCuntz_isDrazinInverse_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    InfoGeometry.Singular.Drazin.IsDrazinInverse
      (star (carFromCuntz C)) 0 2 := by
  refine ⟨by simp, by simp, ?_⟩
  simpa [pow_two] using carFromCuntz_star_sq_eq_zero C

theorem carFromCuntz_mpProjector_eq_leftRange
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (h : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (carFromCuntz C) (star (carFromCuntz C))) :
    InfoGeometry.Singular.MoorePenrose.MP_Projector
        (carFromCuntz C) (star (carFromCuntz C)) h =
      (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) := by
  unfold InfoGeometry.Singular.MoorePenrose.MP_Projector
  exact carFromCuntz_mul_star_eq_leftRangeProjection C

theorem star_carFromCuntz_mpProjector_eq_rightRange
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (h : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (star (carFromCuntz C)) (carFromCuntz C)) :
    InfoGeometry.Singular.MoorePenrose.MP_Projector
        (star (carFromCuntz C)) (carFromCuntz C) h =
      (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
  unfold InfoGeometry.Singular.MoorePenrose.MP_Projector
  exact star_carFromCuntz_mul_carFromCuntz_eq_rightRangeProjection C

theorem carFromCuntz_drazinProjector_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (h : InfoGeometry.Singular.Drazin.IsDrazinInverse
      (carFromCuntz C) 0 2) :
    InfoGeometry.Singular.Drazin.Drazin_Projector
        (carFromCuntz C) 0 2 h = 0 := by
  simp [InfoGeometry.Singular.Drazin.Drazin_Projector]

theorem star_carFromCuntz_drazinProjector_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (h : InfoGeometry.Singular.Drazin.IsDrazinInverse
      (star (carFromCuntz C)) 0 2) :
    InfoGeometry.Singular.Drazin.Drazin_Projector
        (star (carFromCuntz C)) 0 2 h = 0 := by
  simp [InfoGeometry.Singular.Drazin.Drazin_Projector]

theorem carFromCuntz_drazin_inverse_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) {D : Op}
    (hD : InfoGeometry.Singular.Drazin.IsDrazinInverse
      (carFromCuntz C) D 2) :
    D = 0 := by
  exact InfoGeometry.Singular.Drazin.Drazin_unique hD
    (carFromCuntz_isDrazinInverse_zero C)

theorem star_carFromCuntz_drazin_inverse_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) {D : Op}
    (hD : InfoGeometry.Singular.Drazin.IsDrazinInverse
      (star (carFromCuntz C)) D 2) :
    D = 0 := by
  exact InfoGeometry.Singular.Drazin.Drazin_unique hD
    (star_carFromCuntz_isDrazinInverse_zero C)

theorem carFromCuntz_mpDrazinDefect_asymmetry_eq_cliffordBivector
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (hMP : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (carFromCuntz C) (star (carFromCuntz C)))
    (hMPstar : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (star (carFromCuntz C)) (carFromCuntz C))
    (hD : InfoGeometry.Singular.Drazin.IsDrazinInverse
      (carFromCuntz C) 0 2)
    (hDstar : InfoGeometry.Singular.Drazin.IsDrazinInverse
      (star (carFromCuntz C)) 0 2) :
    (InfoGeometry.Singular.MoorePenrose.MP_Projector
        (carFromCuntz C) (star (carFromCuntz C)) hMP -
      InfoGeometry.Singular.Drazin.Drazin_Projector
        (carFromCuntz C) 0 2 hD) -
    (InfoGeometry.Singular.MoorePenrose.MP_Projector
        (star (carFromCuntz C)) (carFromCuntz C) hMPstar -
      InfoGeometry.Singular.Drazin.Drazin_Projector
        (star (carFromCuntz C)) 0 2 hDstar) =
      (carFromCuntz C - star (carFromCuntz C)) *
        (carFromCuntz C + star (carFromCuntz C)) := by
  simp only [InfoGeometry.Singular.MoorePenrose.MP_Projector,
    InfoGeometry.Singular.Drazin.Drazin_Projector, mul_zero, sub_zero]
  have hA := carFromCuntz_sq_eq_zero C
  have hAstar := carFromCuntz_star_sq_eq_zero C
  calc
    carFromCuntz C * star (carFromCuntz C) -
          star (carFromCuntz C) * carFromCuntz C =
        carFromCuntz C * carFromCuntz C +
          carFromCuntz C * star (carFromCuntz C) -
          star (carFromCuntz C) * carFromCuntz C -
          star (carFromCuntz C) * star (carFromCuntz C) := by
            rw [hA, hAstar]
            noncomm_ring
    _ = (carFromCuntz C - star (carFromCuntz C)) *
          (carFromCuntz C + star (carFromCuntz C)) := by
            noncomm_ring

theorem carFromCuntz_cliffordBivector_eq_rangeGrading
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (carFromCuntz C - star (carFromCuntz C)) *
        (carFromCuntz C + star (carFromCuntz C)) =
      (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) - (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
  calc
    (carFromCuntz C - star (carFromCuntz C)) *
          (carFromCuntz C + star (carFromCuntz C)) =
        carFromCuntz C * carFromCuntz C +
          carFromCuntz C * star (carFromCuntz C) -
          star (carFromCuntz C) * carFromCuntz C -
          star (carFromCuntz C) * star (carFromCuntz C) := by
            noncomm_ring
    _ = (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) - (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
      rw [carFromCuntz_sq_eq_zero C, carFromCuntz_star_sq_eq_zero C,
        carFromCuntz_mul_star_eq_leftRangeProjection,
        star_carFromCuntz_mul_carFromCuntz_eq_rightRangeProjection]
      simp [InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection,
        InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection]

theorem carFromCuntz_rangeGrading_sq_eq_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C - (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C)) *
        (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C - (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C)) = 1 := by
  calc
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C - (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C)) *
          (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C - (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C)) =
        (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) -
          (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) -
          (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) +
          (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) * (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
            noncomm_ring
    _ = (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) + (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
      rw [InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection_idempotent C,
        InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection_mul_rightRangeProjection_eq_zero C,
        InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection_mul_leftRangeProjection_eq_zero C,
        InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection_idempotent C]
      simp
    _ = 1 := InfoGeometry.Topology.CuntzO2Carrier.rangeProjection_sum_one C

theorem carFromCuntz_cliffordBivector_sq_eq_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    ((carFromCuntz C - star (carFromCuntz C)) *
        (carFromCuntz C + star (carFromCuntz C))) *
      ((carFromCuntz C - star (carFromCuntz C)) *
        (carFromCuntz C + star (carFromCuntz C))) = 1 := by
  rw [carFromCuntz_cliffordBivector_eq_rangeGrading C]
  exact carFromCuntz_rangeGrading_sq_eq_one C

theorem carFromCuntz_rangeGrading_eq_cliffordBivector
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) - (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) =
      (carFromCuntz C - star (carFromCuntz C)) *
        (carFromCuntz C + star (carFromCuntz C)) := by
  exact (carFromCuntz_cliffordBivector_eq_rangeGrading C).symm

theorem carFromCuntz_moorePenrose_inverse_eq_star
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) {B : Op}
    (hB : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (carFromCuntz C) B) :
    B = star (carFromCuntz C) :=
  InfoGeometry.Singular.MoorePenrose.MoorePenrose_unique hB
    (carFromCuntz_isMoorePenroseInverse C)

theorem star_carFromCuntz_moorePenrose_inverse_eq
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) {B : Op}
    (hB : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (star (carFromCuntz C)) B) :
    B = carFromCuntz C :=
  InfoGeometry.Singular.MoorePenrose.MoorePenrose_unique hB
    (star_carFromCuntz_isMoorePenroseInverse C)

theorem carFromCuntz_mpDrazinDefect_asymmetry_eq_rangeGrading
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (hMP : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (carFromCuntz C) (star (carFromCuntz C)))
    (hMPstar : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (star (carFromCuntz C)) (carFromCuntz C))
    (hD : InfoGeometry.Singular.Drazin.IsDrazinInverse
      (carFromCuntz C) 0 2)
    (hDstar : InfoGeometry.Singular.Drazin.IsDrazinInverse
      (star (carFromCuntz C)) 0 2) :
    (InfoGeometry.Singular.MoorePenrose.MP_Projector
        (carFromCuntz C) (star (carFromCuntz C)) hMP -
      InfoGeometry.Singular.Drazin.Drazin_Projector
        (carFromCuntz C) 0 2 hD) -
    (InfoGeometry.Singular.MoorePenrose.MP_Projector
        (star (carFromCuntz C)) (carFromCuntz C) hMPstar -
      InfoGeometry.Singular.Drazin.Drazin_Projector
        (star (carFromCuntz C)) 0 2 hDstar) =
      (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C) - (InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C) := by
  rw [carFromCuntz_mpDrazinDefect_asymmetry_eq_cliffordBivector
      C hMP hMPstar hD hDstar,
    carFromCuntz_cliffordBivector_eq_rangeGrading C]

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

end InfoGeometry.Canonical
