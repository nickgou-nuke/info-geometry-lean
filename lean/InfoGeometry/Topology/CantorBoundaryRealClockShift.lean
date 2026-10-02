import InfoGeometry.Topology.CantorBoundaryCuntzO2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Topology.CantorBoundaryRealClockShift

open InfoGeometry.Topology.CantorBoundaryCuntzO2

def clock : BoundaryOperator ℝ := matrixUnit 0 0 - matrixUnit 1 1

def shift : BoundaryOperator ℝ := matrixUnit 0 1 + matrixUnit 1 0

def phase : BoundaryOperator ℝ := clock * shift

theorem diagonal_sum :
    matrixUnit (R := ℝ) 0 0 + matrixUnit (R := ℝ) 1 1 = 1 := by
  simpa only [Fin.sum_univ_two] using (matrixUnit_diag_sum (R := ℝ))

theorem clock_sq : clock * clock = 1 := by
  calc
    clock * clock = matrixUnit (R := ℝ) 0 0 + matrixUnit (R := ℝ) 1 1 := by
      simp [clock, sub_mul, mul_sub, matrixUnit_mul]
    _ = 1 := diagonal_sum

theorem shift_sq : shift * shift = 1 := by
  calc
    shift * shift = matrixUnit (R := ℝ) 0 0 + matrixUnit (R := ℝ) 1 1 := by
      simp [shift, add_mul, mul_add, matrixUnit_mul]
    _ = 1 := diagonal_sum

theorem clock_shift_weyl : clock * shift = -(shift * clock) := by
  simp [clock, shift, sub_mul, mul_sub, add_mul, mul_add, matrixUnit_mul] <;> abel

theorem phase_eq_circular_difference :
    phase = matrixUnit (R := ℝ) 0 1 - matrixUnit (R := ℝ) 1 0 := by
  simp [phase, clock, shift, sub_mul, mul_add, matrixUnit_mul]

theorem phase_sq : phase * phase = -1 := by
  calc
    phase * phase = (clock * shift) * clock * shift := by
      simp only [phase, mul_assoc]
    _ = (-(shift * clock)) * clock * shift := by rw [clock_shift_weyl]
    _ = -(shift * (clock * clock) * shift) := by noncomm_ring
    _ = -1 := by rw [clock_sq, mul_one, shift_sq]

theorem phase_fourth_power : phase ^ 4 = 1 := by
  calc
    phase ^ 4 = (phase * phase) * (phase * phase) := by noncomm_ring
    _ = 1 := by rw [phase_sq]; simp

theorem transported_weyl
    (transport : BoundaryOperator ℝ ≃ₐ[ℝ] BoundaryOperator ℝ) :
    transport clock * transport shift = -(transport shift * transport clock) := by
  simpa only [map_mul, map_neg] using congrArg transport clock_shift_weyl

theorem transported_phase_sq
    (transport : BoundaryOperator ℝ ≃ₐ[ℝ] BoundaryOperator ℝ) :
    transport phase * transport phase = -1 := by
  simpa only [map_mul, map_neg, map_one] using congrArg transport phase_sq

end InfoGeometry.Topology.CantorBoundaryRealClockShift
