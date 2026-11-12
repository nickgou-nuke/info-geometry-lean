/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TripotentMatrixExample
import InfoGeometry.OperatorAlgebra.UnitaryCornerCompression
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentParity

/-!
# Dense matrix witnesses for compression and ordered pairing

All witnesses live in the existing full four-by-four real matrix algebra.
Its dense transported matrix units retain noncommutative multiplication.
A native unitary exchange has nonzero raw transfer, but the transferred
observable and its Schwarz defect vanish. The compressed corner identity
and composition laws fail in the same example.

A separate three-factor path through the two-dimensional zero sector
distinguishes the correct middle ordering from its annihilating permutation.
An odd operator with nonzero square prevents confusing parity with nilpotence.
-/

noncomputable section

namespace InfoGeometry.Canonical.HorizonCompressionCounterexamples

open InfoGeometry.Canonical.TripotentMatrixExample
open InfoGeometry.OperatorAlgebra.UnitaryCornerCompression
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.SuperGrassmannianSusy

/-- Recover completeness from the existing three spectral projectors. -/
theorem frame_diagonal_sum :
    frameUnit 0 0 + frameUnit 1 1 + frameUnit 2 2 + frameUnit 3 3 = 1 := by
  calc
    _ = projPos tripotent + projZero tripotent + projNeg tripotent := by
      rw [projPos_eq, projZero_eq, projNeg_eq]
      abel
    _ = 1 := proj_sum_eq_id (T := tripotent)

/-- Exchange the positive and negative lines while fixing the zero sector. -/
def exchange : Mat :=
  frameUnit 0 1 + frameUnit 1 0 + frameUnit 2 2 + frameUnit 3 3

theorem exchange_selfAdjoint : IsSelfAdjoint exchange := by
  change star exchange = exchange
  simp only [exchange, star_add, frameUnit_star]
  abel

theorem exchange_sq : exchange * exchange = 1 := by
  calc
    _ = frameUnit 0 0 + frameUnit 1 1 + frameUnit 2 2 + frameUnit 3 3 := by
      simp [exchange, add_mul, mul_add, frameUnit_mul, add_comm]
    _ = 1 := frame_diagonal_sum

/-- The exchange is an inhabitant of Mathlib's native unitary group. -/
def exchangeUnitary : unitary Mat :=
  ⟨exchange, by
    rw [Unitary.mem_iff]
    simpa only [exchange_selfAdjoint.star_eq] using
      (And.intro exchange_sq exchange_sq)⟩

@[simp] theorem coe_exchangeUnitary : (exchangeUnitary : Mat) = exchange := rfl

theorem exchangeUnitary_mul_self : exchangeUnitary * exchangeUnitary = 1 := by
  apply Subtype.ext
  change exchange * exchange = 1
  exact exchange_sq

/-- Ambient conjugation moves the observed line entirely into its complement. -/
theorem exchange_conjugate_cut :
    Unitary.conjStarAlgAut ℤ Mat exchangeUnitary (frameUnit 0 0) =
      frameUnit 1 1 := by
  rw [Unitary.conjStarAlgAut_apply]
  change exchange * frameUnit 0 0 * star exchange = frameUnit 1 1
  rw [exchange_selfAdjoint.star_eq]
  simp [exchange, add_mul, mul_add, frameUnit_mul]

/-- Raw transfer of the unitary is a nonzero directed matrix unit. -/
theorem raw_transfer_eq :
    (1 - frameUnit 0 0) * (exchangeUnitary : Mat) * frameUnit 0 0 =
      frameUnit 1 0 := by
  change (1 - frameUnit 0 0) * exchange * frameUnit 0 0 = frameUnit 1 0
  simp [exchange, sub_mul, add_mul, mul_add, frameUnit_mul]

theorem raw_transfer_ne_zero :
    (1 - frameUnit 0 0) * (exchangeUnitary : Mat) * frameUnit 0 0 ≠ 0 := by
  rw [raw_transfer_eq]
  exact frameUnit_ne_zero 1 0

/-- The corner identity is lost after observing the exchanged projection. -/
theorem compressed_cut_zero :
    compress (frameUnit 0 0) exchangeUnitary (frameUnit 0 0) = 0 := by
  rw [compress, exchange_conjugate_cut]
  simp [frameUnit_mul]

/-- The actual transferred observable vanishes despite nonzero raw transfer. -/
theorem actual_transfer_zero :
    transfer (frameUnit 0 0) exchangeUnitary (frameUnit 0 0) = 0 := by
  rw [transfer, exchange_conjugate_cut]
  simp [sub_mul, frameUnit_mul]

/-- Raw unitary transfer therefore does not force a nonzero Schwarz defect. -/
theorem cut_schwarz_defect_zero :
    compress (frameUnit 0 0) exchangeUnitary
        (star (frameUnit 0 0) * frameUnit 0 0) -
      star (compress (frameUnit 0 0) exchangeUnitary (frameUnit 0 0)) *
        compress (frameUnit 0 0) exchangeUnitary (frameUnit 0 0) = 0 := by
  simp [frameUnit_star, frameUnit_mul, compressed_cut_zero]

theorem corner_identity_not_preserved :
    compress (frameUnit 0 0) exchangeUnitary (frameUnit 0 0) ≠ frameUnit 0 0 := by
  rw [compressed_cut_zero]
  exact (frameUnit_ne_zero 0 0).symm

/-- Two ambient exchanges restore the observed projection. -/
theorem double_exchange_compression :
    compress (frameUnit 0 0) (exchangeUnitary * exchangeUnitary)
      (frameUnit 0 0) = frameUnit 0 0 := by
  rw [exchangeUnitary_mul_self, compress_identity]
  simp [frameUnit_mul]

/-- Observing between the exchanges removes that nonzero input. -/
theorem iterated_exchange_compression :
    compress (frameUnit 0 0) exchangeUnitary
      (compress (frameUnit 0 0) exchangeUnitary (frameUnit 0 0)) = 0 := by
  rw [compressed_cut_zero, compress_zero]

theorem compression_composition_fails :
    compress (frameUnit 0 0) (exchangeUnitary * exchangeUnitary) (frameUnit 0 0) ≠
      compress (frameUnit 0 0) exchangeUnitary
        (compress (frameUnit 0 0) exchangeUnitary (frameUnit 0 0)) := by
  rw [double_exchange_compression, iterated_exchange_compression]
  exact frameUnit_ne_zero 0 0

/-- The two transitions and middle coefficient have their required supports. -/
theorem ordered_transition_support :
    projPos tripotent * frameUnit 0 2 * projZero tripotent = frameUnit 0 2 ∧
      projZero tripotent * frameUnit 2 3 * projZero tripotent = frameUnit 2 3 ∧
      projZero tripotent * frameUnit 3 1 * projNeg tripotent = frameUnit 3 1 := by
  simp [projPos_eq, projZero_eq, projNeg_eq, add_mul, mul_add, frameUnit_mul]

/-- Moving the middle coefficient before the first transition annihilates it. -/
theorem wrong_order_zero :
    frameUnit 2 3 * frameUnit 0 2 * frameUnit 3 1 = 0 := by
  simp [frameUnit_mul]

/-- The ordered path through two different zero-sector lines survives. -/
theorem ordered_product_eq :
    frameUnit 0 2 * frameUnit 2 3 * frameUnit 3 1 = frameUnit 0 1 := by
  simp [frameUnit_mul]

theorem ordered_product_ne_zero :
    frameUnit 0 2 * frameUnit 2 3 * frameUnit 3 1 ≠ 0 := by
  rw [ordered_product_eq]
  exact frameUnit_ne_zero 0 1

/-- The dense frame also realizes the two ordered outer inverse equations. -/
theorem outer_partial_inverses :
    frameUnit 0 1 * frameUnit 1 0 = projPos tripotent ∧
      frameUnit 1 0 * frameUnit 0 1 = projNeg tripotent := by
  simp [frameUnit_mul, projPos_eq, projNeg_eq]

/-- This sum lies in the existing odd part for the zero-sector cut. -/
theorem odd_witness_fixed :
    oddGrade (projZero tripotent) (frameUnit 0 2 + frameUnit 2 1) =
      frameUnit 0 2 + frameUnit 2 1 := by
  simp only [oddGrade, one_sub_projZero_eq_projPos_add_projNeg]
  simp [projZero_eq, projPos_eq, projNeg_eq, add_mul, mul_add,
    frameUnit_mul, add_comm]

/-- Opposite directed odd corners can compose into an extreme even corner. -/
theorem odd_witness_square :
    (frameUnit 0 2 + frameUnit 2 1) ^ 2 = frameUnit 0 1 := by
  simp [pow_two, add_mul, mul_add, frameUnit_mul]

theorem odd_witness_square_ne_zero :
    (frameUnit 0 2 + frameUnit 2 1) ^ 2 ≠ 0 := by
  rw [odd_witness_square]
  exact frameUnit_ne_zero 0 1

end InfoGeometry.Canonical.HorizonCompressionCounterexamples
