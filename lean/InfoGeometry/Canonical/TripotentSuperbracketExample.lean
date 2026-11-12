/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentSuperbracket
import InfoGeometry.Canonical.TripotentMatrixExample

/-!
# Nonzero signed closure and middle-sector counterexamples

The existing dense four-by-four real matrix example supplies a tripotent and
transported matrix units retaining their full noncommutative multiplication.
The grade-one operator E02 + E21 has nonzero square E01, so its odd signed
self-bracket is a nonzero grade-two operator.

The negative-grade operator E12 survives right multiplication by the middle
projector. Thus the middle spectral sector is not automatically a vacuum
annihilated by negative grades. E00 has grade zero but is outside the middle
corner, so the zero adjoint grade is not just that corner. Noncommutativity
within grade zero is already owned by TripotentMatrixExample.
-/

noncomputable section

namespace InfoGeometry.Canonical.TripotentSuperbracketExample

open InfoGeometry.Canonical.TripotentMatrixExample
open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra.SupergradedBracket

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A two-step chain through the middle sector, in the existing dense frame. -/
def oddRaising : Mat := frameUnit 0 2 + frameUnit 2 1

theorem oddRaising_mem_posOne :
    oddRaising ∈ fiveGradeRange tripotent .posOne := by
  have h02 : frameUnit 0 2 ∈ fiveGradeRange tripotent .posOne := by
    rw [fiveGradeRange_eq_eigenspace tripotent_cube, Module.End.mem_eigenspace_iff]
    simpa [weight, fiveGradeValue] using ad_frameUnit 0 2
  have h21 : frameUnit 2 1 ∈ fiveGradeRange tripotent .posOne := by
    rw [fiveGradeRange_eq_eigenspace tripotent_cube, Module.End.mem_eigenspace_iff]
    simpa [weight, fiveGradeValue] using ad_frameUnit 2 1
  exact (fiveGradeRange tripotent .posOne).add_mem h02 h21

theorem oddRaising_sq :
    oddRaising * oddRaising = frameUnit 0 1 := by
  simp [oddRaising, add_mul, mul_add, frameUnit_mul]

theorem oddRaising_sq_ne_zero : oddRaising * oddRaising ≠ 0 := by
  rw [oddRaising_sq]
  exact frameUnit_ne_zero 0 1

/-- This odd self-bracket is nonzero; the ordinary self-commutator is zero. -/
theorem oddRaising_superBracket_self :
    superBracket (fiveGradeParity .posOne) (fiveGradeParity .posOne)
        oddRaising oddRaising = (2 : ℝ) • frameUnit 0 1 := by
  change oddRaising * oddRaising + oddRaising * oddRaising = _
  rw [oddRaising_sq, two_smul ℝ]

theorem oddRaising_superBracket_self_mem_posTwo :
    superBracket (fiveGradeParity .posOne) (fiveGradeParity .posOne)
        oddRaising oddRaising ∈ fiveGradeRange tripotent .posTwo := by
  exact superBracket_mem_fiveGradeRange tripotent_cube
    (by norm_num [fiveGradeValue]) oddRaising_mem_posOne oddRaising_mem_posOne

theorem oddRaising_superBracket_self_ne_zero :
    superBracket (fiveGradeParity .posOne) (fiveGradeParity .posOne)
        oddRaising oddRaising ≠ 0 := by
  rw [oddRaising_superBracket_self]
  exact smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (frameUnit_ne_zero 0 1)

theorem middleLowering_mem_negOne :
    frameUnit 1 2 ∈ fiveGradeRange tripotent .negOne := by
  rw [fiveGradeRange_eq_eigenspace tripotent_cube, Module.End.mem_eigenspace_iff]
  simpa [weight, fiveGradeValue] using ad_frameUnit 1 2

/-- A negative-grade map is nonzero on the middle spectral sector. -/
theorem middleLowering_mul_projZero :
    frameUnit 1 2 * projZero tripotent = frameUnit 1 2 := by
  rw [projZero_eq, mul_add]
  simp [frameUnit_mul]

theorem middleLowering_mul_projZero_ne_zero :
    frameUnit 1 2 * projZero tripotent ≠ 0 := by
  rw [middleLowering_mul_projZero]
  exact frameUnit_ne_zero 1 2

theorem positiveDiagonal_mem_zero :
    frameUnit 0 0 ∈ fiveGradeRange tripotent .zero := by
  rw [fiveGradeRange_eq_eigenspace tripotent_cube, Module.End.mem_eigenspace_iff]
  simpa [weight, fiveGradeValue] using ad_frameUnit 0 0

/-- The degree-zero subspace contains elements outside the middle corner. -/
theorem positiveDiagonal_not_middle_corner :
    ¬ ∃ X : Mat, projZero tripotent * X * projZero tripotent = frameUnit 0 0 := by
  rintro ⟨X, hX⟩
  have hEP : frameUnit 0 0 * projZero tripotent = 0 := by
    rw [projZero_eq, mul_add]
    simp [frameUnit_mul]
  apply frameUnit_ne_zero 0 0
  calc
    frameUnit 0 0 = frameUnit 0 0 * frameUnit 0 0 := by simp [frameUnit_mul]
    _ = frameUnit 0 0 * (projZero tripotent * X * projZero tripotent) := by rw [hX]
    _ = (frameUnit 0 0 * projZero tripotent) * X * projZero tripotent := by
      noncomm_ring
    _ = 0 := by rw [hEP]; simp

end InfoGeometry.Canonical.TripotentSuperbracketExample
