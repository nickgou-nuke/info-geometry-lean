/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TripotentMatrixExample
import InfoGeometry.OperatorAlgebra.PeirceSpine.HomogenizedFourierDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import Mathlib.Algebra.Group.Units.Basic

/-!
# Dense matrix witnesses for Peirce channel scope

All witnesses live in the existing full real four-by-four matrix algebra.
The transported matrix units have nonzero entries throughout and retain the
ordered matrix-unit product law. The witnesses distinguish independent
channels, an adjoint pair, and the selection of just one off-diagonal corner.

Nonvanishing of a Gram sum does not imply its invertibility. The singular
adjoint-paired witness below is an algebraic obstruction to a strictly positive
lower bound on the whole carrier; it does not assert a theorem about a physical
Hamiltonian or its positive spectral sector.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.PeirceChannelCounterexamples

open InfoGeometry.Canonical.TripotentMatrixExample
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- The rank-one cut used in the intake is a self-adjoint idempotent in the
dense frame. -/
theorem one_channel_cut :
    frameUnit 0 0 * frameUnit 0 0 = frameUnit 0 0 ∧
      star (frameUnit 0 0) = frameUnit 0 0 := by
  simp [frameUnit_mul, frameUnit_star]

/-- The two channels proposed as a zero-overlap example are valid corners. -/
theorem intake_pair_corners :
    conePlus (frameUnit 0 0) (frameUnit 0 1) = frameUnit 0 1 ∧
      coneMinus (frameUnit 0 0) (frameUnit 2 0) = frameUnit 2 0 := by
  constructor <;>
    simp [conePlus, coneMinus, mul_sub, sub_mul, frameUnit_mul]

/-- One multiplication order survives: the intake's proposed zero-overlap
pair has coupling `E₂₁`, using zero-based indices. -/
theorem intake_pair_metric :
    genV (frameUnit 0 0) (frameUnit 0 1) (frameUnit 2 0) = frameUnit 2 1 := by
  simp [genV, anticomm, intake_pair_corners.1, intake_pair_corners.2, frameUnit_mul]

theorem intake_pair_metric_ne_zero :
    genV (frameUnit 0 0) (frameUnit 0 1) (frameUnit 2 0) ≠ 0 := by
  rw [intake_pair_metric]
  exact frameUnit_ne_zero 2 1

/-- A rank-two cut gives a corrected independent-channel counterexample. -/
theorem disjoint_channel_cut :
    (frameUnit 0 0 + frameUnit 1 1) * (frameUnit 0 0 + frameUnit 1 1) =
        frameUnit 0 0 + frameUnit 1 1 ∧
      star (frameUnit 0 0 + frameUnit 1 1) = frameUnit 0 0 + frameUnit 1 1 := by
  constructor <;> simp [mul_add, add_mul, frameUnit_mul, star_add, frameUnit_star]

theorem disjoint_pair_corners :
    conePlus (frameUnit 0 0 + frameUnit 1 1) (frameUnit 0 2) = frameUnit 0 2 ∧
      coneMinus (frameUnit 0 0 + frameUnit 1 1) (frameUnit 3 1) = frameUnit 3 1 := by
  constructor <;>
    simp [conePlus, coneMinus, mul_add, add_mul, mul_sub, sub_mul, frameUnit_mul]

/-- Both independent off-diagonal channels are nonzero. -/
theorem disjoint_pair_nonzero :
    conePlus (frameUnit 0 0 + frameUnit 1 1) (frameUnit 0 2) ≠ 0 ∧
      coneMinus (frameUnit 0 0 + frameUnit 1 1) (frameUnit 3 1) ≠ 0 := by
  rw [disjoint_pair_corners.1, disjoint_pair_corners.2]
  exact ⟨frameUnit_ne_zero 0 2, frameUnit_ne_zero 3 1⟩

/-- Nonzero independent channels can annihilate in both orders. -/
theorem disjoint_pair_metric_zero :
    genV (frameUnit 0 0 + frameUnit 1 1) (frameUnit 0 2) (frameUnit 3 1) = 0 := by
  simp [genV, anticomm, disjoint_pair_corners.1, disjoint_pair_corners.2, frameUnit_mul]

/-- The adjoint-paired metric is a proper projection onto two dense-frame
directions, rather than an invertible operator on the whole matrix space. -/
theorem adjoint_pair_metric :
    genV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) =
      frameUnit 0 0 + frameUnit 1 1 := by
  simp [genV, anticomm, conePlus, coneMinus, frameUnit_star,
    mul_sub, sub_mul, frameUnit_mul]

theorem adjoint_pair_metric_ne_zero :
    genV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) ≠ 0 := by
  intro h
  have hProd := congrArg (fun X : Mat => X * frameUnit 0 0) h
  have hZero : frameUnit 0 0 = 0 := by
    simpa [adjoint_pair_metric, add_mul, frameUnit_mul] using hProd
  exact frameUnit_ne_zero 0 0 hZero

/-- The nonzero adjoint-paired metric has a nonzero right annihilator. -/
theorem adjoint_pair_metric_annihilator :
    genV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) * frameUnit 2 2 = 0 := by
  simp [adjoint_pair_metric, add_mul, frameUnit_mul]

/-- A positive Gram pairing can be nonzero and still singular. -/
theorem adjoint_pair_metric_not_isUnit :
    ¬ IsUnit (genV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1))) := by
  intro hUnit
  apply frameUnit_ne_zero 2 2
  apply hUnit.mul_left_cancel
  simpa only [mul_zero] using adjoint_pair_metric_annihilator

/-- A lower-only amplitude does not commute with the chosen cut. -/
theorem lower_amplitude_commutator_ne_zero :
    comm (frameUnit 0 0) (frameUnit 1 0) ≠ 0 := by
  simpa [InfoGeometry.OperatorAlgebra.PeirceSpine.comm, frameUnit_mul]
    using neg_ne_zero.mpr (frameUnit_ne_zero 1 0)

/-- Nevertheless, the selected upper channel and its adjoint are zero.
Thus nonzero `[P,A]` alone does not imply nonzero `genV P A (star A)`. -/
theorem lower_amplitude_selected_metric_zero :
    genV (frameUnit 0 0) (frameUnit 1 0) (star (frameUnit 1 0)) = 0 := by
  simp [genV, anticomm, conePlus, coneMinus, frameUnit_star,
    mul_sub, sub_mul, frameUnit_mul]

/-- The two mass-channel constructions differ on an operator outside the
centralizer of `V`. This consumes the generic ordered-commutator formula. -/
theorem mass_channel_discrepancy :
    hProjV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) (frameUnit 0 2) -
        fourierV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) (frameUnit 0 2) =
      (3 : ℤ) • frameUnit 0 2 := by
  rw [hProjV_sub_fourierV one_channel_cut.1]
  simp [adjoint_pair_metric, InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
    mul_add, add_mul, frameUnit_mul]

/-- Equality of the homogenized and Fourier mass channels cannot be
asserted on all elements of the ambient noncommutative algebra. -/
theorem mass_channels_ne :
    hProjV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) (frameUnit 0 2) ≠
      fourierV (frameUnit 0 0) (frameUnit 0 1) (star (frameUnit 0 1)) (frameUnit 0 2) := by
  intro h
  have hZero : (3 : ℤ) • frameUnit 0 2 = 0 := by
    rw [← mass_channel_discrepancy, h, sub_self]
  have hEntry := congrArg (fun X : Mat => X 0 0) hZero
  norm_num [Matrix.smul_apply, frameUnit_apply, reflection] at hEntry

end InfoGeometry.Canonical.PeirceChannelCounterexamples
