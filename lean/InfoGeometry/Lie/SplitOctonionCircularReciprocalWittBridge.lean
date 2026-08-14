import InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge
import InfoGeometry.Lie.SplitOctonionCircularWittForm

/-!
# Reciprocal exponential readout of the circular Witt flow

This file is the consumer edge from the reciprocal exponential pair to the
already-defined circular axial flow.  It records the positive, negative, and
central channel scalings and derives the opposite-channel invariance of the
Witt form.  No compactification or physical interpretation is introduced.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularReciprocalWittBridge

open InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
open InfoGeometry.Lie.SplitOctonionCircularWittForm

abbrev Coordinate := Fin 8 → ℝ

theorem axialFlowCoordinate_eq_hyperbolicFlowCoordinate (t : ℝ) :
    axialFlowCoordinate t = hyperbolicFlowCoordinate t := by
  have hweight : ∀ i : Fin 8,
      InfoGeometry.Lie.SplitOctonionCircularAxialGrading.axialWeight i =
        InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialWeight i := by
    intro i
    fin_cases i <;> rfl
  ext x i
  simp [axialFlowCoordinate_apply, hyperbolicFlowCoordinate_apply, hweight]

theorem axialFlowCoordinate_positiveChannel (t : ℝ) (x : Coordinate)
    (i : Fin 3) :
    axialFlowCoordinate t x ⟨i.val + 1, by omega⟩ =
      (reciprocalExponentialPair t).1 * x ⟨i.val + 1, by omega⟩ := by
  fin_cases i <;> simp [axialFlowCoordinate_apply, reciprocalExponentialPair,
    axialWeight]

theorem axialFlowCoordinate_negativeChannel (t : ℝ) (x : Coordinate)
    (i : Fin 3) :
    axialFlowCoordinate t x ⟨i.val + 5, by omega⟩ =
      (reciprocalExponentialPair t).2 * x ⟨i.val + 5, by omega⟩ := by
  fin_cases i <;> simp [axialFlowCoordinate_apply, reciprocalExponentialPair,
    axialWeight]

theorem axialFlowCoordinate_zeroChannel (t : ℝ) (x : Coordinate) :
    axialFlowCoordinate t x 0 = x 0 := by
  simp [axialFlowCoordinate_apply, axialWeight]

theorem axialFlowCoordinate_fourChannel (t : ℝ) (x : Coordinate) :
    axialFlowCoordinate t x 4 = x 4 := by
  simp [axialFlowCoordinate_apply, axialWeight]

theorem reciprocalExponentialPair_zero_axialFlowCoordinate_zero :
    reciprocalExponentialPair 0 = (1, 1) ∧
      axialFlowCoordinate 0 =
        (LinearMap.id : Coordinate →ₗ[ℝ] Coordinate) := by
  exact ⟨reciprocalExponentialPair_zero, axialFlowCoordinate_zero⟩

theorem axialFlowCoordinate_oppositePair_invariant
    (t : ℝ) (x : Coordinate) (i : Fin 3) :
    axialFlowCoordinate t x ⟨i.val + 1, by omega⟩ *
        axialFlowCoordinate t x ⟨i.val + 5, by omega⟩ =
      x ⟨i.val + 1, by omega⟩ * x ⟨i.val + 5, by omega⟩ := by
  rw [axialFlowCoordinate_positiveChannel,
    axialFlowCoordinate_negativeChannel]
  exact reciprocal_exponential_channel_invariant
    (x ⟨i.val + 1, by omega⟩)
    (x ⟨i.val + 5, by omega⟩) t

theorem circularWittNorm_axialFlow_reciprocal (t : ℝ) (x : Coordinate) :
    circularWittNorm (axialFlowCoordinate t x) = circularWittNorm x := by
  rw [circularWittNorm]
  rw [axialFlowCoordinate_zeroChannel, axialFlowCoordinate_fourChannel]
  have h₀ : axialFlowCoordinate t x 1 * axialFlowCoordinate t x 5 = x 1 * x 5 := by
    simpa using axialFlowCoordinate_oppositePair_invariant t x 0
  have h₁ : axialFlowCoordinate t x 2 * axialFlowCoordinate t x 6 = x 2 * x 6 := by
    simpa using axialFlowCoordinate_oppositePair_invariant t x 1
  have h₂ : axialFlowCoordinate t x 3 * axialFlowCoordinate t x 7 = x 3 * x 7 := by
    simpa using axialFlowCoordinate_oppositePair_invariant t x 2
  rw [h₀, h₁, h₂]
  rfl

theorem circularWittNorm_axialFlow_from_reciprocalPair
    (t : ℝ) (x : Coordinate) :
    circularWittNorm (axialFlowCoordinate t x) = circularWittNorm x :=
  circularWittNorm_axialFlow_reciprocal t x

end InfoGeometry.Lie.SplitOctonionCircularReciprocalWittBridge
