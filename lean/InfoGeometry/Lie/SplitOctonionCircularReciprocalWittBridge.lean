import InfoGeometry.Lie.SplitOctonionCircularReciprocalExponentialBridge
import InfoGeometry.Lie.SplitOctonionCircularWittForm
import InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
import InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
import InfoGeometry.Lie.SplitOctonionCircularAxialGrading

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
open InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
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

/- The reciprocal group law is realized by composition of the concrete flow. -/
theorem axialFlowCoordinate_add_from_reciprocalPair (s t : ℝ) :
    axialFlowCoordinate (s + t) =
      (axialFlowCoordinate s).comp (axialFlowCoordinate t) := by
  exact InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialFlowCoordinate_add
    s t

/-- The reciprocal axial flow as a quadratic isometry of circular coordinates. -/
noncomputable def axialFlowCoordinateQuadraticIsometry (t : ℝ) :
    circularPeirceQuadratic.IsometryEquiv circularPeirceQuadratic :=
  { hyperbolicFlowCoordinateEquiv t with
    map_app' := fun x => by
      change circularPeirceQuadratic (hyperbolicFlowCoordinate t x) =
        circularPeirceQuadratic x
      rw [← axialFlowCoordinate_eq_hyperbolicFlowCoordinate t]
      exact circularPeirceQuadratic_axialFlowCoordinate t x }

@[simp] theorem axialFlowCoordinateQuadraticIsometry_apply
    (t : ℝ) (x : Coordinate) :
    axialFlowCoordinateQuadraticIsometry t x = axialFlowCoordinate t x := by
  change hyperbolicFlowCoordinate t x = axialFlowCoordinate t x
  rw [axialFlowCoordinate_eq_hyperbolicFlowCoordinate]

@[simp] theorem axialFlowCoordinateQuadraticIsometry_preserves_form
    (t : ℝ) (x : Coordinate) :
    circularPeirceQuadratic (axialFlowCoordinateQuadraticIsometry t x) =
      circularPeirceQuadratic x :=
  QuadraticMap.IsometryEquiv.map_app
    (axialFlowCoordinateQuadraticIsometry t) x

/- The pair group law acts componentwise on every Witt channel. -/
theorem reciprocalExponentialPair_add_channel_scale
    (s t xPlus xMinus : ℝ) :
    ((reciprocalExponentialPair (s + t)).1 * xPlus,
      (reciprocalExponentialPair (s + t)).2 * xMinus) =
      ((reciprocalExponentialPair s).1 *
          ((reciprocalExponentialPair t).1 * xPlus),
       (reciprocalExponentialPair s).2 *
          ((reciprocalExponentialPair t).2 * xMinus)) := by
  rw [reciprocalExponentialPair_add]
  apply Prod.ext <;> ring

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

theorem circularWittNorm_axialFlow_from_reciprocalPair
    (t : ℝ) (x : Coordinate) :
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

end InfoGeometry.Lie.SplitOctonionCircularReciprocalWittBridge
