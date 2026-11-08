/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfigurationTransition
import InfoGeometry.Physics.NuclearDoubledConfiguration
import InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction
import InfoGeometry.Physics.NuclearRealClockTransitionStrength

/-!
# The three-configuration transition on the native real doubled carrier

Both external states occupy the same specified positive native leg. The
configuration maps and probe act on both legs through `pairedLift`. Positive
normalization and the two real clock quadratures recover the same operator
readout as the undoubled configuration calculation. The sheet grading remains
distinct from the Feshbach configuration split and from spatial parity.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfigurationDoubledTransition

open InfoGeometry.Krein
open InfoGeometry.Krein.BornRuleCore
open InfoGeometry.Physics.NuclearThreeConfiguration
open InfoGeometry.Physics.NuclearThreeConfigurationTransition
open InfoGeometry.Physics.NuclearDoubledConfiguration
open InfoGeometry.Physics.NuclearThreeConfigurationKreinReduction
open InfoGeometry.Physics.NuclearEffectiveObservables
open InfoGeometry.Physics.NuclearRealClockTransitionStrength

section PositiveLeg

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem metricWeight_pairedLift_positive (A : X →L[ℝ] Y) (x : X) :
    metricWeight (pairedLift A) (to_doubled x 0) = metricWeight A x := by
  calc
    metricWeight (pairedLift A) (to_doubled x 0) =
        inner ℝ (pairedLift A (to_doubled x 0))
          (pairedLift A (to_doubled x 0)) := by
      rw [metricWeight_eq_norm_sq, real_inner_self_eq_norm_sq]
    _ = inner ℝ (A x) (A x) := by
      simp [WithLp.prod_inner_apply, to_doubled]
    _ = metricWeight A x := by
      rw [metricWeight_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem normalizedState_pairedLift_positive (A : X →L[ℝ] Y) (x : X) :
    normalizedState (pairedLift A) (to_doubled x 0) =
      to_doubled (normalizedState A x) 0 := by
  unfold normalizedState
  rw [metricWeight_pairedLift_positive]
  apply DoubledSpace.ext <;>
    simp [WithLp.smul_fst, WithLp.smul_snd]

end PositiveLeg

private theorem configuration_zero_vector :
    (WithLp.toLp 2 ![0, 0, 0] : ConfigurationSpace) = 0 := by
  ext i
  fin_cases i <;> rfl

def darkDoubled : DoubledSpace ModelSpace := to_doubled darkModel 0
def brightDoubled : DoubledSpace ModelSpace := to_doubled brightModel 0

def doubledProbe (κ : ℝ) :
    DoubledSpace ConfigurationSpace →L[ℝ] DoubledSpace ConfigurationSpace :=
  pairedLift (probe κ)

theorem darkDoubled_positive : spectral_epsilon darkDoubled = darkDoubled := by
  simp [darkDoubled]

theorem brightDoubled_positive : spectral_epsilon brightDoubled = brightDoubled := by
  simp [brightDoubled]

theorem doubledProbe_comp_clockAxis (κ : ℝ) :
    (doubledProbe κ).comp clockAxis = clockAxis.comp (doubledProbe κ) :=
  pairedLift_comp_clockAxis (probe κ)

theorem doubled_metricWeight_dark (c g E : ℝ) :
    metricWeight (doubledGraphMap c g E) darkDoubled = 2 := by
  rw [doubledGraphMap, darkDoubled, metricWeight_pairedLift_positive,
    metricWeight_dark]

theorem doubled_metricWeight_bright (c g E : ℝ) :
    metricWeight (doubledGraphMap c g E) brightDoubled =
      2 + 4 * g ^ 2 / (E - c) ^ 2 := by
  rw [doubledGraphMap, brightDoubled, metricWeight_pairedLift_positive,
    metricWeight_bright]

theorem doubled_effective_matrix_element (a c g E κ : ℝ) :
    inner ℝ brightDoubled
        (effectiveOperator (doubledGraphMap c g a) (doubledGraphMap c g E)
          (doubledProbe κ) darkDoubled) = 2 * κ := by
  have h := effective_matrix_element a c g E κ
  rw [inner_effectiveOperator] at h ⊢
  simpa [doubledGraphMap, doubledProbe, darkDoubled, brightDoubled,
    WithLp.prod_inner_apply, to_doubled, configuration_zero_vector] using h

/-- Dark initial state at energy `a`, bright final state at energy `E`, both
on the same positive leg and normalized by their own induced metrics. -/
def doubledMeasuredStrength (a c g E κ : ℝ) : ℝ :=
  kreinAdaptedAmplitude
    (normalizedState (doubledGraphMap c g E) brightDoubled)
    (doubledProbe κ (normalizedState (doubledGraphMap c g a) darkDoubled)) ^ 2

theorem doubledMeasuredStrength_eq (a c g E κ : ℝ) :
    doubledMeasuredStrength a c g E κ = measuredStrength a c g E κ := by
  unfold doubledMeasuredStrength doubledGraphMap doubledProbe darkDoubled brightDoubled
  rw [normalizedState_pairedLift_positive, normalizedState_pairedLift_positive,
    kreinAdaptedAmplitude_eq_inner, pairedLift_to_doubled]
  simp [measuredStrength, WithLp.prod_inner_apply, to_doubled]

theorem doubledMeasuredStrength_closed_form (a c g E κ : ℝ) (hE : E ≠ c) :
    doubledMeasuredStrength a c g E κ =
      κ ^ 2 * (E - c) ^ 2 / ((E - c) ^ 2 + 2 * g ^ 2) := by
  rw [doubledMeasuredStrength_eq, measuredStrength_closed_form a c g E κ hE]

/-- The phase invariant readout uses the same two real external states. -/
def clockMeasuredStrength (a c g E κ : ℝ) : ℝ :=
  twoQuadratureStrength
    (normalizedState (doubledGraphMap c g E) brightDoubled)
    (doubledProbe κ (normalizedState (doubledGraphMap c g a) darkDoubled))

/-- On the specified common positive leg the second quadrature is zero. -/
theorem clockMeasuredStrength_eq (a c g E κ : ℝ) :
    clockMeasuredStrength a c g E κ = measuredStrength a c g E κ := by
  unfold clockMeasuredStrength doubledGraphMap doubledProbe darkDoubled brightDoubled
  rw [normalizedState_pairedLift_positive, normalizedState_pairedLift_positive,
    pairedLift_to_doubled]
  simp [twoQuadratureStrength, kreinAdaptedAmplitude_eq_inner,
    measuredStrength, clockAxis_to_doubled, WithLp.prod_inner_apply, to_doubled,
    configuration_zero_vector]

theorem clockMeasuredStrength_closed_form (a c g E κ : ℝ) (hE : E ≠ c) :
    clockMeasuredStrength a c g E κ =
      κ ^ 2 * (E - c) ^ 2 / ((E - c) ^ 2 + 2 * g ^ 2) := by
  rw [clockMeasuredStrength_eq, measuredStrength_closed_form a c g E κ hE]

end InfoGeometry.Physics.NuclearThreeConfigurationDoubledTransition
