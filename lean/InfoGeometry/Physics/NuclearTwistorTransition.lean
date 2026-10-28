/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearTwistorStationaryStates
import InfoGeometry.Physics.NuclearThreeConfigurationDoubledTransition

/-!
# The same normalized transition on polynomial and genuine-dual states

The probe is a real polynomial number-conserving operator, not its eventual
scalar readout. Both external states have their own induced normalizations.
The operator matrix element is preserved by the actual embeddings before the
existing closed strength formula is applied. The complete basis sum rule is
the norm of the transition image, not an assumed unit probability.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearTwistorTransition

open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Twistor.RealDualTwistor
open InfoGeometry.Twistor.RealDualTwistorPositiveSector
open InfoGeometry.Physics.NuclearThreeConfiguration
open InfoGeometry.Physics.NuclearThreeConfigurationTransition
open InfoGeometry.Physics.NuclearThreeConfigurationDoubledTransition
open InfoGeometry.Physics.NuclearTwistorConfigurationSector
open InfoGeometry.Physics.NuclearTwistorStationaryStates

/-- This readout is defined from the polynomial probe and normalized external states. -/
def polynomialMeasuredStrength (a c g E κ : ℝ) : ℝ :=
  fockPairing (brightPolynomial c g E) (polynomialProbe κ (darkPolynomial a c g)) ^ 2

theorem polynomialMeasuredStrength_eq (a c g E κ : ℝ) :
    polynomialMeasuredStrength a c g E κ = measuredStrength a c g E κ := by
  unfold polynomialMeasuredStrength brightPolynomial darkPolynomial
  rw [polynomialProbe_embedding, euclideanEmbedding_pairing]
  rfl

theorem polynomialMeasuredStrength_closed_form (a c g E κ : ℝ) (hE : E ≠ c) :
    polynomialMeasuredStrength a c g E κ =
      κ ^ 2 * (E - c) ^ 2 / ((E - c) ^ 2 + 2 * g ^ 2) := by
  rw [polynomialMeasuredStrength_eq, measuredStrength_closed_form a c g E κ hE]

/-- The positive graph provides a genuine-dual matrix element with the same norm. -/
def dualMeasuredStrength (a c g E κ : ℝ) : ℝ :=
  neutralForm (positiveEmbedding (brightConfiguration c g E))
    (dualLift (probe κ).toLinearMap (positiveEmbedding (darkConfiguration a c g))) ^ 2

theorem dualMeasuredStrength_eq (a c g E κ : ℝ) :
    dualMeasuredStrength a c g E κ = measuredStrength a c g E κ := by
  unfold dualMeasuredStrength
  rw [positiveEmbedding_transition _ (probe_adjoint κ)]
  rfl

theorem dualMeasuredStrength_closed_form (a c g E κ : ℝ) (hE : E ≠ c) :
    dualMeasuredStrength a c g E κ =
      κ ^ 2 * (E - c) ^ 2 / ((E - c) ^ 2 + 2 * g ^ 2) := by
  rw [dualMeasuredStrength_eq, measuredStrength_closed_form a c g E κ hE]

/-- The existing doubled readout includes both real phase quadratures. -/
theorem polynomialMeasuredStrength_eq_clock (a c g E κ : ℝ) :
    polynomialMeasuredStrength a c g E κ = clockMeasuredStrength a c g E κ := by
  rw [polynomialMeasuredStrength_eq, clockMeasuredStrength_eq]

/-- For the specified positive representatives the graph and clock readouts agree.
This does not claim that clock rotation preserves the positive graph. -/
theorem dualMeasuredStrength_eq_clock (a c g E κ : ℝ) :
    dualMeasuredStrength a c g E κ = clockMeasuredStrength a c g E κ := by
  rw [dualMeasuredStrength_eq, clockMeasuredStrength_eq]

theorem polynomialMeasuredStrength_nonneg (a c g E κ : ℝ) :
    0 ≤ polynomialMeasuredStrength a c g E κ := sq_nonneg _

/-- Completeness over all three output configurations; arbitrary probes need not have unit sum. -/
theorem polynomialProbe_strength_sum (κ : ℝ) (x : ConfigurationSpace) :
    (∑ i : Fin 3,
      fockPairing (MvPolynomial.X i) (polynomialProbe κ (euclideanEmbedding x)) ^ 2) =
      fockPairing (polynomialProbe κ (euclideanEmbedding x))
        (polynomialProbe κ (euclideanEmbedding x)) := by
  rw [polynomialProbe_embedding, euclideanEmbedding_pairing,
    real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  simp only [fockPairing_X_left, euclideanEmbedding_apply,
    oneParticleCoeff_linearForm]

end InfoGeometry.Physics.NuclearTwistorTransition
