/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearTwistorTransition

/-!
# A nontrivial exact real sector with two normalized transitions

Take `a = 1`, `c = 0`, `g = 1`, and unit probe calibration. The constructed
dark state has energy `1`; the two constructed bright states have energies
`2` and `-1`. All three energies are off the eliminated pole `c = 0`.
The two operator strengths are `2/3` and `1/3`. These are exact values in a
chosen model energy unit, not assignments to measured nuclear levels.
The upper transition is upward in energy; these operator strengths are not
two spontaneous-decay branching probabilities.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearTwistorSectorExample

open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Twistor.RealSpectralAction
open InfoGeometry.Physics.NuclearTwistorConfigurationSector
open InfoGeometry.Physics.NuclearTwistorStationaryStates
open InfoGeometry.Physics.NuclearTwistorTransition

/-- Explicit nonzero-coupling stationary states, without a supplied spectral witness. -/
theorem three_stationary_states :
    Stationary fockForm (polynomialHamiltonian 1 0 1) (darkPolynomial 1 0 1) 1 ∧
    Stationary fockForm (polynomialHamiltonian 1 0 1) (brightPolynomial 0 1 2) 2 ∧
    Stationary fockForm (polynomialHamiltonian 1 0 1) (brightPolynomial 0 1 (-1)) (-1) := by
  exact ⟨darkPolynomial_stationary 1 0 1,
    brightPolynomial_stationary 1 0 1 2 (by norm_num) (by norm_num),
    brightPolynomial_stationary 1 0 1 (-1) (by norm_num) (by norm_num)⟩

theorem upper_transition_strength :
    polynomialMeasuredStrength 1 0 1 2 1 = 2 / 3 := by
  rw [polynomialMeasuredStrength_closed_form 1 0 1 2 1 (by norm_num)]
  norm_num

theorem lower_transition_strength :
    polynomialMeasuredStrength 1 0 1 (-1) 1 = 1 / 3 := by
  rw [polynomialMeasuredStrength_closed_form 1 0 1 (-1) 1 (by norm_num)]
  norm_num

/-- Unit total strength is established for this probe and initial state. -/
theorem two_bright_strengths_sum :
    polynomialMeasuredStrength 1 0 1 2 1 +
      polynomialMeasuredStrength 1 0 1 (-1) 1 = 1 := by
  rw [upper_transition_strength, lower_transition_strength]
  norm_num

theorem dual_two_bright_strengths_sum :
    dualMeasuredStrength 1 0 1 2 1 + dualMeasuredStrength 1 0 1 (-1) 1 = 1 := by
  rw [dualMeasuredStrength_eq, dualMeasuredStrength_eq,
    ← polynomialMeasuredStrength_eq, ← polynomialMeasuredStrength_eq]
  exact two_bright_strengths_sum

end InfoGeometry.Physics.NuclearTwistorSectorExample
