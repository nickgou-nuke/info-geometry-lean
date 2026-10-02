import InfoGeometry.Physics.ChiralPerturbation
import InfoGeometry.Physics.MagneticModulation
import InfoGeometry.Physics.ParticleGammaCorrelation
import InfoGeometry.Physics.CompoundChirality

namespace InfoGeometry.Physics.ChiralModelTests

open ChiralPerturbation MagneticModulation ParticleGammaCorrelation CompoundChirality

example : resonanceEnvelope 0 0 = 0 := by
  norm_num [resonanceEnvelope]

example : resonanceEnvelope 0 1 = 1 :=
  resonanceEnvelope_on_resonance 1 one_ne_zero

example : resonanceEnvelope 1 1 = 1 / 2 := by
  norm_num [resonanceEnvelope]

example (time : ℝ) : transitionProbability 1 1 time ≤ 1 / 2 := by
  have envelope_bound := transitionProbability_le_envelope 1 1 time
  norm_num [resonanceEnvelope] at envelope_bound
  exact envelope_bound

example (coupling time : ℝ) : transitionProbability 1 coupling time < 1 :=
  transitionProbability_lt_one_of_detuned 1 coupling time one_ne_zero

example : transitionProbability 0 1 0 = 0 := transitionProbability_initial 0 1

example : transitionProbability 0 1 Real.pi = 1 := by
  simpa using transitionProbability_pi_pulse 1 one_ne_zero

example : transitionProbability 0 1 (2 * Real.pi) = 0 := by
  simpa using transitionProbability_two_pi_pulse 1 one_ne_zero

example : signedReadout 1 0 1 ≠ signedReadout 1 0 (-1) :=
  zero_shift_does_not_remove_readout_separation 1 one_ne_zero

example : 0 < signedReadout 1 2 1 ∧ 0 < signedReadout 1 2 (-1) :=
  distinct_readouts_can_have_the_same_sign.2

example : phaseDifference 1 Real.pi 1 ≠ 0 ∧
    Real.cos (phaseDifference 1 Real.pi 1) = 1 ∧
    Real.sin (phaseDifference 1 Real.pi 1) = 0 := by
  refine ⟨(phaseDifference_ne_zero_iff _ _ _).mpr
    ⟨one_ne_zero, Real.pi_ne_zero, one_ne_zero⟩, ?_, ?_⟩ <;>
    simp [phaseDifference_eq]

example : signedCorrelation ![1, 0, 0] ![0, 1, 0] 1 = 0 := by
  norm_num [signedCorrelation, dotProduct, Fin.sum_univ_succ]

example : signedCorrelation ![1, 0, 0] ![1, 0, 0] 1 ≠
    signedCorrelation ![1, 0, 0] ![1, 0, 0] (-1) := by
  norm_num [signedCorrelation, dotProduct, Fin.sum_univ_succ]

example : rotationAfterReversal ![1, 2, 3] = ![1, -2, 3] := by
  simp [rotationAfterReversal_coordinates]

example : residualSpin ![1, 2, 3] ![1, 2, 3] = 0 :=
  residualSpin_can_vanish _

#print axioms resonanceEnvelope_eq_one_iff
#print axioms transitionProbability_bounds
#print axioms transitionProbability_le_envelope
#print axioms resonanceEnvelope_lt_one_of_detuned
#print axioms transitionProbability_lt_one_of_detuned
#print axioms transitionProbability_pi_pulse
#print axioms transitionProbability_two_pi_pulse
#print axioms resonance_does_not_give_time_independent_transfer
#print axioms readouts_distinct_iff
#print axioms opposite_signs_iff
#print axioms correlation_separates_iff
#print axioms nonzero_vectors_need_not_separate
#print axioms rotationAfterReversal_involutive
#print axioms rotationAfterReversal_need_not_negate_spin

end InfoGeometry.Physics.ChiralModelTests
