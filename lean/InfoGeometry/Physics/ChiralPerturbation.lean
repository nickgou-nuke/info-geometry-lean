import InfoGeometry.Physics.ThoriumIsomericChiralRotor
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace InfoGeometry.Physics.ChiralPerturbation

noncomputable section

def resonanceEnvelope (detuning coupling : ℝ) : ℝ :=
  coupling ^ 2 / (detuning ^ 2 + coupling ^ 2)

theorem resonanceEnvelope_nonneg (detuning coupling : ℝ) :
    0 ≤ resonanceEnvelope detuning coupling :=
  div_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem resonanceEnvelope_le_one (detuning coupling : ℝ) :
    resonanceEnvelope detuning coupling ≤ 1 := by
  unfold resonanceEnvelope
  by_cases denominator_zero : detuning ^ 2 + coupling ^ 2 = 0
  · simp [denominator_zero]
  · apply (div_le_one (lt_of_le_of_ne
      (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm denominator_zero))).mpr
    linarith [sq_nonneg detuning]

theorem resonanceEnvelope_on_resonance (coupling : ℝ) (coupling_ne : coupling ≠ 0) :
    resonanceEnvelope 0 coupling = 1 := by
  simp [resonanceEnvelope, pow_ne_zero 2 coupling_ne]

theorem resonanceEnvelope_eq_one_iff (detuning coupling : ℝ) (coupling_ne : coupling ≠ 0) :
    resonanceEnvelope detuning coupling = 1 ↔ detuning = 0 := by
  have denominator_pos : 0 < detuning ^ 2 + coupling ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero coupling_ne)
  unfold resonanceEnvelope
  rw [div_eq_one_iff_eq (ne_of_gt denominator_pos)]
  constructor
  · intro equal
    have square_zero : detuning ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp square_zero
  · rintro rfl
    ring

def transitionProbability (detuning coupling time : ℝ) : ℝ :=
  resonanceEnvelope detuning coupling *
    Thorium229.rabiTransitionProb (Real.sqrt (detuning ^ 2 + coupling ^ 2) * time)

theorem transitionProbability_le_envelope (detuning coupling time : ℝ) :
    transitionProbability detuning coupling time ≤ resonanceEnvelope detuning coupling := by
  have oscillation := Thorium229.rabi_prob_bounds
    (Real.sqrt (detuning ^ 2 + coupling ^ 2) * time)
  simpa [transitionProbability] using
    mul_le_mul_of_nonneg_left oscillation.2 (resonanceEnvelope_nonneg detuning coupling)

theorem resonanceEnvelope_lt_one_of_detuned
    (detuning coupling : ℝ) (detuning_ne : detuning ≠ 0) :
    resonanceEnvelope detuning coupling < 1 := by
  have detuning_square_pos : 0 < detuning ^ 2 := sq_pos_of_ne_zero detuning_ne
  have denominator_pos : 0 < detuning ^ 2 + coupling ^ 2 :=
    add_pos_of_pos_of_nonneg detuning_square_pos (sq_nonneg coupling)
  unfold resonanceEnvelope
  apply (div_lt_one denominator_pos).mpr
  linarith

theorem transitionProbability_lt_one_of_detuned
    (detuning coupling time : ℝ) (detuning_ne : detuning ≠ 0) :
    transitionProbability detuning coupling time < 1 :=
  (transitionProbability_le_envelope detuning coupling time).trans_lt
    (resonanceEnvelope_lt_one_of_detuned detuning coupling detuning_ne)

theorem transitionProbability_bounds (detuning coupling time : ℝ) :
    0 ≤ transitionProbability detuning coupling time ∧
      transitionProbability detuning coupling time ≤ 1 := by
  have envelope_nonneg := resonanceEnvelope_nonneg detuning coupling
  have envelope_le := resonanceEnvelope_le_one detuning coupling
  have oscillation := Thorium229.rabi_prob_bounds
    (Real.sqrt (detuning ^ 2 + coupling ^ 2) * time)
  constructor
  · exact mul_nonneg envelope_nonneg oscillation.1
  · exact (mul_le_mul envelope_le oscillation.2 oscillation.1 zero_le_one).trans_eq (one_mul 1)

theorem transitionProbability_initial (detuning coupling : ℝ) :
    transitionProbability detuning coupling 0 = 0 := by
  simp [transitionProbability, Thorium229.rabiTransitionProb]

theorem transitionProbability_on_resonance (coupling time : ℝ) (coupling_ne : coupling ≠ 0) :
    transitionProbability 0 coupling time = Thorium229.rabiTransitionProb (|coupling| * time) := by
  simp [transitionProbability, resonanceEnvelope_on_resonance coupling coupling_ne,
    Real.sqrt_sq_eq_abs]

theorem transitionProbability_pi_pulse (coupling : ℝ) (coupling_ne : coupling ≠ 0) :
    transitionProbability 0 coupling (Real.pi / |coupling|) = 1 := by
  rw [transitionProbability_on_resonance coupling _ coupling_ne]
  have angle : |coupling| * (Real.pi / |coupling|) = Real.pi := by
    field_simp [abs_ne_zero.mpr coupling_ne]
  rw [angle]
  exact Thorium229.rabi_pi_pulse

theorem transitionProbability_two_pi_pulse (coupling : ℝ) (coupling_ne : coupling ≠ 0) :
    transitionProbability 0 coupling (2 * Real.pi / |coupling|) = 0 := by
  rw [transitionProbability_on_resonance coupling _ coupling_ne]
  have angle : |coupling| * (2 * Real.pi / |coupling|) = 2 * Real.pi := by
    field_simp [abs_ne_zero.mpr coupling_ne]
  rw [angle]
  simp [Thorium229.rabiTransitionProb]

theorem resonance_does_not_give_time_independent_transfer
    (coupling : ℝ) (coupling_ne : coupling ≠ 0) :
    ∃ first second : ℝ,
      transitionProbability 0 coupling first ≠ transitionProbability 0 coupling second := by
  refine ⟨0, Real.pi / |coupling|, ?_⟩
  rw [transitionProbability_initial, transitionProbability_pi_pulse coupling coupling_ne]
  exact zero_ne_one

end

end InfoGeometry.Physics.ChiralPerturbation
