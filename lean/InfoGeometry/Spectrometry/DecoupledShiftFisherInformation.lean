import InfoGeometry.Spectrometry.DecoupledThermodynamicGeometry

namespace InfoGeometry.Spectrometry.DecoupledThermodynamics

open scoped BigOperators
open InfoGeometry.Spectrometry.FiniteWeightDispersion

noncomputable section

theorem hasDerivAt_log_stateProbability (energy cutoff temperature : ℝ) (accepted : Bool) :
    HasDerivAt (fun value => Real.log (stateProbability value cutoff temperature accepted))
      ((lineWeight energy cutoff temperature - acceptedIndicator accepted) / temperature) energy := by
  have weight_pos := (line_weight_bounds energy cutoff temperature).1
  have complement_pos := sub_pos.mpr (line_weight_bounds energy cutoff temperature).2
  cases accepted
  · simp only [stateProbability, acceptedIndicator, Bool.false_eq_true, if_false, sub_zero]
    convert ((hasDerivAt_lineWeight energy cutoff temperature).const_sub 1).log
      (ne_of_gt complement_pos) using 1
    field_simp
  · simp only [stateProbability, acceptedIndicator, if_true]
    convert (hasDerivAt_lineWeight energy cutoff temperature).log
      (ne_of_gt weight_pos) using 1
    field_simp
    ring

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

omit [DecidableEq Line] in
theorem log_joint_probability_eq_sum (energies : Line → ℝ) (cutoff temperature : ℝ)
    (configuration : Line → Bool) :
    Real.log (jointProbability energies cutoff temperature configuration) =
      ∑ line, Real.log (stateProbability (energies line) cutoff temperature (configuration line)) := by
  exact Real.log_prod (fun line _ =>
    ne_of_gt (state_probability_pos (energies line) cutoff temperature (configuration line)))

omit [DecidableEq Line] in
theorem hasDerivAt_log_jointProbability_common_shift
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (configuration : Line → Bool) :
    HasDerivAt (fun offset =>
      Real.log (jointProbability (fun line => energies line + offset) cutoff temperature configuration))
      ((activeSupport (fun line => energies line + shift) cutoff temperature -
        acceptedCount configuration) / temperature) shift := by
  simp_rw [log_joint_probability_eq_sum]
  have line_derivative (line : Line) :
      HasDerivAt (fun offset =>
        Real.log (stateProbability (energies line + offset) cutoff temperature (configuration line)))
        ((lineWeight (energies line + shift) cutoff temperature -
          acceptedIndicator (configuration line)) / temperature) shift := by
    simpa using
      (hasDerivAt_log_stateProbability (energies line + shift) cutoff temperature
        (configuration line)).comp shift ((hasDerivAt_id shift).const_add (energies line))
  simpa only [activeSupport, acceptedCount, ← Finset.sum_div, Finset.sum_sub_distrib] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun line _ => line_derivative line)

def commonShiftScore (energies : Line → ℝ) (cutoff temperature shift : ℝ)
    (configuration : Line → Bool) : ℝ :=
  deriv (fun offset =>
    Real.log (jointProbability (fun line => energies line + offset) cutoff temperature configuration))
    shift

omit [DecidableEq Line] in
theorem common_shift_score_eq (energies : Line → ℝ) (cutoff temperature shift : ℝ)
    (configuration : Line → Bool) :
    commonShiftScore energies cutoff temperature shift configuration =
      (activeSupport (fun line => energies line + shift) cutoff temperature -
        acceptedCount configuration) / temperature :=
  (hasDerivAt_log_jointProbability_common_shift energies cutoff temperature shift configuration).deriv

def commonShiftFisherInformation (energies : Line → ℝ) (cutoff temperature shift : ℝ) : ℝ :=
  jointExpectation (fun line => energies line + shift) cutoff temperature
    (fun configuration => commonShiftScore energies cutoff temperature shift configuration ^ 2)

theorem common_shift_fisher_eq_variance_div_temperature_sq
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) :
    commonShiftFisherInformation energies cutoff temperature shift =
      acceptedCountVariance (fun line => energies line + shift) cutoff temperature / temperature ^ 2 := by
  unfold commonShiftFisherInformation
  simp_rw [common_shift_score_eq]
  rw [accepted_count_variance_eq_centered_moment]
  unfold jointExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro configuration _
  ring

theorem common_shift_fisher_eq_susceptibility_div_temperature
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (temperature_pos : 0 < temperature) :
    commonShiftFisherInformation energies cutoff temperature shift =
      shiftSusceptibility energies cutoff temperature shift / temperature := by
  rw [common_shift_fisher_eq_variance_div_temperature_sq,
    shift_susceptibility_eq_variance_div_temperature energies cutoff temperature shift temperature_pos]
  ring

theorem common_shift_fisher_pos [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (temperature_ne : temperature ≠ 0) :
    0 < commonShiftFisherInformation energies cutoff temperature shift := by
  rw [common_shift_fisher_eq_variance_div_temperature_sq]
  exact div_pos (accepted_count_variance_pos _ _ _) (sq_pos_of_ne_zero temperature_ne)

theorem common_shift_fisher_le_state_envelope [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) :
    commonShiftFisherInformation energies cutoff temperature shift ≤
      varianceEnvelope (Fintype.card Line)
        (activeSupport (fun line => energies line + shift) cutoff temperature) / temperature ^ 2 := by
  rw [common_shift_fisher_eq_variance_div_temperature_sq]
  exact div_le_div_of_nonneg_right
    (accepted_count_variance_le_state_envelope _ _ _) (sq_nonneg temperature)

theorem common_shift_geometry [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature shift : ℝ) (temperature_pos : 0 < temperature) :
    let shifted := fun line => energies line + shift
    let support := activeSupport shifted cutoff temperature
    let count := (Fintype.card Line : ℝ)
    let variance := acceptedCountVariance shifted cutoff temperature
    let weights := fun line => lineWeight (shifted line) cutoff temperature
    variance = support - squaredWeightSum weights ∧
    support * (1 - support / count) - variance = dispersion weights ∧
    variance ≤ support * (1 - support / count) ∧
    support * (1 - support / count) ≤ count / 4 ∧
    -deriv (deriv (shiftedFreeEnergy energies cutoff temperature)) shift = variance / temperature ∧
    commonShiftFisherInformation energies cutoff temperature shift = variance / temperature ^ 2 := by
  exact ⟨accepted_count_variance_decomposition _ _ _,
    accepted_count_envelope_defect _ _ _,
    accepted_count_variance_le_state_envelope _ _ _,
    envelope_le_quarter _ _ Fintype.card_pos,
    shift_susceptibility_eq_variance_div_temperature energies cutoff temperature shift temperature_pos,
    common_shift_fisher_eq_variance_div_temperature_sq energies cutoff temperature shift⟩

end

end InfoGeometry.Spectrometry.DecoupledThermodynamics
