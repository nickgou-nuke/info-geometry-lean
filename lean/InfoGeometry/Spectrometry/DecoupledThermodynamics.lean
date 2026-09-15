import InfoGeometry.Spectrometry.DecoupledThermodynamicRegression

namespace InfoGeometry.Spectrometry.DecoupledThermodynamics

open scoped BigOperators Topology
open Filter

noncomputable section

section IndependentStates

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

def stateBoltzmann (energy cutoff temperature : ℝ) (accepted : Bool) : ℝ :=
  if accepted then Real.exp (-energy / temperature) else Real.exp (-cutoff / temperature)

def stateProbability (energy cutoff temperature : ℝ) (accepted : Bool) : ℝ :=
  if accepted then lineWeight energy cutoff temperature
  else 1 - lineWeight energy cutoff temperature

def jointPartition (energies : Line → ℝ) (cutoff temperature : ℝ) : ℝ :=
  ∑ configuration : Line → Bool,
    ∏ line, stateBoltzmann (energies line) cutoff temperature (configuration line)

def jointProbability (energies : Line → ℝ) (cutoff temperature : ℝ)
    (configuration : Line → Bool) : ℝ :=
  ∏ line, stateProbability (energies line) cutoff temperature (configuration line)

theorem state_probability_pos (energy cutoff temperature : ℝ) (accepted : Bool) :
    0 < stateProbability energy cutoff temperature accepted := by
  cases accepted
  · exact sub_pos.mpr (line_weight_bounds energy cutoff temperature).2
  · exact (line_weight_bounds energy cutoff temperature).1

theorem state_probabilities_sum_one (energy cutoff temperature : ℝ) :
    ∑ accepted : Bool, stateProbability energy cutoff temperature accepted = 1 := by
  simp [stateProbability]

theorem joint_partition_factorization (energies : Line → ℝ) (cutoff temperature : ℝ) :
    jointPartition energies cutoff temperature =
      ∏ line, linePartition (energies line) cutoff temperature := by
  classical
  simpa [jointPartition, stateBoltzmann, linePartition, Fintype.sum_bool, add_comm] using
    (Fintype.prod_sum (fun line accepted =>
      stateBoltzmann (energies line) cutoff temperature accepted)).symm

theorem joint_partition_pos (energies : Line → ℝ) (cutoff temperature : ℝ) :
    0 < jointPartition energies cutoff temperature := by
  rw [joint_partition_factorization]
  exact Finset.prod_pos (fun line _ => line_partition_pos (energies line) cutoff temperature)

omit [DecidableEq Line] in
theorem joint_probability_pos (energies : Line → ℝ) (cutoff temperature : ℝ)
    (configuration : Line → Bool) :
    0 < jointProbability energies cutoff temperature configuration := by
  exact Finset.prod_pos (fun line _ =>
    state_probability_pos (energies line) cutoff temperature (configuration line))

theorem joint_probabilities_sum_one (energies : Line → ℝ) (cutoff temperature : ℝ) :
    ∑ configuration : Line → Bool,
      jointProbability energies cutoff temperature configuration = 1 := by
  classical
  unfold jointProbability
  rw [← Fintype.prod_sum]
  simp only [state_probabilities_sum_one, Finset.prod_const_one]

theorem state_probability_eq_normalized_boltzmann
    (energy cutoff temperature : ℝ) (accepted : Bool) :
    stateProbability energy cutoff temperature accepted =
      stateBoltzmann energy cutoff temperature accepted /
        linePartition energy cutoff temperature := by
  cases accepted
  · simp only [stateProbability, Bool.false_eq_true, if_false, stateBoltzmann]
    rw [line_weight_complement]
    simp [lineWeight, linePartition, add_comm]
  · rfl

theorem joint_probability_eq_normalized_boltzmann
    (energies : Line → ℝ) (cutoff temperature : ℝ) (configuration : Line → Bool) :
    jointProbability energies cutoff temperature configuration =
      (∏ line, stateBoltzmann (energies line) cutoff temperature (configuration line)) /
        jointPartition energies cutoff temperature := by
  simp only [jointProbability, state_probability_eq_normalized_boltzmann,
    Finset.prod_div_distrib, joint_partition_factorization]

theorem total_freeEnergy_eq_log_joint_partition
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    totalFreeEnergy energies cutoff temperature =
      -temperature * Real.log (jointPartition energies cutoff temperature) := by
  rw [joint_partition_factorization, Real.log_prod
    (fun line _ => ne_of_gt (line_partition_pos (energies line) cutoff temperature))]
  simp only [totalFreeEnergy, lineFreeEnergy, Finset.mul_sum]

theorem sum_product_bool_marginal
    (probability : Line → Bool → ℝ)
    (normalized : ∀ line, probability line false + probability line true = 1)
    (selected : Line) :
    (∑ configuration : Line → Bool,
      if configuration selected then ∏ line, probability line (configuration line) else 0) =
        probability selected true := by
  classical
  let restricted := fun line accepted =>
    if line = selected then (if accepted then probability line accepted else 0)
    else probability line accepted
  have term_identity (configuration : Line → Bool) :
      (if configuration selected then ∏ line, probability line (configuration line) else 0) =
        ∏ line, restricted line (configuration line) := by
    cases state_eq : configuration selected
    · simp only [Bool.false_eq_true, if_false]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ selected) (by simp [restricted, state_eq])
    · simp only [if_true]
      apply Finset.prod_congr rfl
      intro line _
      by_cases selected_eq : line = selected
      · simp [restricted, selected_eq, state_eq]
      · simp [restricted, selected_eq]
  simp_rw [term_identity]
  rw [← Fintype.prod_sum]
  have local_sum (line : Line) :
      (∑ accepted : Bool, restricted line accepted) =
        if line = selected then probability selected true else 1 := by
    by_cases selected_eq : line = selected
    · simp [restricted, selected_eq]
    · simp [restricted, selected_eq, normalized, add_comm]
  simp_rw [local_sum]
  simp

theorem joint_probability_marginal (energies : Line → ℝ) (cutoff temperature : ℝ)
    (selected : Line) :
    (∑ configuration : Line → Bool,
      if configuration selected then jointProbability energies cutoff temperature configuration
      else 0) = lineWeight (energies selected) cutoff temperature := by
  exact sum_product_bool_marginal
    (fun line accepted => stateProbability (energies line) cutoff temperature accepted)
    (fun line => by simp [stateProbability]) selected

theorem active_support_eq_expected_accepted_count
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    activeSupport energies cutoff temperature =
      ∑ configuration : Line → Bool,
        jointProbability energies cutoff temperature configuration *
          (∑ line, if configuration line then (1 : ℝ) else 0) := by
  simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun line _ =>
    (joint_probability_marginal energies cutoff temperature line).symm)

end IndependentStates

section DifferentialAndTemperature

theorem hasDerivAt_lineWeight (energy cutoff temperature : ℝ) :
    HasDerivAt (fun value => lineWeight value cutoff temperature)
      (-lineWeight energy cutoff temperature *
        (1 - lineWeight energy cutoff temperature) / temperature) energy := by
  have denominator_pos : 0 < 1 + Real.exp ((energy - cutoff) / temperature) := by positivity
  have raw_derivative :=
    (((((hasDerivAt_id energy).sub_const cutoff).div_const temperature).exp).const_add 1).inv
      (ne_of_gt denominator_pos)
  convert raw_derivative using 1
  · ext value
    simp [line_weight_eq_logistic, one_div]
  · simp only [line_weight_eq_logistic, id_eq]
    field_simp
    ring

theorem hasDerivAt_other_line_weight
    {Line : Type*} [DecidableEq Line]
    (energies : Line → ℝ) (cutoff temperature value : ℝ) (line other : Line)
    (distinct : line ≠ other) :
    HasDerivAt (fun replacement =>
      lineWeight ((Function.update energies other replacement) line) cutoff temperature) 0 value := by
  simpa only [Function.update_of_ne distinct] using
    hasDerivAt_const value (lineWeight (energies line) cutoff temperature)

theorem line_weight_lt_half_iff
    (energy cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    lineWeight energy cutoff temperature < 1 / 2 ↔ cutoff < energy := by
  rw [← not_le, line_weight_ge_half_iff energy cutoff temperature temperature_pos, not_le]

theorem tendsto_line_weight_high_temperature (energy cutoff : ℝ) :
    Tendsto (fun temperature => lineWeight energy cutoff temperature) atTop (𝓝 (1 / 2)) := by
  have gap_limit : Tendsto (fun temperature : ℝ => (energy - cutoff) / temperature)
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (energy - cutoff)
  convert (tendsto_const_nhds (x := (1 : ℝ))).div (gap_limit.rexp.const_add 1)
    (by norm_num : (1 : ℝ) + Real.exp 0 ≠ 0) using 1 <;>
    norm_num [line_weight_eq_logistic, Pi.div_def]

theorem tendsto_line_weight_low_temperature_of_lt
    (energy cutoff : ℝ) (below_cutoff : energy < cutoff) :
    Tendsto (fun temperature => lineWeight energy cutoff temperature) (𝓝[>] 0) (𝓝 1) := by
  have gap_limit : Tendsto (fun temperature : ℝ => temperature⁻¹ * (cutoff - energy))
      (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.atTop_mul_const (sub_pos.mpr below_cutoff)
  have exponential_limit :
      Tendsto (fun temperature : ℝ => Real.exp ((energy - cutoff) / temperature))
        (𝓝[>] 0) (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp gap_limit using 1
    ext temperature
    congr 1
    simp only [div_eq_mul_inv]
    ring
  simpa [line_weight_eq_logistic, Pi.div_def] using
    (tendsto_const_nhds (x := (1 : ℝ))).div (exponential_limit.const_add 1)
      (by norm_num : (1 : ℝ) + 0 ≠ 0)

theorem tendsto_line_weight_low_temperature_of_gt
    (energy cutoff : ℝ) (above_cutoff : cutoff < energy) :
    Tendsto (fun temperature => lineWeight energy cutoff temperature) (𝓝[>] 0) (𝓝 0) := by
  have complementary_limit :=
    (tendsto_line_weight_low_temperature_of_lt cutoff energy above_cutoff).const_sub 1
  simpa only [line_weight_complement, sub_self] using complementary_limit

end DifferentialAndTemperature

end

end InfoGeometry.Spectrometry.DecoupledThermodynamics
