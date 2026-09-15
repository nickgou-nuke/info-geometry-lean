import InfoGeometry.Spectrometry.DecoupledBernoulliMoments
import Mathlib.Analysis.Convex.Deriv

namespace InfoGeometry.Spectrometry.DecoupledThermodynamics

open scoped BigOperators Topology
open Filter

namespace FluctuationDependency

inductive Archetype
  | productMeasure
  | countVariance
  | freeEnergyDerivative
  | weightDerivative
  | susceptibility
  | varianceBound
  | weightLimits
  | varianceLimits
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | productMeasure => {productMeasure}
  | countVariance => {productMeasure, countVariance}
  | freeEnergyDerivative => {freeEnergyDerivative}
  | weightDerivative => {weightDerivative}
  | susceptibility =>
      {productMeasure, countVariance, freeEnergyDerivative, weightDerivative, susceptibility}
  | varianceBound => {productMeasure, countVariance, varianceBound}
  | weightLimits => {weightLimits}
  | varianceLimits => {productMeasure, countVariance, weightLimits, varianceLimits}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem dependency_branches :
    productMeasure ≤ countVariance ∧
    countVariance ≤ susceptibility ∧
    freeEnergyDerivative ≤ susceptibility ∧
    weightDerivative ≤ susceptibility ∧
    countVariance ≤ varianceBound ∧
    countVariance ≤ varianceLimits ∧
    weightLimits ≤ varianceLimits := by
  change
    prerequisites productMeasure ⊆ prerequisites countVariance ∧
    prerequisites countVariance ⊆ prerequisites susceptibility ∧
    prerequisites freeEnergyDerivative ⊆ prerequisites susceptibility ∧
    prerequisites weightDerivative ⊆ prerequisites susceptibility ∧
    prerequisites countVariance ⊆ prerequisites varianceBound ∧
    prerequisites countVariance ⊆ prerequisites varianceLimits ∧
    prerequisites weightLimits ⊆ prerequisites varianceLimits
  decide

theorem bounds_and_limits_incomparable :
    ¬ varianceBound ≤ varianceLimits ∧ ¬ varianceLimits ≤ varianceBound := by
  change ¬ prerequisites varianceBound ⊆ prerequisites varianceLimits ∧
    ¬ prerequisites varianceLimits ⊆ prerequisites varianceBound
  decide

end FluctuationDependency

noncomputable section

section ScalarCalculus

theorem hasDerivAt_lineFreeEnergy (energy cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) :
    HasDerivAt (fun value => lineFreeEnergy value cutoff temperature)
      (lineWeight energy cutoff temperature) energy := by
  have derivative := hasFDerivAt_lineFreeEnergy _ _ energy cutoff temperature
    temperature_pos (hasDerivAt_id energy).hasFDerivAt
  simpa [smul_eq_mul] using derivative.hasDerivAt

theorem deriv_lineFreeEnergy (energy cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) :
    deriv (fun value => lineFreeEnergy value cutoff temperature) energy =
      lineWeight energy cutoff temperature :=
  (hasDerivAt_lineFreeEnergy energy cutoff temperature temperature_pos).deriv

theorem deriv_lineFreeEnergy_eq (cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) :
    deriv (fun energy => lineFreeEnergy energy cutoff temperature) =
      fun energy => lineWeight energy cutoff temperature := by
  funext energy
  exact deriv_lineFreeEnergy energy cutoff temperature temperature_pos

theorem hasDerivAt_deriv_lineFreeEnergy (energy cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) :
    HasDerivAt (deriv (fun value => lineFreeEnergy value cutoff temperature))
      (-lineWeight energy cutoff temperature *
        (1 - lineWeight energy cutoff temperature) / temperature) energy := by
  rw [deriv_lineFreeEnergy_eq cutoff temperature temperature_pos]
  exact hasDerivAt_lineWeight energy cutoff temperature

theorem second_derivative_lineFreeEnergy_neg (energy cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) :
    deriv (deriv (fun value => lineFreeEnergy value cutoff temperature)) energy < 0 := by
  rw [(hasDerivAt_deriv_lineFreeEnergy energy cutoff temperature temperature_pos).deriv]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (line_weight_bounds energy cutoff temperature).1)
      (sub_pos.mpr (line_weight_bounds energy cutoff temperature).2)) temperature_pos

theorem strictConcaveOn_lineFreeEnergy (cutoff temperature : ℝ)
    (temperature_pos : 0 < temperature) :
    StrictConcaveOn ℝ Set.univ (fun energy => lineFreeEnergy energy cutoff temperature) := by
  have continuous : Continuous (fun energy => lineFreeEnergy energy cutoff temperature) :=
    continuous_iff_continuousAt.mpr (fun energy =>
      (hasDerivAt_lineFreeEnergy energy cutoff temperature temperature_pos).continuousAt)
  apply StrictAnti.strictConcaveOn_univ_of_deriv continuous
  rw [deriv_lineFreeEnergy_eq cutoff temperature temperature_pos]
  exact line_weight_strictAnti cutoff temperature temperature_pos

theorem bernoulli_variance_le_quarter (probability : ℝ) :
    probability * (1 - probability) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (probability - 1 / 2)]

theorem bernoulli_variance_eq_quarter_iff (probability : ℝ) :
    probability * (1 - probability) = 1 / 4 ↔ probability = 1 / 2 := by
  constructor
  · intro equality
    nlinarith [sq_nonneg (probability - 1 / 2)]
  · intro equality
    rw [equality]
    norm_num

end ScalarCalculus

section CountFluctuations

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

theorem accepted_count_variance_nonneg (energies : Line → ℝ) (cutoff temperature : ℝ) :
    0 ≤ acceptedCountVariance energies cutoff temperature := by
  rw [accepted_count_variance_eq_sum]
  exact Finset.sum_nonneg (fun line _ => mul_nonneg
    (line_weight_bounds (energies line) cutoff temperature).1.le
    (sub_nonneg.mpr (line_weight_bounds (energies line) cutoff temperature).2.le))

theorem accepted_count_variance_pos [Nonempty Line]
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    0 < acceptedCountVariance energies cutoff temperature := by
  rw [accepted_count_variance_eq_sum]
  exact Finset.sum_pos (fun line _ => mul_pos
    (line_weight_bounds (energies line) cutoff temperature).1
    (sub_pos.mpr (line_weight_bounds (energies line) cutoff temperature).2)) Finset.univ_nonempty

theorem accepted_count_variance_le_quarter_card
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    acceptedCountVariance energies cutoff temperature ≤ (Fintype.card Line : ℝ) / 4 := by
  rw [accepted_count_variance_eq_sum]
  calc
    _ ≤ ∑ _line : Line, (1 / 4 : ℝ) :=
      Finset.sum_le_sum (fun line _ =>
        bernoulli_variance_le_quarter (lineWeight (energies line) cutoff temperature))
    _ = (Fintype.card Line : ℝ) / 4 := by simp [div_eq_mul_inv]

theorem accepted_count_variance_at_cutoff (cutoff temperature : ℝ) :
    acceptedCountVariance (fun _line : Line => cutoff) cutoff temperature =
      (Fintype.card Line : ℝ) / 4 := by
  simp [accepted_count_variance_eq_sum, line_weight_at_cutoff]
  ring

theorem accepted_count_fluctuation_response
    (energies : Line → ℝ) (cutoff temperature : ℝ) (temperature_ne : temperature ≠ 0) :
    acceptedCountVariance energies cutoff temperature =
      -temperature * ∑ line,
        deriv (fun energy => lineWeight energy cutoff temperature) (energies line) := by
  rw [accepted_count_variance_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro line _
  rw [(hasDerivAt_lineWeight (energies line) cutoff temperature).deriv]
  field_simp

theorem accepted_count_variance_eq_freeEnergy_curvature
    (energies : Line → ℝ) (cutoff temperature : ℝ) (temperature_pos : 0 < temperature) :
    acceptedCountVariance energies cutoff temperature =
      -temperature * ∑ line,
        deriv (deriv (fun energy => lineFreeEnergy energy cutoff temperature)) (energies line) := by
  rw [deriv_lineFreeEnergy_eq cutoff temperature temperature_pos]
  exact accepted_count_fluctuation_response energies cutoff temperature (ne_of_gt temperature_pos)

theorem hasDerivAt_activeSupport_common_shift
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    HasDerivAt (fun shift =>
      activeSupport (fun line => energies line + shift) cutoff temperature)
      (-acceptedCountVariance energies cutoff temperature / temperature) 0 := by
  have line_derivative (line : Line) :
      HasDerivAt (fun shift => lineWeight (energies line + shift) cutoff temperature)
        (-lineWeight (energies line) cutoff temperature *
          (1 - lineWeight (energies line) cutoff temperature) / temperature) 0 := by
    simpa using (hasDerivAt_lineWeight (energies line + 0) cutoff temperature).comp 0
      ((hasDerivAt_id (0 : ℝ)).const_add (energies line))
  convert HasDerivAt.fun_sum (fun line _ => line_derivative line) using 1
  simp only [accepted_count_variance_eq_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib, neg_mul]

theorem accepted_count_variance_eq_shift_susceptibility
    (energies : Line → ℝ) (cutoff temperature : ℝ) (temperature_ne : temperature ≠ 0) :
    acceptedCountVariance energies cutoff temperature =
      -temperature * deriv (fun shift =>
        activeSupport (fun line => energies line + shift) cutoff temperature) 0 := by
  rw [(hasDerivAt_activeSupport_common_shift energies cutoff temperature).deriv]
  field_simp

end CountFluctuations

section TemperatureLimits

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

theorem tendsto_accepted_count_variance_high_temperature
    (energies : Line → ℝ) (cutoff : ℝ) :
    Tendsto (fun temperature => acceptedCountVariance energies cutoff temperature)
      atTop (𝓝 ((Fintype.card Line : ℝ) / 4)) := by
  have line_limit (line : Line) :=
    (tendsto_line_weight_high_temperature (energies line) cutoff).mul
      ((tendsto_line_weight_high_temperature (energies line) cutoff).const_sub 1)
  have sum_limit := tendsto_finset_sum Finset.univ (fun line _ => line_limit line)
  convert sum_limit using 1
  · ext temperature
    exact accepted_count_variance_eq_sum energies cutoff temperature
  · simp
    ring

theorem tendsto_line_variance_low_temperature (energy cutoff : ℝ) :
    Tendsto (fun temperature => lineWeight energy cutoff temperature *
      (1 - lineWeight energy cutoff temperature))
      (𝓝[>] 0) (𝓝 (if energy = cutoff then (1 / 4 : ℝ) else 0)) := by
  classical
  rcases lt_trichotomy energy cutoff with below | equal | above
  · simpa [ne_of_lt below] using
      (tendsto_line_weight_low_temperature_of_lt energy cutoff below).mul
        ((tendsto_line_weight_low_temperature_of_lt energy cutoff below).const_sub 1)
  · subst energy
    simp only [line_weight_at_cutoff, if_true]
    have constant : Tendsto (fun _temperature : ℝ => (1 / 4 : ℝ))
        (𝓝[>] 0) (𝓝 (1 / 4 : ℝ)) := tendsto_const_nhds
    convert constant using 1
    norm_num
  · simpa [ne_of_gt above] using
      (tendsto_line_weight_low_temperature_of_gt energy cutoff above).mul
        ((tendsto_line_weight_low_temperature_of_gt energy cutoff above).const_sub 1)

def cutoffTieCount (energies : Line → ℝ) (cutoff : ℝ) : ℕ :=
  (Finset.univ.filter (fun line => energies line = cutoff)).card

theorem tendsto_accepted_count_variance_low_temperature
    (energies : Line → ℝ) (cutoff : ℝ) :
    Tendsto (fun temperature => acceptedCountVariance energies cutoff temperature)
      (𝓝[>] 0) (𝓝 ((cutoffTieCount energies cutoff : ℝ) / 4)) := by
  classical
  have sum_limit := tendsto_finset_sum Finset.univ (fun line _ =>
    tendsto_line_variance_low_temperature (energies line) cutoff)
  convert sum_limit using 1
  · ext temperature
    exact accepted_count_variance_eq_sum energies cutoff temperature
  · simp [cutoffTieCount, ← Finset.sum_filter, div_eq_mul_inv]

theorem tendsto_accepted_count_variance_low_temperature_no_ties
    (energies : Line → ℝ) (cutoff : ℝ) (no_ties : ∀ line, energies line ≠ cutoff) :
    Tendsto (fun temperature => acceptedCountVariance energies cutoff temperature)
      (𝓝[>] 0) (𝓝 0) := by
  simpa [cutoffTieCount, no_ties] using
    tendsto_accepted_count_variance_low_temperature energies cutoff

end TemperatureLimits

end

end InfoGeometry.Spectrometry.DecoupledThermodynamics
