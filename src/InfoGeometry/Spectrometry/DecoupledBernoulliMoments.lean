import InfoGeometry.Spectrometry.DecoupledThermodynamics
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance

namespace InfoGeometry.Spectrometry.DecoupledThermodynamics

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

local instance : MeasurableSpace (Line → Bool) := ⊤

def jointPMF (energies : Line → ℝ) (cutoff temperature : ℝ) : PMF (Line → Bool) :=
  PMF.ofFintype (fun configuration =>
    ENNReal.ofReal (jointProbability energies cutoff temperature configuration)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun configuration _ =>
        (joint_probability_pos energies cutoff temperature configuration).le)]
      rw [joint_probabilities_sum_one, ENNReal.ofReal_one])

def jointExpectation (energies : Line → ℝ) (cutoff temperature : ℝ)
    (observable : (Line → Bool) → ℝ) : ℝ :=
  ∑ configuration, jointProbability energies cutoff temperature configuration *
    observable configuration

theorem joint_expectation_eq_integral (energies : Line → ℝ) (cutoff temperature : ℝ)
    (observable : (Line → Bool) → ℝ) :
    jointExpectation energies cutoff temperature observable =
      ∫ configuration, observable configuration ∂(jointPMF energies cutoff temperature).toMeasure := by
  rw [PMF.integral_eq_sum]
  simp only [jointExpectation, jointPMF, PMF.ofFintype_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro configuration _
  rw [ENNReal.toReal_ofReal (joint_probability_pos energies cutoff temperature configuration).le]

theorem joint_expectation_product (energies : Line → ℝ) (cutoff temperature : ℝ)
    (observable : Line → Bool → ℝ) :
    jointExpectation energies cutoff temperature
        (fun configuration => ∏ line, observable line (configuration line)) =
      ∏ line, ∑ accepted : Bool,
        stateProbability (energies line) cutoff temperature accepted * observable line accepted := by
  simp only [jointExpectation, jointProbability, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (line : Line) (accepted : Bool) =>
    stateProbability (energies line) cutoff temperature accepted * observable line accepted)).symm

def acceptedIndicator (accepted : Bool) : ℝ := if accepted then 1 else 0

def acceptedCount (configuration : Line → Bool) : ℝ :=
  ∑ line, acceptedIndicator (configuration line)

def centeredAcceptance (energy cutoff temperature : ℝ) (accepted : Bool) : ℝ :=
  acceptedIndicator accepted - lineWeight energy cutoff temperature

theorem centered_acceptance_mean (energy cutoff temperature : ℝ) :
    (∑ accepted : Bool, stateProbability energy cutoff temperature accepted *
      centeredAcceptance energy cutoff temperature accepted) = 0 := by
  simp [stateProbability, centeredAcceptance, acceptedIndicator]
  ring

theorem centered_acceptance_second_moment (energy cutoff temperature : ℝ) :
    (∑ accepted : Bool, stateProbability energy cutoff temperature accepted *
      centeredAcceptance energy cutoff temperature accepted ^ 2) =
      lineWeight energy cutoff temperature * (1 - lineWeight energy cutoff temperature) := by
  simp [stateProbability, centeredAcceptance, acceptedIndicator]
  ring

theorem expected_accepted_count (energies : Line → ℝ) (cutoff temperature : ℝ) :
    jointExpectation energies cutoff temperature acceptedCount =
      activeSupport energies cutoff temperature := by
  exact (active_support_eq_expected_accepted_count energies cutoff temperature).symm

theorem centered_acceptance_pair_moment (energies : Line → ℝ) (cutoff temperature : ℝ)
    (first second : Line) :
    jointExpectation energies cutoff temperature (fun configuration =>
      centeredAcceptance (energies first) cutoff temperature (configuration first) *
      centeredAcceptance (energies second) cutoff temperature (configuration second)) =
      if first = second then
        lineWeight (energies first) cutoff temperature *
          (1 - lineWeight (energies first) cutoff temperature)
      else 0 := by
  classical
  let observable := fun line accepted =>
    (if line = first then centeredAcceptance (energies line) cutoff temperature accepted else 1) *
    (if line = second then centeredAcceptance (energies line) cutoff temperature accepted else 1)
  have product_identity (configuration : Line → Bool) :
      (∏ line, observable line (configuration line)) =
        centeredAcceptance (energies first) cutoff temperature (configuration first) *
        centeredAcceptance (energies second) cutoff temperature (configuration second) := by
    dsimp only [observable]
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [← product_identity]
  rw [joint_expectation_product]
  by_cases equal : first = second
  · subst second
    simp only [if_true]
    have local_moment (line : Line) :
        (∑ accepted : Bool,
          stateProbability (energies line) cutoff temperature accepted * observable line accepted) =
        if line = first then
          lineWeight (energies first) cutoff temperature *
            (1 - lineWeight (energies first) cutoff temperature)
        else 1 := by
      by_cases selected : line = first
      · subst line
        simpa only [observable, if_true, ← sq] using
          centered_acceptance_second_moment (energies first) cutoff temperature
      · simp only [observable, selected, if_false, mul_one]
        exact state_probabilities_sum_one (energies line) cutoff temperature
    simp_rw [local_moment]
    simp
  · rw [if_neg equal]
    apply Finset.prod_eq_zero (Finset.mem_univ first)
    simpa only [observable, if_true, equal, if_false, mul_one] using
      centered_acceptance_mean (energies first) cutoff temperature

def acceptedCountVariance (energies : Line → ℝ) (cutoff temperature : ℝ) : ℝ :=
  ProbabilityTheory.variance acceptedCount (jointPMF energies cutoff temperature).toMeasure

theorem accepted_count_variance_eq_centered_moment
    (energies : Line → ℝ) (cutoff temperature : ℝ) :
    acceptedCountVariance energies cutoff temperature =
      jointExpectation energies cutoff temperature (fun configuration =>
        (acceptedCount configuration - activeSupport energies cutoff temperature) ^ 2) := by
  rw [acceptedCountVariance, ProbabilityTheory.variance_eq_integral
    (measurable_of_finite acceptedCount).aemeasurable]
  rw [← joint_expectation_eq_integral, ← joint_expectation_eq_integral, expected_accepted_count]

theorem accepted_count_variance_eq_sum (energies : Line → ℝ) (cutoff temperature : ℝ) :
    acceptedCountVariance energies cutoff temperature =
      ∑ line, lineWeight (energies line) cutoff temperature *
        (1 - lineWeight (energies line) cutoff temperature) := by
  rw [accepted_count_variance_eq_centered_moment]
  have centered_sum (configuration : Line → Bool) :
      acceptedCount configuration - activeSupport energies cutoff temperature =
        ∑ line, centeredAcceptance (energies line) cutoff temperature (configuration line) := by
    simp [acceptedCount, activeSupport, centeredAcceptance, Finset.sum_sub_distrib]
  simp_rw [centered_sum, sq, Finset.sum_mul, Finset.mul_sum]
  unfold jointExpectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_comm]
  change (∑ second, jointExpectation energies cutoff temperature (fun configuration =>
    centeredAcceptance (energies first) cutoff temperature (configuration first) *
    centeredAcceptance (energies second) cutoff temperature (configuration second))) = _
  simp_rw [centered_acceptance_pair_moment]
  simp

end

end InfoGeometry.Spectrometry.DecoupledThermodynamics
