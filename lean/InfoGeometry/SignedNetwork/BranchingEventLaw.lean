import InfoGeometry.SignedNetwork.BranchingEnsembleGenerator
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Exponential

/-!
# Native probability laws for the next branching event and its waiting time

The marked-event law is a `PMF`, including a `none` outcome at zero total rate.
The expectation theorem is an actual Bochner integral against `PMF.toMeasure`.
On active states the waiting time has Mathlib's `expMeasure` law, and the
waiting time and mark have their product probability measure.

`none` denotes absorption, not a zero-duration jump. Finite event-indexed
iterates are provided. No infinite clock limit, nonexplosion, or continuous-
time first-moment theorem is postulated by these definitions.
-/

noncomputable section

namespace InfoGeometry.SignedNetwork.BranchingEventLaw

open MeasureTheory ProbabilityTheory
open InfoGeometry.SignedNetwork.ExactCancellation
open InfoGeometry.SignedNetwork.BranchingEnsembleGenerator

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- An optional mark makes zero total rate an explicit absorbing outcome. -/
def eventProbability (L : Matrix C C ℝ) (p : Counts C) : Option (Event C) → ℝ
  | none => if totalRate L p = 0 then 1 else 0
  | some e => if totalRate L p = 0 then 0 else eventRate L p e / totalRate L p

theorem eventProbability_nonneg (L : Matrix C C ℝ) (p : Counts C)
    (e : Option (Event C)) : 0 ≤ eventProbability L p e := by
  cases e with
  | none => simp only [eventProbability]; split_ifs <;> norm_num
  | some e =>
      simp only [eventProbability]
      split_ifs
      · exact le_rfl
      · exact div_nonneg (eventRate_nonneg L p e) (totalRate_nonneg L p)

/-- Normalization is proved from the actual event intensities. -/
theorem sum_eventProbability (L : Matrix C C ℝ) (p : Counts C) :
    (∑ e, eventProbability L p e) = 1 := by
  classical
  by_cases hq : totalRate L p = 0
  · simp [Fintype.sum_option, eventProbability, hq]
  · simp only [Fintype.sum_option, eventProbability, hq, if_false, zero_add, add_zero]
    rw [← Finset.sum_div]
    exact div_self hq

/-- The actual probability mass function, rather than a normalization predicate. -/
def eventPMF (L : Matrix C C ℝ) (p : Counts C) : PMF (Option (Event C)) :=
  PMF.ofFintype (fun e => ENNReal.ofReal (eventProbability L p e)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun e _ => eventProbability_nonneg L p e), sum_eventProbability]
    simp)

@[simp] theorem eventPMF_toReal (L : Matrix C C ℝ) (p : Counts C)
    (e : Option (Event C)) :
    (eventPMF L p e).toReal = eventProbability L p e := by
  exact ENNReal.toReal_ofReal (eventProbability_nonneg L p e)

/-- On an active state the absorbing mark has probability zero. -/
theorem eventPMF_none_of_active (L : Matrix C C ℝ) (p : Counts C)
    (hq : totalRate L p ≠ 0) : eventPMF L p none = 0 := by
  simp [eventPMF, eventProbability, hq]

/-- At zero rate the mark law is concentrated at absorption. -/
theorem eventPMF_of_absorbing (L : Matrix C C ℝ) (p : Counts C)
    (hq : totalRate L p = 0) : eventPMF L p = PMF.pure none := by
  ext e
  cases e <;> simp [eventPMF, eventProbability, hq]

/-- Absorption preserves the state and terminates the physical jump recursion. -/
def applyOptional (p : Counts C) : Option (Event C) → Counts C
  | none => p
  | some e => applyEvent p e

/-- Optional deterministic pruning after the sampled event. -/
def pruneState (prune : Bool) (p : Counts C) : Counts C :=
  if prune then cancel p else p

@[simp] theorem signedReal_pruneState (prune : Bool) (p : Counts C) (x : C) :
    signedReal (pruneState prune p) x = signedReal p x := by
  cases prune <;> simp [pruneState]

/-- Next count-state law, obtained by an actual pushforward of the mark PMF. -/
def nextStatePMF (prune : Bool) (L : Matrix C C ℝ) (p : Counts C) : PMF (Counts C) :=
  (eventPMF L p).map (fun e => pruneState prune (applyOptional p e))

/-- Pruning at this event is exactly a pushforward by the canonical cancellation map. -/
theorem nextStatePMF_pruned (L : Matrix C C ℝ) (p : Counts C) :
    nextStatePMF true L p = (nextStatePMF false L p).map cancel := by
  change (eventPMF L p).map (fun e => cancel (applyOptional p e)) =
    ((eventPMF L p).map (applyOptional p)).map cancel
  rw [PMF.map_comp]
  rfl

/-- Finite event-indexed laws. These are not fixed-physical-time laws: each
step still needs its state-dependent exponential holding time. -/
def eventIterates (prune : Bool) (L : Matrix C C ℝ) (p : Counts C) :
    ℕ → PMF (Counts C)
  | 0 => PMF.pure p
  | k + 1 => (eventIterates prune L p k).bind (nextStatePMF prune L)

@[simp] theorem eventIterates_zero (prune : Bool) (L : Matrix C C ℝ) (p : Counts C) :
    eventIterates prune L p 0 = PMF.pure p := rfl

/-- Algebraic identity needed to center the next-event expectation. -/
theorem generator_eq_uncentered (L : Matrix C C ℝ) (F : Counts C → ℝ)
    (p : Counts C) :
    generator L F p = (∑ e, eventRate L p e * F (applyEvent p e)) -
      totalRate L p * F p := by
  simp only [generator, totalRate, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

section Measures

variable [MeasurableSpace C] [MeasurableSingletonClass C]

/-- Genuine expectation under the finite marked-event measure, including the
absorbing case. The inverse total rate is a holding-time factor, not physical time. -/
theorem integral_next_event (L : Matrix C C ℝ) (p : Counts C)
    (F : Counts C → ℝ) :
    (∫ e, F (applyOptional p e) ∂(eventPMF L p).toMeasure) =
      F p + generator L F p / totalRate L p := by
  rw [PMF.integral_eq_sum]
  simp only [eventPMF_toReal, smul_eq_mul]
  by_cases hq : totalRate L p = 0
  · simp [Fintype.sum_option, eventProbability, hq, applyOptional]
  · simp only [Fintype.sum_option, eventProbability, hq, if_false, zero_mul,
      zero_add, add_zero, applyOptional]
    calc
      (∑ e, eventRate L p e / totalRate L p * F (applyEvent p e)) =
          (∑ e, eventRate L p e * F (applyEvent p e)) / totalRate L p := by
        simp only [div_mul_eq_mul_div, Finset.sum_div]
      _ = F p + generator L F p / totalRate L p := by
        rw [generator_eq_uncentered]
        field_simp [hq]
        ring

/-- Exact conditional first moment of the next marked birth. -/
theorem integral_next_signedReal (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) (x : C) :
    (∫ e, signedReal (applyOptional p e) x ∂(eventPMF L p).toMeasure) =
      signedReal p x + linearDrift L p x / totalRate L p := by
  rw [integral_next_event, generator_signedReal L hL]

/-- The same actual expectation after optional exact cancellation. -/
theorem integral_next_signedReal_pruned (prune : Bool) (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) (x : C) :
    (∫ e, signedReal (pruneState prune (applyOptional p e)) x
      ∂(eventPMF L p).toMeasure) =
      signedReal p x + linearDrift L p x / totalRate L p := by
  simp only [signedReal_pruneState]
  exact integral_next_signedReal L hL p x

/-- On an active state, this is the joint law of the holding time and event
mark. At zero rate the process is absorbed instead of drawing a holding time. -/
def activeJumpLaw (L : Matrix C C ℝ) (p : Counts C) :
    Measure (ℝ × Option (Event C)) :=
  (expMeasure (totalRate L p)).prod (eventPMF L p).toMeasure

/-- The active joint law is a native probability measure. -/
theorem activeJumpLaw_probability (L : Matrix C C ℝ) (p : Counts C)
    (hq : 0 < totalRate L p) : IsProbabilityMeasure (activeJumpLaw L p) := by
  letI : IsProbabilityMeasure (expMeasure (totalRate L p)) :=
    isProbabilityMeasure_expMeasure hq
  unfold activeJumpLaw
  infer_instance

/-- Exact exponential waiting-time CDF, not a one-birth-per-time-step update. -/
theorem holdingTime_cdf (L : Matrix C C ℝ) (p : Counts C)
    (hq : 0 < totalRate L p) (t : ℝ) (ht : 0 ≤ t) :
    cdf (expMeasure (totalRate L p)) t =
      1 - Real.exp (-(totalRate L p * t)) := by
  rw [cdf_expMeasure_eq hq, if_pos ht]

end Measures

end InfoGeometry.SignedNetwork.BranchingEventLaw
