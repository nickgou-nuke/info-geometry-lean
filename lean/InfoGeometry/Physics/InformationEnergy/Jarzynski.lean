/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
import InfoGeometry.Physics.InformationEnergy.BinaryErasure
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Finite fluctuation moments, conditioning, and erasure work

The finite Jensen and partition arguments in Bérut, Petrosyan, and Ciliberto,
arXiv:1503.06537v1, Section 4, equations (23)--(27) and (29).

All averages here are finite weighted sums or Mathlib's `Finset.centerMass`.
The work fluctuation identities are explicit hypotheses; these theorems do not
derive a dynamical Jarzynski equality. The entropy-production specialization
instead consumes the existing finite forward/reverse ensemble owner and its
proved integral fluctuation theorem.

For the erasure application, the success probability is measured when the
drag force stops, before subsequent barrier restoration. The two equilibrium
basin weights `1 / 2` are hypotheses specific to the symmetric cyclic setting.
Both conditioning events have strictly positive probability. Perfect-success
limits, stochastic work integrals, and identification of work with heat are
outside these finite statements.
-/

noncomputable section

namespace InfoGeometry.Physics.InformationEnergy.Jarzynski

open Finset
open InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus.DirectedThermoGraph

variable {ι : Type*}

/-- Jensen's inequality turns an upper bound on a finite exponential moment
into a lower bound on the associated mean work. The weights need not sum to
one because `centerMass` performs the normalization. -/
theorem neg_log_expMoment_le_centerMass
    (s : Finset ι) (w W : ι → ℝ) {β A : ℝ}
    (hβ : 0 < β) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmass : 0 < ∑ i ∈ s, w i) (hA : 0 < A)
    (hmoment : s.centerMass w (fun i => Real.exp (-β * W i)) ≤ A) :
    -Real.log A / β ≤ s.centerMass w W := by
  have hJ := convexOn_exp.map_centerMass_le
    (t := s) (w := w) (p := fun i => -β * W i)
    hw hmass (fun _ _ => Set.mem_univ _)
  have hscale : s.centerMass w (fun i => -β * W i) =
      -β * s.centerMass w W := by
    simpa only [smul_eq_mul] using
      (Finset.centerMass_smul (c := -β) (t := s) (w := w) (z := W))
  rw [hscale] at hJ
  change Real.exp (-β * s.centerMass w W) ≤
    s.centerMass w (fun i => Real.exp (-β * W i)) at hJ
  have hlog : -β * s.centerMass w W ≤ Real.log A :=
    (Real.le_log_iff_exp_le hA).2 (hJ.trans hmoment)
  apply (div_le_iff₀ hβ).2
  nlinarith

/-- The mean-work consequence of a finite Jarzynski identity. The equality
for the exponential moment is assumed, not supplied by a definition of that
moment or by a pre-existing lower bound on work. -/
theorem mean_work_ge_of_jarzynski
    (s : Finset ι) (w W : ι → ℝ) {β ΔF : ℝ}
    (hβ : 0 < β) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hnorm : ∑ i ∈ s, w i = 1)
    (hJarzynski : (∑ i ∈ s, w i * Real.exp (-β * W i)) =
      Real.exp (-β * ΔF)) :
    ΔF ≤ ∑ i ∈ s, w i * W i := by
  have hmass : 0 < ∑ i ∈ s, w i := by rw [hnorm]; norm_num
  have hmoment : s.centerMass w (fun i => Real.exp (-β * W i)) =
      Real.exp (-β * ΔF) := by
    simpa only [Finset.centerMass, hnorm, inv_one, one_smul, smul_eq_mul, one_mul]
      using hJarzynski
  have h := neg_log_expMoment_le_centerMass s w W hβ hw hmass
    (Real.exp_pos (-β * ΔF)) hmoment.le
  rw [Real.log_exp] at h
  have hcancel : -(-β * ΔF) / β = ΔF := by
    field_simp [hβ.ne']
  rw [hcancel] at h
  simpa only [Finset.centerMass, hnorm, inv_one, one_smul, smul_eq_mul, one_mul]
    using h

/-- The existing finite forward/reverse fluctuation law has nonnegative
forward mean entropy production. This uses its proved fluctuation identity
and derives the mean inequality by Jensen. -/
theorem expectation_entropyProduction_nonneg
    {PathSample : Type} [Fintype PathSample]
    (L : IntegralFluctuationLaw PathSample) :
    0 ≤ L.expectation L.entropyProduction := by
  classical
  have hmoment :
      (∑ ω, L.forwardProbability ω * Real.exp (-(1 : ℝ) * L.entropyProduction ω)) =
        Real.exp (-(1 : ℝ) * (0 : ℝ)) := by
    simpa only [neg_one_mul, mul_zero, Real.exp_zero,
      IntegralFluctuationLaw.expectation] using integral_fluctuation_theorem L
  exact mean_work_ge_of_jarzynski Finset.univ L.forwardProbability
    L.entropyProduction (β := 1) (ΔF := 0) (by norm_num)
    (fun ω _ => (L.forward_positive ω).le) L.forward_normalized hmoment

/-- Reconstruction of any weighted observable from an event and its
complement. This is the finite algebra behind the law of total expectation;
the two conditional averages are derived from the actual partition. -/
theorem sum_eq_conditioned_mixture
    (s : Finset ι) (P : ι → Prop) [DecidablePred P] (w f : ι → ℝ) {p : ℝ}
    (hnorm : ∑ i ∈ s, w i = 1)
    (hP : ∑ i ∈ s.filter P, w i = p)
    (hp : p ≠ 0) (hpc : 1 - p ≠ 0) :
    (∑ i ∈ s, w i * f i) =
      p * (s.filter P).centerMass w f +
        (1 - p) * (s.filter (fun i => ¬P i)).centerMass w f := by
  have hnot : (∑ i ∈ s.filter (fun i => ¬P i), w i) = 1 - p := by
    have htotal := Finset.sum_filter_add_sum_filter_not s P w
    rw [hnorm, hP] at htotal
    linarith
  have hsuccess : p * (s.filter P).centerMass w f =
      ∑ i ∈ s.filter P, w i * f i := by
    simp only [Finset.centerMass, smul_eq_mul, hP]
    rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  have hfailure : (1 - p) * (s.filter (fun i => ¬P i)).centerMass w f =
      ∑ i ∈ s.filter (fun i => ¬P i), w i * f i := by
    simp only [Finset.centerMass, smul_eq_mul, hnot]
    rw [← mul_assoc, mul_inv_cancel₀ hpc, one_mul]
  rw [hsuccess, hfailure]
  exact (Finset.sum_filter_add_sum_filter_not s P (fun i => w i * f i)).symm

/-- An event of positive mass `p` and reference mass `1 / 2`
obeys the success-conditioned work bound of equation (25), provided its
conditional exponential moment is the specified ratio. -/
theorem conditioned_mean_work_lower_bound
    (s : Finset ι) (w W : ι → ℝ) {β p : ℝ}
    (hβ : 0 < β) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmass : ∑ i ∈ s, w i = p) (hp : 0 < p)
    (hmoment : s.centerMass w (fun i => Real.exp (-β * W i)) = (1 / 2) / p) :
    (Real.log 2 + Real.log p) / β ≤ s.centerMass w W := by
  have hmass_pos : 0 < ∑ i ∈ s, w i := by rw [hmass]; exact hp
  have hA : 0 < (1 / 2 : ℝ) / p := div_pos (by norm_num) hp
  have h := neg_log_expMoment_le_centerMass s w W hβ hw hmass_pos hA hmoment.le
  have hlog : -Real.log ((1 / 2 : ℝ) / p) = Real.log 2 + Real.log p := by
    rw [Real.log_div (by norm_num : (1 / 2 : ℝ) ≠ 0) hp.ne',
      Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
    ring
  simpa only [hlog] using h

/-- The success/failure identities imply both the full exponential moment
and the binary-entropy work bound. In particular, the full moment is `1`,
while the success-conditioned moment is `(1 / 2) / p`.

Here `p` is the actual mass of the success event. Both events must have
positive mass, and the two conditional identities remain named hypotheses. -/
theorem partition_moments_imply_work_bound
    (s : Finset ι) (P : ι → Prop) [DecidablePred P] (w W : ι → ℝ) {β p : ℝ}
    (hβ : 0 < β) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hnorm : ∑ i ∈ s, w i = 1)
    (hP : ∑ i ∈ s.filter P, w i = p) (hp : 0 < p) (hp_one : p < 1)
    (hsuccess : (s.filter P).centerMass w (fun i => Real.exp (-β * W i)) =
      (1 / 2) / p)
    (hfailure : (s.filter (fun i => ¬P i)).centerMass w
      (fun i => Real.exp (-β * W i)) = (1 / 2) / (1 - p)) :
    ((∑ i ∈ s, w i * Real.exp (-β * W i)) = 1) ∧
      ((Real.log 2 - Real.binEntropy p) / β ≤ ∑ i ∈ s, w i * W i) := by
  have hpc : 0 < 1 - p := sub_pos.mpr hp_one
  have hnot : (∑ i ∈ s.filter (fun i => ¬P i), w i) = 1 - p := by
    have htotal := Finset.sum_filter_add_sum_filter_not s P w
    rw [hnorm, hP] at htotal
    linarith
  have hsuccess_bound := conditioned_mean_work_lower_bound (s.filter P) w W hβ
    (fun i hi => hw i (Finset.mem_filter.mp hi).1) hP hp hsuccess
  have hfailure_bound := conditioned_mean_work_lower_bound
    (s.filter (fun i => ¬P i)) w W hβ
    (fun i hi => hw i (Finset.mem_filter.mp hi).1) hnot hpc hfailure
  have hmix_work := sum_eq_conditioned_mixture s P w W hnorm hP hp.ne' hpc.ne'
  have hmix_exp := sum_eq_conditioned_mixture s P w
    (fun i => Real.exp (-β * W i)) hnorm hP hp.ne' hpc.ne'
  constructor
  · rw [hmix_exp, hsuccess, hfailure]
    field_simp [hp.ne', hpc.ne']
    ring
  · calc
      (Real.log 2 - Real.binEntropy p) / β =
          p * ((Real.log 2 + Real.log p) / β) +
            (1 - p) * ((Real.log 2 + Real.log (1 - p)) / β) := by
              simp only [Real.binEntropy, Real.log_inv]
              ring
      _ ≤ p * (s.filter P).centerMass w W +
          (1 - p) * (s.filter (fun i => ¬P i)).centerMass w W :=
            add_le_add (mul_le_mul_of_nonneg_left hsuccess_bound hp.le)
              (mul_le_mul_of_nonneg_left hfailure_bound hpc.le)
      _ = ∑ i ∈ s, w i * W i := hmix_work.symm

/-- Conversion from inverse temperature to the existing binary erasure-cost
owner. The relation `β⁻¹ = kB * T` is explicit, as are the conditional
fluctuation identities used to obtain the work bound. -/
theorem mean_work_ge_erasureCost_of_conditional_moments
    (s : Finset ι) (P : ι → Prop) [DecidablePred P] (w W : ι → ℝ)
    {β p kB T : ℝ}
    (hβ : 0 < β) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hnorm : ∑ i ∈ s, w i = 1)
    (hP : ∑ i ∈ s.filter P, w i = p) (hp : 0 < p) (hp_one : p < 1)
    (hthermal : β⁻¹ = kB * T)
    (hsuccess : (s.filter P).centerMass w (fun i => Real.exp (-β * W i)) =
      (1 / 2) / p)
    (hfailure : (s.filter (fun i => ¬P i)).centerMass w
      (fun i => Real.exp (-β * W i)) = (1 / 2) / (1 - p)) :
    BinaryErasure.erasureCost kB T p ≤ ∑ i ∈ s, w i * W i := by
  have hbound := (partition_moments_imply_work_bound s P w W hβ hw hnorm hP
    hp hp_one hsuccess hfailure).2
  calc
    BinaryErasure.erasureCost kB T p = (Real.log 2 - Real.binEntropy p) / β := by
      rw [BinaryErasure.erasureCost, div_eq_mul_inv, hthermal]
      ring
    _ ≤ ∑ i ∈ s, w i * W i := hbound

end InfoGeometry.Physics.InformationEnergy.Jarzynski
