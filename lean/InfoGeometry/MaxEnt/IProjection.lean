import InfoGeometry.MaxEnt.Finite
import InfoGeometry.Measure.DiscreteRN
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option autoImplicit false

namespace InfoGeometry.MaxEnt.IProjection

open scoped BigOperators ENNReal
open InfoGeometry InfoGeometry.MaxEnt.Finite MeasureTheory

noncomputable section

variable {α ι : Type*}
variable [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable [DecidableEq ι]

/--
Every real-valued function on a finite type is integrable against a finite measure.
-/
lemma integrable_of_fintype (f : α → ℝ) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable f μ := by
  classical
  let C : ℝ := ∑ y : α, ‖f y‖
  have hf_meas : AEStronglyMeasurable f μ :=
    (measurable_of_finite f).aestronglyMeasurable
  refine MeasureTheory.Integrable.of_bound hf_meas C ?_
  filter_upwards with x
  have hx :
      ‖f x‖ ≤ ∑ y : α, ‖f y‖ := by
    simpa using
      (Finset.single_le_sum
        (f := fun y : α => ‖f y‖)
        (s := (Finset.univ : Finset α))
        (a := x)
        (by
          intro y _hy
          exact norm_nonneg (f y))
        (by simp))
  simpa [C] using hx

/-- 
Finite sum formula for KL divergence against a full-support reference PMF. 
Coincides with `InformationTheory.klDiv`.
-/
theorem toReal_klDiv_eq_sum_log_ratio 
    [DecidableEq α]
    (P Q : ProbabilityDist α) 
    (hQ : ∀ x, 0 < (Q x).toReal) :
    (InformationTheory.klDiv P.toMeasure Q.toMeasure).toReal = 
      ∑ x, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) := by
  have h_ac : P.toMeasure ≪ Q.toMeasure := by
    intro s hQs
    have hs : MeasurableSet s := (Set.toFinite s).measurableSet
    have hQs' : Disjoint Q.support s := (Q.toMeasure_apply_eq_zero_iff hs).1 hQs
    refine (P.toMeasure_apply_eq_zero_iff hs).2 ?_
    refine Set.disjoint_left.2 ?_
    intro x hxP hxS
    have hxQ : x ∈ Q.support := by
      refine (Q.mem_support_iff x).2 ?_
      intro h0
      have : 0 < (Q x).toReal := hQ x
      simp [h0] at this
    exact (Set.disjoint_left.1 hQs' hxQ) hxS
  have h_mass : P.toMeasure Set.univ = Q.toMeasure Set.univ := by
    simp
  rw [InformationTheory.toReal_klDiv_of_measure_eq h_ac h_mass]
  have h_rn := InfoGeometry.Measure.DiscreteRN.rnDeriv_pmf_eq_div P Q h_ac
  have h_int :
      (∫ x, llr P.toMeasure Q.toMeasure x ∂P.toMeasure)
        =
      ∫ x, Real.log (((P x : ℝ≥0∞) / (Q x : ℝ≥0∞)).toReal) ∂P.toMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [h_rn] with x hx
    simp [MeasureTheory.llr_def, hx]
  rw [h_int]
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  congr 1
  rw [ENNReal.toReal_div]

/-- 
Nonnegativity of the finite KL sum against a full-support reference PMF. 
-/
lemma sum_log_ratio_nonneg
    [DecidableEq α]
    (P Q : ProbabilityDist α)
    (hQ : ∀ x, 0 < (Q x).toReal) :
    0 ≤ ∑ x, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) := by
  rw [← toReal_klDiv_eq_sum_log_ratio P Q hQ]
  exact ENNReal.toReal_nonneg

/--
The I-Projection (Information Projection) theorem:
The distribution that minimizes KL divergence to a prior `q` subject to
linear constraints is the unique Gibbs distribution that satisfies those constraints.
-/
theorem gibbs_is_minimizer
    [DecidableEq α]
    (J : FiniteJaynesProblem α ι)
    (hprior : J.FullSupportPrior)
    [Nonempty α] (lam : ι → ℝ) (hZ : J.partition lam ≠ 0)
    (h_match : J.SatisfiesTargetMoments lam hZ)
    (P : ProbabilityDist α)
    (h_feasible : ∀ i ∈ J.index, J.moment P (J.feature i) = J.target i) :
    ∑ x, ((J.gibbsDist lam hZ) x).toReal *
      Real.log (((J.gibbsDist lam hZ) x).toReal / (J.prior x).toReal)
      ≤
    ∑ x, (P x).toReal * Real.log ((P x).toReal / (J.prior x).toReal) := by
  have hP := J.kl_prior_eq_kl_gibbs_add_dualObjective hprior lam hZ P h_feasible
  have hG := J.kl_prior_eq_kl_gibbs_add_dualObjective hprior lam hZ (J.gibbsDist lam hZ)
      (by simp [FiniteJaynesProblem.SatisfiesTargetMoments] at h_match; exact h_match)
  have h_full_gibbs : ∀ x, 0 < ((J.gibbsDist lam hZ) x).toReal := by
    intro x
    rw [J.gibbsDist_pointwise]
    unfold FiniteJaynesProblem.gibbsProb FiniteJaynesProblem.gibbsWeight
    exact div_pos (mul_pos (hprior x) (Real.exp_pos _))
      (lt_of_le_of_ne (J.partition_nonneg lam) (Ne.symm hZ))
  have h_nonneg :
      0 ≤ ∑ x, (P x).toReal * Real.log ((P x).toReal / (J.gibbsDist lam hZ x).toReal) := by
    apply sum_log_ratio_nonneg P (J.gibbsDist lam hZ) h_full_gibbs
  simp_rw [J.gibbsDist_pointwise] at hP hG h_nonneg ⊢
  have h_gibbs_pos : ∀ x, J.gibbsProb lam hZ x ≠ 0 := by
    intro x
    rw [J.gibbsProb_eq_prior_mul_exp_tilt lam hZ x]
    exact (mul_pos (hprior x) (Real.exp_pos _)).ne'
  have h_self : (∑ x, J.gibbsProb lam hZ x * Real.log (J.gibbsProb lam hZ x / J.gibbsProb lam hZ x)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    simp [h_gibbs_pos x]
  rw [h_self, zero_sub] at hG
  rw [hP, hG]
  linarith

/-- 
Uniqueness of the I-Projection.
-/
theorem gibbs_is_unique_minimizer
    [DecidableEq α]
    (J : FiniteJaynesProblem α ι)
    (hprior : J.FullSupportPrior)
    [Nonempty α] (lam : ι → ℝ) (hZ : J.partition lam ≠ 0)
    (h_match : J.SatisfiesTargetMoments lam hZ)
    (P : ProbabilityDist α)
    (h_feasible : ∀ i ∈ J.index, J.moment P (J.feature i) = J.target i)
    (hEq :
      ∑ x, (P x).toReal * Real.log ((P x).toReal / (J.prior x).toReal)
        =
      ∑ x, ((J.gibbsDist lam hZ) x).toReal *
        Real.log (((J.gibbsDist lam hZ) x).toReal / (J.prior x).toReal)) :
    P = J.gibbsDist lam hZ := by
  have hP := J.kl_prior_eq_kl_gibbs_add_dualObjective hprior lam hZ P h_feasible
  have hG := J.kl_prior_eq_kl_gibbs_add_dualObjective hprior lam hZ (J.gibbsDist lam hZ)
      (by simp [FiniteJaynesProblem.SatisfiesTargetMoments] at h_match; exact h_match)
  simp_rw [J.gibbsDist_pointwise] at hEq hP hG ⊢
  have h_gibbs_pos : ∀ x, J.gibbsProb lam hZ x ≠ 0 := by
    intro x
    rw [J.gibbsProb_eq_prior_mul_exp_tilt lam hZ x]
    exact (mul_pos (hprior x) (Real.exp_pos _)).ne'
  have h_self : (∑ x, J.gibbsProb lam hZ x * Real.log (J.gibbsProb lam hZ x / J.gibbsProb lam hZ x)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    simp [h_gibbs_pos x]
  rw [h_self, zero_sub] at hG
  have h_prior_eq_dual :
      ∑ x, (P x).toReal * Real.log ((P x).toReal / (J.prior x).toReal)
        = - J.dualObjective lam := by
    rw [hEq, hG]
  have h_kl_zero : ∑ x, (P x).toReal * Real.log ((P x).toReal / J.gibbsProb lam hZ x) = 0 := by 
    linarith [hEq, hP, hG]
  -- Convert to InformationTheory.klDiv
  have h_full_gibbs : ∀ x, 0 < ((J.gibbsDist lam hZ) x).toReal := by
    intro x
    rw [J.gibbsDist_pointwise]
    unfold FiniteJaynesProblem.gibbsProb FiniteJaynesProblem.gibbsWeight
    exact div_pos (mul_pos (hprior x) (Real.exp_pos _))
      (lt_of_le_of_ne (J.partition_nonneg lam) (Ne.symm hZ))
  have h_kl_mt : (InformationTheory.klDiv P.toMeasure (J.gibbsDist lam hZ).toMeasure).toReal = 0 := by
    rw [toReal_klDiv_eq_sum_log_ratio P (J.gibbsDist lam hZ) h_full_gibbs]
    simp_rw [J.gibbsDist_pointwise]
    exact h_kl_zero
  
  have h_ac_gibbs : P.toMeasure ≪ (J.gibbsDist lam hZ).toMeasure := by
    intro s hGs
    have hs : MeasurableSet s := (Set.toFinite s).measurableSet
    have hGs' : Disjoint (J.gibbsDist lam hZ).support s :=
      ((J.gibbsDist lam hZ).toMeasure_apply_eq_zero_iff hs).1 hGs
    refine (P.toMeasure_apply_eq_zero_iff hs).2 ?_
    refine Set.disjoint_left.2 ?_
    intro x hxP hxS
    have hxG : x ∈ (J.gibbsDist lam hZ).support := by
      refine ((J.gibbsDist lam hZ).mem_support_iff x).2 ?_
      intro h0
      have : 0 < ((J.gibbsDist lam hZ) x).toReal := h_full_gibbs x
      simp [h0] at this
    exact (Set.disjoint_left.1 hGs' hxG) hxS
  
  have h_int_gibbs : Integrable (llr P.toMeasure (J.gibbsDist lam hZ).toMeasure) P.toMeasure :=
    integrable_of_fintype _ _

  have h_kl_enn : InformationTheory.klDiv P.toMeasure (J.gibbsDist lam hZ).toMeasure = 0 := by
    have h_ne_top : InformationTheory.klDiv P.toMeasure (J.gibbsDist lam hZ).toMeasure ≠ ⊤ := by
      rw [InformationTheory.klDiv_ne_top_iff]
      exact ⟨h_ac_gibbs, h_int_gibbs⟩
    apply (ENNReal.toReal_eq_toReal_iff' h_ne_top ENNReal.zero_ne_top).mp
    simp [h_kl_mt]

  have h_meas_eq : P.toMeasure = (J.gibbsDist lam hZ).toMeasure := by
    exact (InformationTheory.klDiv_eq_zero_iff).1 h_kl_enn

  exact PMF.toMeasure_inj.mp h_meas_eq

end

end InfoGeometry.MaxEnt.IProjection
