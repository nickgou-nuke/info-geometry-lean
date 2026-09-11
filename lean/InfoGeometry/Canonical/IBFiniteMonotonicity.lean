import InfoGeometry.Canonical.IBMonotonicity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.IBFinitePythagorean
import InfoGeometry.Measure.Normalized
import InfoGeometry.MaxEnt.IProjection

open MeasureTheory
open scoped BigOperators ENNReal

namespace InfoGeometry.Canonical.IBFiniteMonotonicity

open InfoGeometry.Canonical.IBFunctional
open InfoGeometry.Canonical.IBPythagorean
open InfoGeometry.Canonical.IBMonotonicity
open InfoGeometry.Canonical.IBFinitePythagorean
open InfoGeometry.MeasureProjective.Normalized
open InfoGeometry.MaxEnt
open InfoGeometry.MaxEnt.Finite

set_option linter.unusedSectionVars false

variable {X T : Type*}
variable [Fintype X] [Fintype T]
variable [DecidableEq X] [DecidableEq T]
variable [MeasurableSpace X] [MeasurableSpace T]
variable [MeasurableSingletonClass X] [MeasurableSingletonClass T]
variable [Nonempty T]

/-- A complete finite Blahut-Arimoto descent witness at one marginal step. -/
def IBDescentWitness
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (hKL_encoder : FiniteKLFamily (q_n : Measure T) (IBNextEncoder q_n β D hInt))
    (p_old : X → ProbabilityMeasure T) : Prop :=
  ∃ hKL_old : FiniteKLFamily (q_n : Measure T) p_old,
    ∃ hKL_next :
      FiniteKLFamily
        ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
        (IBNextEncoder q_n β D hInt),
      IBGlobalFreeEnergy pX q_n β D (IBNextEncoder q_n β D hInt) hKL_encoder
          ≤ IBGlobalFreeEnergy pX q_n β D p_old hKL_old ∧
        IBMarginalDescentWitness
          pX q_n (IBNextMarginal pX q_n β D hInt h_meas) β D
          (IBNextEncoder q_n β D hInt) hKL_encoder hKL_next

/-- Single-slice finite Jaynes problem induced by the current target marginal `q_n`. -/
noncomputable def finiteSliceJaynes
    (q_n : ProbabilityMeasure T)
    (D : X → T → ℝ)
    (x : X) : FiniteJaynesProblem T Unit :=
  FiniteJaynesProblem.ofLogLikelihood
    (probMeasureToPMF q_n)
    (InfoGeometry.Canonical.IBMeasure.distortionRV D x)

lemma finiteSliceJaynes_fullSupportPrior
    (q_n : ProbabilityMeasure T)
    (D : X → T → ℝ)
    (x : X)
    (hq : ∀ t : T, 0 < ((probMeasureToPMF q_n) t).toReal) :
    (finiteSliceJaynes q_n D x).FullSupportPrior := by
  intro t
  simpa [finiteSliceJaynes] using hq t

lemma finiteSliceJaynes_partition_eq_integral_exp
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (x : X) :
    (finiteSliceJaynes q_n D x).partition (fun _ => β)
      = ∫ t, Real.exp (-β * D x t) ∂(q_n : Measure T) := by
  unfold finiteSliceJaynes FiniteJaynesProblem.ofLogLikelihood FiniteJaynesProblem.partition
  rw [integral_eq_sum_probMeasure
    (P := q_n)
    (f := fun t => Real.exp (-β * D x t))]
  refine Finset.sum_congr rfl ?_
  intro t ht
  simp [FiniteJaynesProblem.energy, InfoGeometry.Canonical.IBMeasure.distortionRV]

lemma finiteSliceJaynes_partition_ne_zero
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (x : X) :
    (finiteSliceJaynes q_n D x).partition (fun _ => β) ≠ 0 := by
  rw [finiteSliceJaynes_partition_eq_integral_exp (q_n := q_n) (β := β) (D := D) (x := x)]
  exact (integral_exp_neg_distortion_pos q_n β D x).ne'

lemma probMeasureToPMF_IBNextEncoder_eq_finiteSliceGibbs
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (x : X) :
    probMeasureToPMF (IBNextEncoder q_n β D hInt x)
      =
    let J := finiteSliceJaynes q_n D x
    let hZ := finiteSliceJaynes_partition_ne_zero q_n β D x
    J.gibbsDist (fun _ => β) hZ := by
  classical
  let J := finiteSliceJaynes q_n D x
  let hZ := finiteSliceJaynes_partition_ne_zero q_n β D x
  ext t
  apply (ENNReal.toReal_eq_toReal_iff'
    ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)).apply_ne_top t)
    ((J.gibbsDist (fun _ => β) hZ).apply_ne_top t)).1
  rw [probMeasureToPMF_apply]
  change
    (((InfoGeometry.Canonical.IBMeasure.IBGibbsMeasure (qT := (q_n : Measure T)) β D x) {t}).toReal)
      =
    (((J.gibbsDist (fun _ => β) hZ) t).toReal)
  have htilted :
      (((InfoGeometry.Canonical.IBMeasure.IBGibbsMeasure (qT := (q_n : Measure T)) β D x) {t}).toReal)
        =
      (ENNReal.ofReal
        (∫ a in ({t} : Set T),
            Real.exp (-β * D x a) / ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T)
          ∂(q_n : Measure T))).toReal := by
    simpa [InfoGeometry.Canonical.IBMeasure.IBGibbsMeasure,
      InfoGeometry.Canonical.IBMeasure.distortionRV] using
      congrArg ENNReal.toReal
        (MeasureTheory.tilted_apply_eq_ofReal_integral'
          (μ := (q_n : Measure T))
          (f := fun a => -β * D x a)
          (s := ({t} : Set T))
          (hs := measurableSet_singleton t))
  rw [htilted]
  have h_nonneg :
      0 ≤
        ∫ a in ({t} : Set T),
            Real.exp (-β * D x a) / ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T)
          ∂(q_n : Measure T) := by
    refine integral_nonneg ?_
    intro a
    positivity
  rw [ENNReal.toReal_ofReal h_nonneg]
  have hsingleton :
      ∫ a in ({t} : Set T),
          Real.exp (-β * D x a) /
            ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T)
          ∂(q_n : Measure T)
        =
      ((q_n : Measure T).real {t}) *
        (Real.exp (-β * D x t) /
          ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T)) := by
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_singleton
        (μ := (q_n : Measure T))
        (f := fun a => Real.exp (-β * D x a) / ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T))
        t)
  rw [hsingleton]
  rw [J.gibbsDist_pointwise]
  unfold FiniteJaynesProblem.gibbsProb FiniteJaynesProblem.gibbsWeight
  rw [finiteSliceJaynes_partition_eq_integral_exp (q_n := q_n) (β := β) (D := D) (x := x)]
  have hmass :
      ((q_n : Measure T).real {t}) = ((probMeasureToPMF q_n) t).toReal := by
    simp [probMeasureToPMF_apply, measureReal_def]
  rw [hmass]
  simp [J, finiteSliceJaynes, FiniteJaynesProblem.ofLogLikelihood,
    FiniteJaynesProblem.energy, InfoGeometry.Canonical.IBMeasure.distortionRV]
  ring_nf

lemma IBNextEncoder_positive_of_fullSupport
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (hq : ∀ t : T, 0 < ((probMeasureToPMF q_n) t).toReal) :
    ∀ x : X, ∀ t : T,
      0 < ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal := by
  intro x t
  exact IBNextEncoder_positive_of_ref_positive q_n β D hInt x t (hq t)

private lemma finiteSlice_log_gibbsRatio_eq_energy_sub_logPartition_of_ref_positive
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (x : X)
    (t : T)
    (hq_t : 0 < ((probMeasureToPMF q_n) t).toReal) :
    let J := finiteSliceJaynes q_n D x
    let lam : Unit → ℝ := fun _ => β
    let hZ := finiteSliceJaynes_partition_ne_zero q_n β D x
    Real.log (J.gibbsProb lam hZ t / ((probMeasureToPMF q_n) t).toReal)
      = J.energy lam t - J.logPartition lam := by
  let J := finiteSliceJaynes q_n D x
  let lam : Unit → ℝ := fun _ => β
  let hZ := finiteSliceJaynes_partition_ne_zero q_n β D x
  change
    Real.log (J.gibbsProb lam hZ t / ((probMeasureToPMF q_n) t).toReal)
      = J.energy lam t - J.logPartition lam
  have hqx : ((probMeasureToPMF q_n) t).toReal ≠ 0 := hq_t.ne'
  have hgibbs :
      J.gibbsProb lam hZ t
        =
      ((probMeasureToPMF q_n) t).toReal * Real.exp (J.energy lam t - J.logPartition lam) := by
    simpa [J, finiteSliceJaynes, FiniteJaynesProblem.ofLogLikelihood] using
      J.gibbsProb_eq_prior_mul_exp_tilt lam hZ t
  have hratio :
      J.gibbsProb lam hZ t / ((probMeasureToPMF q_n) t).toReal
        = Real.exp (J.energy lam t - J.logPartition lam) := by
    rw [hgibbs]
    field_simp [hqx]
  rw [hratio, Real.log_exp]

private lemma finiteSlice_kl_gibbs_variational_identity_of_supportFaithful
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (x : X)
    (p : ProbabilityMeasure T)
    (hpq :
      PMFSupportFaithful
        (probMeasureToPMF p)
        (probMeasureToPMF q_n)) :
    let J := finiteSliceJaynes q_n D x
    let lam : Unit → ℝ := fun _ => β
    let hZ := finiteSliceJaynes_partition_ne_zero q_n β D x
    (∑ t : T,
      ((probMeasureToPMF p) t).toReal *
        Real.log (((probMeasureToPMF p) t).toReal / J.gibbsProb lam hZ t))
      =
    (∑ t : T,
      ((probMeasureToPMF p) t).toReal *
        Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal))
      - (∑ i ∈ J.index, lam i * J.moment (probMeasureToPMF p) (J.feature i))
      + J.logPartition lam := by
  let J := finiteSliceJaynes q_n D x
  let lam : Unit → ℝ := fun _ => β
  let hZ := finiteSliceJaynes_partition_ne_zero q_n β D x
  have hpoint :
      ∀ t : T,
        ((probMeasureToPMF p) t).toReal *
          Real.log (((probMeasureToPMF p) t).toReal / J.gibbsProb lam hZ t)
          =
        ((probMeasureToPMF p) t).toReal *
          (Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal)
            - (J.energy lam t - J.logPartition lam)) := by
    intro t
    by_cases hPt : ((probMeasureToPMF p) t).toReal = 0
    · rw [hPt]
      simp
    · have hPt_pos : 0 < ((probMeasureToPMF p) t).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hPt)
      have hq_t : 0 < ((probMeasureToPMF q_n) t).toReal := hpq t hPt_pos
      have hgpos : 0 < J.gibbsProb lam hZ t := by
        unfold J lam
        rw [FiniteJaynesProblem.gibbsProb_eq_prior_mul_exp_tilt]
        simpa [finiteSliceJaynes] using mul_pos hq_t (Real.exp_pos _)
      have hmain :
          Real.log (((probMeasureToPMF p) t).toReal / J.gibbsProb lam hZ t)
            =
          Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal)
            - (J.energy lam t - J.logPartition lam) := by
        have hlog :=
          finiteSlice_log_gibbsRatio_eq_energy_sub_logPartition_of_ref_positive
            (q_n := q_n) (β := β) (D := D) (x := x) (t := t) hq_t
        have hlog' :
            Real.log (J.gibbsProb lam hZ t / ((probMeasureToPMF q_n) t).toReal)
              = J.energy lam t - J.logPartition lam := by
          simpa [J, lam, hZ] using hlog
        have hratio_pg :
            ((probMeasureToPMF p) t).toReal / J.gibbsProb lam hZ t
              =
            ((((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal) /
              (J.gibbsProb lam hZ t / ((probMeasureToPMF q_n) t).toReal)) := by
          field_simp [hPt, hq_t.ne', hgpos.ne']
        rw [hratio_pg,
          Real.log_div (div_ne_zero hPt hq_t.ne') (div_ne_zero hgpos.ne' hq_t.ne'),
          hlog']
      rw [hmain]
  calc
    (∑ t : T,
      ((probMeasureToPMF p) t).toReal *
        Real.log (((probMeasureToPMF p) t).toReal / J.gibbsProb lam hZ t))
      =
    ∑ t : T,
      ((probMeasureToPMF p) t).toReal *
        (Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal)
          - (J.energy lam t - J.logPartition lam)) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            exact hpoint t
    _ =
      ∑ t : T,
        (((probMeasureToPMF p) t).toReal *
          Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal)
          - ((probMeasureToPMF p) t).toReal * J.energy lam t
          + ((probMeasureToPMF p) t).toReal * J.logPartition lam) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            ring
    _ =
      (∑ t : T,
        ((probMeasureToPMF p) t).toReal *
          Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal))
        - (∑ t : T, ((probMeasureToPMF p) t).toReal * J.energy lam t)
        + (∑ t : T, ((probMeasureToPMF p) t).toReal * J.logPartition lam) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ =
      (∑ t : T,
        ((probMeasureToPMF p) t).toReal *
          Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal))
        - (∑ i ∈ J.index, lam i * J.moment (probMeasureToPMF p) (J.feature i))
        + (∑ t : T, ((probMeasureToPMF p) t).toReal * J.logPartition lam) := by
            rw [J.sum_prob_mul_energy (probMeasureToPMF p) lam]
    _ =
      (∑ t : T,
        ((probMeasureToPMF p) t).toReal *
          Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal))
        - (∑ i ∈ J.index, lam i * J.moment (probMeasureToPMF p) (J.feature i))
        + J.logPartition lam := by
            have hsum : ∑ t : T, ((probMeasureToPMF p) t).toReal = 1 :=
              InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.sum_toReal_eq_one (probMeasureToPMF p)
            rw [← Finset.sum_mul, hsum, one_mul]

/-- Single-slice finite objective at fixed reference `q_n`. -/
noncomputable def finiteSliceObjective
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (x : X)
    (p : ProbabilityMeasure T) : ℝ :=
  β * ∑ t : T, ((probMeasureToPMF p) t).toReal * D x t
    + (InfoGeometry.fin_kl_div (probMeasureToPMF p) (probMeasureToPMF q_n)).toReal

lemma finiteSliceObjective_eq_kl_to_next_minus_logPartition_of_supportFaithful
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (x : X)
    (p : ProbabilityMeasure T)
    (hpq :
      PMFSupportFaithful
        (probMeasureToPMF p)
        (probMeasureToPMF q_n)) :
    finiteSliceObjective q_n β D x p
      =
    (InfoGeometry.fin_kl_div
      (probMeasureToPMF p)
      (probMeasureToPMF (IBNextEncoder q_n β D hInt x))).toReal
      - (finiteSliceJaynes q_n D x).logPartition (fun _ => β) := by
  let J := finiteSliceJaynes q_n D x
  let lam : Unit → ℝ := fun _ => β
  have hZ : J.partition lam ≠ 0 := finiteSliceJaynes_partition_ne_zero q_n β D x
  have hnext_sf :
      PMFSupportFaithful
        (probMeasureToPMF p)
        (probMeasureToPMF (IBNextEncoder q_n β D hInt x)) := by
    intro t hPt
    exact IBNextEncoder_positive_of_ref_positive q_n β D hInt x t (hpq t hPt)
  have hKLq :
      (InfoGeometry.fin_kl_div (probMeasureToPMF p) (probMeasureToPMF q_n)).toReal
        =
      ∑ t : T,
        ((probMeasureToPMF p) t).toReal *
          Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal) := by
    simpa [InfoGeometry.fin_kl_div, InfoGeometry.KL.kl_div] using
      (toReal_fin_klDiv_eq_sum_log_ratio_of_supportFaithful
        (P := probMeasureToPMF p)
        (Q := probMeasureToPMF q_n)
        (hQ := hpq))
  have hKLnext :
      (InfoGeometry.fin_kl_div
          (probMeasureToPMF p)
          (probMeasureToPMF (IBNextEncoder q_n β D hInt x))).toReal
        =
      ∑ t : T,
        ((probMeasureToPMF p) t).toReal *
          Real.log
            (((probMeasureToPMF p) t).toReal /
              ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal) := by
    simpa [InfoGeometry.fin_kl_div, InfoGeometry.KL.kl_div] using
      (toReal_fin_klDiv_eq_sum_log_ratio_of_supportFaithful
        (P := probMeasureToPMF p)
        (Q := probMeasureToPMF (IBNextEncoder q_n β D hInt x))
        (hQ := hnext_sf))
  have hvar :=
    finiteSlice_kl_gibbs_variational_identity_of_supportFaithful
      (q_n := q_n) (β := β) (D := D) (x := x)
      (p := p) hpq
  have hmom :
      (∑ i ∈ J.index, lam i * J.moment (probMeasureToPMF p) (J.feature i))
        =
      -β * ∑ t : T, ((probMeasureToPMF p) t).toReal * D x t := by
    simp [J, lam, finiteSliceJaynes, FiniteJaynesProblem.ofLogLikelihood,
      FiniteJaynesProblem.moment,
      InfoGeometry.Canonical.IBMeasure.distortionRV]
  have hgibbs :
      (∑ t : T,
        ((probMeasureToPMF p) t).toReal *
          Real.log
            (((probMeasureToPMF p) t).toReal /
              ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal))
        =
      ∑ t : T,
        ((probMeasureToPMF p) t).toReal *
          Real.log (((probMeasureToPMF p) t).toReal / J.gibbsProb lam hZ t) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    have hEq :=
      congrArg (fun pmf : PMF T => ((pmf t).toReal))
        (probMeasureToPMF_IBNextEncoder_eq_finiteSliceGibbs
          (q_n := q_n) (β := β) (D := D) (hInt := hInt) (x := x))
    have hEq' :
        ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal
          = J.gibbsProb lam hZ t := by
      simpa [J, lam, hZ, FiniteJaynesProblem.gibbsDist_pointwise] using hEq
    rw [hEq']
  unfold finiteSliceObjective
  have hvar' :
      (InfoGeometry.fin_kl_div
          (probMeasureToPMF p)
          (probMeasureToPMF (IBNextEncoder q_n β D hInt x))).toReal
        =
      (InfoGeometry.fin_kl_div (probMeasureToPMF p) (probMeasureToPMF q_n)).toReal
        + β * ∑ t : T, ((probMeasureToPMF p) t).toReal * D x t
        + J.logPartition lam := by
    calc
      (InfoGeometry.fin_kl_div
          (probMeasureToPMF p)
          (probMeasureToPMF (IBNextEncoder q_n β D hInt x))).toReal
          =
        ∑ t : T,
          ((probMeasureToPMF p) t).toReal *
            Real.log (((probMeasureToPMF p) t).toReal /
              ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal) := hKLnext
      _ =
        ∑ t : T,
          ((probMeasureToPMF p) t).toReal *
            Real.log (((probMeasureToPMF p) t).toReal / J.gibbsProb lam hZ t) := hgibbs
      _ =
        ∑ t : T,
          ((probMeasureToPMF p) t).toReal *
            Real.log (((probMeasureToPMF p) t).toReal / ((probMeasureToPMF q_n) t).toReal)
          - (∑ i ∈ J.index, lam i * J.moment (probMeasureToPMF p) (J.feature i))
          + J.logPartition lam := hvar
      _ =
        (InfoGeometry.fin_kl_div (probMeasureToPMF p) (probMeasureToPMF q_n)).toReal
          + β * ∑ t : T, ((probMeasureToPMF p) t).toReal * D x t
          + J.logPartition lam := by
            rw [hKLq, hmom]
            ring
  linarith

lemma finiteSliceObjective_minimized_by_IBNextEncoder_of_supportFaithful
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (x : X)
    (p : ProbabilityMeasure T)
    (hpq :
      PMFSupportFaithful
        (probMeasureToPMF p)
        (probMeasureToPMF q_n)) :
    finiteSliceObjective q_n β D x (IBNextEncoder q_n β D hInt x)
      ≤
    finiteSliceObjective q_n β D x p := by
  have hnextEq :=
    finiteSliceObjective_eq_kl_to_next_minus_logPartition_of_supportFaithful
      (q_n := q_n) (β := β) (D := D) (hInt := hInt) (x := x)
      (p := IBNextEncoder q_n β D hInt x)
      (IBNextEncoder_supportFaithful_ref q_n β D hInt x)
  have hpEq :=
    finiteSliceObjective_eq_kl_to_next_minus_logPartition_of_supportFaithful
      (q_n := q_n) (β := β) (D := D) (hInt := hInt) (x := x)
      (p := p) hpq
  have hnonneg :
      0 ≤
        (InfoGeometry.fin_kl_div
          (probMeasureToPMF p)
          (probMeasureToPMF (IBNextEncoder q_n β D hInt x))).toReal := by
    exact ENNReal.toReal_nonneg
  have hself :
      (InfoGeometry.fin_kl_div
        (probMeasureToPMF (IBNextEncoder q_n β D hInt x))
        (probMeasureToPMF (IBNextEncoder q_n β D hInt x))).toReal = 0 := by
    simp [InfoGeometry.fin_kl_div]
  rw [hnextEq, hpEq, hself]
  linarith

lemma finiteSliceObjective_eq_kl_to_next_minus_logPartition
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (x : X)
    (p : ProbabilityMeasure T)
    (hq : ∀ t : T, 0 < ((probMeasureToPMF q_n) t).toReal) :
    finiteSliceObjective q_n β D x p
      =
    (InfoGeometry.fin_kl_div
      (probMeasureToPMF p)
      (probMeasureToPMF (IBNextEncoder q_n β D hInt x))).toReal
      - (finiteSliceJaynes q_n D x).logPartition (fun _ => β) := by
  exact finiteSliceObjective_eq_kl_to_next_minus_logPartition_of_supportFaithful
    (q_n := q_n) (β := β) (D := D) (hInt := hInt) (x := x) (p := p)
    (fun t hPt => hq t)

lemma finiteSliceObjective_minimized_by_IBNextEncoder
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (x : X)
    (p : ProbabilityMeasure T)
    (hq : ∀ t : T, 0 < ((probMeasureToPMF q_n) t).toReal) :
    finiteSliceObjective q_n β D x (IBNextEncoder q_n β D hInt x)
      ≤
    finiteSliceObjective q_n β D x p := by
  exact finiteSliceObjective_minimized_by_IBNextEncoder_of_supportFaithful
    (q_n := q_n) (β := β) (D := D) (hInt := hInt) (x := x) (p := p)
    (fun t hPt => hq t)

theorem encoderDescent_finite_supportFaithful
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (p_old : X → ProbabilityMeasure T)
    (hp_old :
      ∀ x : X,
        PMFSupportFaithful
          (probMeasureToPMF (p_old x))
          (probMeasureToPMF q_n)) :
    let hKL_encoder :=
      finiteKLFamily_of_supportFaithful_ref
        q_n
        (IBNextEncoder q_n β D hInt)
        (IBNextEncoder_supportFaithful_ref q_n β D hInt)
    let hKL_old := finiteKLFamily_of_supportFaithful_ref q_n p_old hp_old
    IBGlobalFreeEnergy pX q_n β D (IBNextEncoder q_n β D hInt) hKL_encoder
      ≤
    IBGlobalFreeEnergy pX q_n β D p_old hKL_old := by
  intro hKL_encoder hKL_old
  have hnext_expand :
      IBGlobalFreeEnergy pX q_n β D (IBNextEncoder q_n β D hInt) hKL_encoder
        =
      finiteWeightedDistortion pX β D (IBNextEncoder q_n β D hInt)
        + finiteWeightedKL pX q_n (IBNextEncoder q_n β D hInt) := by
    simpa using
      (IBGlobalFreeEnergy_eq_finiteWeighted
        (pX := pX) (ref := q_n) (β := β) (D := D)
        (encoder := IBNextEncoder q_n β D hInt)
        (hKL := hKL_encoder))
  have hold_expand :
      IBGlobalFreeEnergy pX q_n β D p_old hKL_old
        =
      finiteWeightedDistortion pX β D p_old
        + finiteWeightedKL pX q_n p_old := by
    simpa using
      (IBGlobalFreeEnergy_eq_finiteWeighted
        (pX := pX) (ref := q_n) (β := β) (D := D)
        (encoder := p_old) (hKL := hKL_old))
  rw [hnext_expand, hold_expand]
  let w : X → ℝ := fun x => ((probMeasureToPMF pX) x).toReal
  let localObj : X → (X → ProbabilityMeasure T) → ℝ :=
    fun x encoder =>
      finiteSliceObjective q_n β D x (encoder x)
  have hslice :
      ∀ x : X,
        localObj x (IBNextEncoder q_n β D hInt) ≤ localObj x p_old := by
    intro x
    exact finiteSliceObjective_minimized_by_IBNextEncoder_of_supportFaithful
      (q_n := q_n) (β := β) (D := D) (hInt := hInt)
      (x := x) (p := p_old x) (hp_old x)
  have hsum :
      ∑ x : X, w x * localObj x (IBNextEncoder q_n β D hInt)
        ≤
      ∑ x : X, w x * localObj x p_old := by
    refine Finset.sum_le_sum ?_
    intro x hx
    exact mul_le_mul_of_nonneg_left (hslice x) (by exact ENNReal.toReal_nonneg)
  let nextDistTerm : X → ℝ := fun x =>
    ((probMeasureToPMF pX) x).toReal *
      (β * ∑ t : T, ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal * D x t)
  let nextKLTerm : X → ℝ := fun x =>
    ((probMeasureToPMF pX) x).toReal *
      (InfoGeometry.fin_kl_div
        (probMeasureToPMF (IBNextEncoder q_n β D hInt x))
        (probMeasureToPMF q_n)).toReal
  let oldDistTerm : X → ℝ := fun x =>
    ((probMeasureToPMF pX) x).toReal *
      (β * ∑ t : T, ((probMeasureToPMF (p_old x)) t).toReal * D x t)
  let oldKLTerm : X → ℝ := fun x =>
    ((probMeasureToPMF pX) x).toReal *
      (InfoGeometry.fin_kl_div
        (probMeasureToPMF (p_old x))
        (probMeasureToPMF q_n)).toReal
  have hnext_repack :
      finiteWeightedDistortion pX β D (IBNextEncoder q_n β D hInt)
        + finiteWeightedKL pX q_n (IBNextEncoder q_n β D hInt)
        =
      ∑ x : X, w x * localObj x (IBNextEncoder q_n β D hInt) := by
    unfold w localObj finiteSliceObjective finiteWeightedDistortion finiteWeightedKL
    calc
      (∑ x : X, nextDistTerm x) + (∑ x : X, nextKLTerm x)
          =
        ∑ x : X, (nextDistTerm x + nextKLTerm x) := by
            rw [← Finset.sum_add_distrib]
      _ = ∑ x : X, w x * localObj x (IBNextEncoder q_n β D hInt) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            unfold nextDistTerm nextKLTerm w localObj finiteSliceObjective
            ring_nf
  have hold_repack :
      finiteWeightedDistortion pX β D p_old
        + finiteWeightedKL pX q_n p_old
        =
      ∑ x : X, w x * localObj x p_old := by
    unfold w localObj finiteSliceObjective finiteWeightedDistortion finiteWeightedKL
    calc
      (∑ x : X, oldDistTerm x) + (∑ x : X, oldKLTerm x)
          =
        ∑ x : X, (oldDistTerm x + oldKLTerm x) := by
            rw [← Finset.sum_add_distrib]
      _ = ∑ x : X, w x * localObj x p_old := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            unfold oldDistTerm oldKLTerm w localObj finiteSliceObjective
            ring_nf
  calc
    finiteWeightedDistortion pX β D (IBNextEncoder q_n β D hInt)
        + finiteWeightedKL pX q_n (IBNextEncoder q_n β D hInt)
      = ∑ x : X, w x * localObj x (IBNextEncoder q_n β D hInt) := hnext_repack
    _ ≤ ∑ x : X, w x * localObj x p_old := hsum
    _ = finiteWeightedDistortion pX β D p_old + finiteWeightedKL pX q_n p_old := hold_repack.symm

theorem ibDescentWitness_finite_supportFaithful
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (p_old : X → ProbabilityMeasure T)
    (hp_old :
      ∀ x : X,
        PMFSupportFaithful
          (probMeasureToPMF (p_old x))
          (probMeasureToPMF q_n)) :
    IBDescentWitness pX q_n β D hInt h_meas
      (finiteKLFamily_of_supportFaithful_ref
        q_n
        (IBNextEncoder q_n β D hInt)
        (IBNextEncoder_supportFaithful_ref q_n β D hInt))
      p_old := by
  let hKL_encoder :=
    finiteKLFamily_of_supportFaithful_ref
      q_n
      (IBNextEncoder q_n β D hInt)
      (IBNextEncoder_supportFaithful_ref q_n β D hInt)
  let hKL_old :=
    finiteKLFamily_of_supportFaithful_ref q_n p_old hp_old
  let hnext :=
    IBNextEncoder_supportFaithful_nextMarginal
      (pX := pX) (q_n := q_n) (β := β) (D := D) (hInt := hInt)
      (h_meas := h_meas)
  let hKL_next :=
    finiteKLFamily_of_supportFaithful_ref
      (IBNextMarginal pX q_n β D hInt h_meas)
      (IBNextEncoder q_n β D hInt)
      hnext
  change IBDescentWitness pX q_n β D hInt h_meas hKL_encoder p_old
  refine ⟨hKL_old, hKL_next, ?_, ?_⟩
  · exact encoderDescent_finite_supportFaithful
      (pX := pX) (q_n := q_n) (β := β) (D := D)
      (hInt := hInt) (p_old := p_old) hp_old
  · exact ibMarginalDescentWitness_finite_supportFaithful
      (pX := pX) (q_n := q_n) (β := β) (D := D)
      (hInt := hInt) (h_meas := h_meas)

theorem IB_monotone_descent_finite_supportFaithful
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (p_old : X → ProbabilityMeasure T)
    (hp_old :
      ∀ x : X,
        PMFSupportFaithful
          (probMeasureToPMF (p_old x))
          (probMeasureToPMF q_n)) :
    IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D
      (IBNextEncoder q_n β D hInt)
      (finiteKLFamily_of_supportFaithful_ref
        (IBNextMarginal pX q_n β D hInt h_meas)
        (IBNextEncoder q_n β D hInt)
        (IBNextEncoder_supportFaithful_nextMarginal
          (pX := pX) (q_n := q_n) (β := β) (D := D) (hInt := hInt)
          (h_meas := h_meas)))
      ≤
    IBGlobalFreeEnergy pX q_n β D p_old
      (finiteKLFamily_of_supportFaithful_ref q_n p_old hp_old) := by
  let hKL_encoder :=
    finiteKLFamily_of_supportFaithful_ref
      q_n
      (IBNextEncoder q_n β D hInt)
      (IBNextEncoder_supportFaithful_ref q_n β D hInt)
  let hKL_old := finiteKLFamily_of_supportFaithful_ref q_n p_old hp_old
  let hnext :=
    IBNextEncoder_supportFaithful_nextMarginal
      (pX := pX) (q_n := q_n) (β := β) (D := D) (hInt := hInt)
      (h_meas := h_meas)
  let hKL_next :=
    finiteKLFamily_of_supportFaithful_ref
      (IBNextMarginal pX q_n β D hInt h_meas)
      (IBNextEncoder q_n β D hInt)
      hnext
  change IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D
      (IBNextEncoder q_n β D hInt) hKL_next
      ≤
    IBGlobalFreeEnergy pX q_n β D p_old hKL_old
  exact IB_monotone_descent
    (pX := pX) (q_n := q_n) (β := β) (D := D)
    (hInt := hInt) (h_meas := h_meas) (hKL_encoder := hKL_encoder)
    (p_old := p_old) (hKL_old := hKL_old) (hKL_next := hKL_next)
    (h_encoder := encoderDescent_finite_supportFaithful
      (pX := pX) (q_n := q_n) (β := β) (D := D)
      (hInt := hInt) (p_old := p_old) (hp_old := hp_old))
    (h_marginal := ibMarginalDescentWitness_finite_supportFaithful
      (pX := pX) (q_n := q_n) (β := β) (D := D)
      (hInt := hInt) (h_meas := h_meas))

theorem encoderDescent_finite_fullSupport
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (p_old : X → ProbabilityMeasure T)
    (hq : ∀ t : T, 0 < ((probMeasureToPMF q_n) t).toReal) :
    let hKL_encoder :=
      finiteKLFamily_of_positive_ref q_n (IBNextEncoder q_n β D hInt) hq
    let hKL_old := finiteKLFamily_of_positive_ref q_n p_old hq
    IBGlobalFreeEnergy pX q_n β D (IBNextEncoder q_n β D hInt) hKL_encoder
      ≤
    IBGlobalFreeEnergy pX q_n β D p_old hKL_old := by
  intro hKL_encoder hKL_old
  let hKL_encoder' :=
    finiteKLFamily_of_supportFaithful_ref
      q_n
      (IBNextEncoder q_n β D hInt)
      (IBNextEncoder_supportFaithful_ref q_n β D hInt)
  let hKL_old' :=
    finiteKLFamily_of_supportFaithful_ref q_n p_old (fun x t hpos => hq t)
  simpa [hKL_encoder', hKL_old'] using
    (encoderDescent_finite_supportFaithful
      (pX := pX) (q_n := q_n) (β := β) (D := D)
      (hInt := hInt) (p_old := p_old) (hp_old := fun x t hpos => hq t))

theorem ibDescentWitness_finite_fullSupport
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (p_old : X → ProbabilityMeasure T)
    (hq : ∀ t : T, 0 < ((probMeasureToPMF q_n) t).toReal) :
    IBDescentWitness pX q_n β D hInt h_meas
      (finiteKLFamily_of_positive_ref q_n (IBNextEncoder q_n β D hInt) hq) p_old := by
  let hKL_encoder' :=
    finiteKLFamily_of_supportFaithful_ref
      q_n
      (IBNextEncoder q_n β D hInt)
      (IBNextEncoder_supportFaithful_ref q_n β D hInt)
  simpa [hKL_encoder'] using
    (ibDescentWitness_finite_supportFaithful
      (pX := pX) (q_n := q_n) (β := β) (D := D)
      (hInt := hInt) (h_meas := h_meas) (p_old := p_old)
      (hp_old := fun x t hpos => hq t))

theorem IB_monotone_descent_finite_fullSupport
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (p_old : X → ProbabilityMeasure T)
    (hq : ∀ t : T, 0 < ((probMeasureToPMF q_n) t).toReal) :
    IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D
      (IBNextEncoder q_n β D hInt)
      (finiteKLFamily_of_positive_ref
        (IBNextMarginal pX q_n β D hInt h_meas)
        (IBNextEncoder q_n β D hInt)
        (IBNextMarginal_positive_of_encoder_positive
          (pX := pX) (q_n := q_n) (β := β) (D := D) (hInt := hInt)
          (h_meas := h_meas)
          (IBNextEncoder_positive_of_fullSupport q_n β D hInt hq)))
      ≤
    IBGlobalFreeEnergy pX q_n β D p_old
      (finiteKLFamily_of_positive_ref q_n p_old hq) := by
  have henc := IBNextEncoder_positive_of_fullSupport q_n β D hInt hq
  let hKL_next' :=
    finiteKLFamily_of_supportFaithful_ref
      (IBNextMarginal pX q_n β D hInt h_meas)
      (IBNextEncoder q_n β D hInt)
      (IBNextEncoder_supportFaithful_nextMarginal
        (pX := pX) (q_n := q_n) (β := β) (D := D) (hInt := hInt) (h_meas := h_meas))
  simpa [hKL_next'] using
    (IB_monotone_descent_finite_supportFaithful
      (pX := pX) (q_n := q_n) (β := β) (D := D)
      (hInt := hInt) (h_meas := h_meas) (p_old := p_old)
      (hp_old := fun x t hpos => hq t))

end InfoGeometry.Canonical.IBFiniteMonotonicity
