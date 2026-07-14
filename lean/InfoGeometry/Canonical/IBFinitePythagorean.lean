import InfoGeometry.Canonical.IBPythagorean
import InfoGeometry.EntropicInference
import InfoGeometry.Measure.Normalized
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open MeasureTheory
open scoped BigOperators ENNReal

namespace IBFinitePythagorean

open InfoGeometry.Canonical.IBFreeEnergy
open InfoGeometry.Canonical.IBFunctional
open InfoGeometry.Canonical.IBPythagorean
open InfoGeometry.MeasureProjective.Normalized

set_option linter.unusedSectionVars false

variable {X T : Type*}
variable [Fintype X] [Fintype T]
variable [DecidableEq X] [DecidableEq T]
variable [MeasurableSpace X] [MeasurableSpace T]
variable [MeasurableSingletonClass X] [MeasurableSingletonClass T]
variable [Nonempty T]

lemma probMeasureToPMF_toMeasure {α : Type*}
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : ProbabilityMeasure α) :
    ((probMeasureToPMF P).toMeasure : Measure α) = (P : Measure α) := by
  change (((pmfToProbMeasure (probMeasureToPMF P)) : ProbabilityMeasure α) : Measure α) = (P : Measure α)
  simpa using congrArg (fun Q : ProbabilityMeasure α => (Q : Measure α))
    (pmfToProbMeasure_probMeasureToPMF P)

lemma pmf_toMeasure_eq_count_withDensity {α : Type*}
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) :
    p.toMeasure = Measure.count.withDensity (fun a => p a) := by
  ext s hs
  rw [p.toMeasure_apply hs, withDensity_apply (fun a => p a) hs,
    ← MeasureTheory.lintegral_indicator hs, MeasureTheory.lintegral_count]

lemma lintegral_eq_tsum_probMeasure {α : Type*}
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : ProbabilityMeasure α)
    (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂(P : Measure α) = ∑' a, (probMeasureToPMF P a) * f a := by
  rw [← probMeasureToPMF_toMeasure P, pmf_toMeasure_eq_count_withDensity]
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable
    Measure.count (measurable_of_finite (probMeasureToPMF P))]
  · rw [MeasureTheory.lintegral_count]
    exact tsum_congr (fun a => by rw [Pi.mul_apply, mul_comm])
  · filter_upwards with a
    exact (probMeasureToPMF P).apply_lt_top a

/-- Finite weighted distortion term for a discrete encoder family. -/
noncomputable def finiteWeightedDistortion
    (pX : ProbabilityMeasure X)
    (β : ℝ)
    (D : X → T → ℝ)
    (encoder : X → ProbabilityMeasure T) : ℝ :=
  ∑ x : X,
    ((probMeasureToPMF pX) x).toReal *
      (β * ∑ t : T, ((probMeasureToPMF (encoder x)) t).toReal * D x t)

/-- Finite weighted KL term for a discrete encoder family. -/
noncomputable def finiteWeightedKL
    (pX : ProbabilityMeasure X)
    (ref : ProbabilityMeasure T)
    (encoder : X → ProbabilityMeasure T) : ℝ :=
  ∑ x : X,
    ((probMeasureToPMF pX) x).toReal *
      (InfoGeometry.fin_kl_div
        (probMeasureToPMF (encoder x))
        (probMeasureToPMF ref)).toReal

lemma finiteKLFamily_of_positive_ref
    (ref : ProbabilityMeasure T)
    (encoder : X → ProbabilityMeasure T)
    (href : ∀ t : T, 0 < ((probMeasureToPMF ref) t).toReal) :
    FiniteKLFamily (ref : Measure T) encoder := by
  intro x
  have h :=
    InfoGeometry.EntropicInference.kl_div_ne_top_of_right_toReal_pos
      (P := probMeasureToPMF (encoder x))
      (Q := probMeasureToPMF ref)
      href
  rw [show (encoder x : Measure T) = (probMeasureToPMF (encoder x)).toMeasure by
      simpa using (probMeasureToPMF_toMeasure (encoder x)).symm]
  rw [show (ref : Measure T) = (probMeasureToPMF ref).toMeasure by
      simpa using (probMeasureToPMF_toMeasure ref).symm]
  simpa [klDivENN, InfoGeometry.KL.kl_div, InfoGeometry.fin_kl_div] using h

lemma integral_eq_sum_probMeasure
    (P : ProbabilityMeasure X)
    (f : X → ℝ) :
    ∫ x, f x ∂(P : Measure X)
      = ∑ x : X, ((probMeasureToPMF P) x).toReal * f x := by
  rw [← probMeasureToPMF_toMeasure P]
  simpa [smul_eq_mul] using
    (PMF.integral_eq_sum (p := probMeasureToPMF P) (f := f))

lemma klDiv_eq_fin_klDiv_toReal
    (ref : ProbabilityMeasure T)
    (encoder : ProbabilityMeasure T)
    (hKL : klDivENN (encoder : Measure T) (ref : Measure T) ≠ ⊤) :
    klDiv (encoder : Measure T) (ref : Measure T) hKL
      =
    (InfoGeometry.fin_kl_div (probMeasureToPMF encoder) (probMeasureToPMF ref)).toReal := by
  unfold klDiv klDivENN InfoGeometry.KL.kl_div InfoGeometry.fin_kl_div
  simp [probMeasureToPMF_toMeasure]

theorem IBGlobalFreeEnergy_eq_finiteWeighted
    (pX : ProbabilityMeasure X)
    (ref : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (encoder : X → ProbabilityMeasure T)
    (hKL : FiniteKLFamily (ref : Measure T) encoder) :
    IBGlobalFreeEnergy pX ref β D encoder hKL
      =
    finiteWeightedDistortion pX β D encoder
      + finiteWeightedKL pX ref encoder := by
  let localTerm : X → ℝ := fun x =>
    ((probMeasureToPMF pX) x).toReal *
      (β * ∑ t : T, ((probMeasureToPMF (encoder x)) t).toReal * D x t
        + (InfoGeometry.fin_kl_div
            (probMeasureToPMF (encoder x))
            (probMeasureToPMF ref)).toReal)
  calc
    IBGlobalFreeEnergy pX ref β D encoder hKL
        =
      ∑ x : X, localTerm x := by
      unfold IBGlobalFreeEnergy
      rw [integral_eq_sum_probMeasure
        (P := pX)
        (f := fun x => IBLocalFreeEnergy (ref : Measure T) β D x (encoder x) (hKL x))]
      refine Finset.sum_congr rfl ?_
      intro x hx
      change
        ((probMeasureToPMF pX) x).toReal *
          IBLocalFreeEnergy (ref : Measure T) β D x (encoder x) (hKL x)
          =
        localTerm x
      unfold IBLocalFreeEnergy
      rw [integral_eq_sum_probMeasure (P := encoder x) (f := D x)]
      rw [klDiv_eq_fin_klDiv_toReal (ref := ref) (encoder := encoder x) (hKL := hKL x)]
    _ =
      finiteWeightedDistortion pX β D encoder
        + finiteWeightedKL pX ref encoder := by
      calc
        ∑ x : X, localTerm x
            =
          ∑ x : X,
            ((((probMeasureToPMF pX) x).toReal *
                (β * ∑ t : T, ((probMeasureToPMF (encoder x)) t).toReal * D x t))
              +
            (((probMeasureToPMF pX) x).toReal *
                (InfoGeometry.fin_kl_div
                  (probMeasureToPMF (encoder x))
                  (probMeasureToPMF ref)).toReal)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [localTerm]
          ring
        _ =
          (∑ x : X,
            ((probMeasureToPMF pX) x).toReal *
              (β * ∑ t : T, ((probMeasureToPMF (encoder x)) t).toReal * D x t))
          +
          (∑ x : X,
            ((probMeasureToPMF pX) x).toReal *
              (InfoGeometry.fin_kl_div
                (probMeasureToPMF (encoder x))
                (probMeasureToPMF ref)).toReal) := by
          rw [Finset.sum_add_distrib]
        _ = finiteWeightedDistortion pX β D encoder + finiteWeightedKL pX ref encoder := by
          rfl

/-- Support-faithfulness of a PMF reference to a source PMF. -/
def PMFSupportFaithful {α : Type*} [Fintype α]
    (P Q : PMF α) : Prop :=
  ∀ a : α, 0 < (P a).toReal → 0 < (Q a).toReal

lemma pmf_absolutelyContinuous_of_supportFaithful
    {α : Type*}
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : PMF α)
    (hQ : PMFSupportFaithful P Q) :
    P.toMeasure ≪ Q.toMeasure := by
  intro s hQs
  have hs : MeasurableSet s := (Set.toFinite s).measurableSet
  have hQs' : Disjoint Q.support s := (Q.toMeasure_apply_eq_zero_iff hs).1 hQs
  refine (P.toMeasure_apply_eq_zero_iff hs).2 ?_
  refine Set.disjoint_left.2 ?_
  intro x hxP hxS
  have hPx : P x ≠ 0 := (P.mem_support_iff x).1 hxP
  have hPx_toReal : 0 < (P x).toReal := ENNReal.toReal_pos hPx (P.apply_ne_top x)
  have hxQ : x ∈ Q.support := by
    refine (Q.mem_support_iff x).2 ?_
    intro hQx
    have : 0 < (Q x).toReal := hQ x hPx_toReal
    simp [hQx] at this
  exact (Set.disjoint_left.1 hQs' hxQ) hxS

lemma klDiv_ne_top_of_supportFaithful
    {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : PMF α)
    (hQ : PMFSupportFaithful P Q) :
    InfoGeometry.fin_kl_div P Q ≠ ⊤ := by
  have h_ac : P.toMeasure ≪ Q.toMeasure :=
    pmf_absolutelyContinuous_of_supportFaithful P Q hQ
  have h_int :
      Integrable (MeasureTheory.llr P.toMeasure Q.toMeasure) P.toMeasure :=
    InfoGeometry.MaxEnt.IProjection.integrable_of_fintype _ _
  simpa [InfoGeometry.fin_kl_div, InfoGeometry.KL.kl_div] using
    (InformationTheory.klDiv_ne_top_iff).2 ⟨h_ac, h_int⟩

lemma toReal_fin_klDiv_eq_sum_log_ratio_of_supportFaithful
    {α : Type*}
    [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : PMF α)
    (hQ : PMFSupportFaithful P Q) :
    (InfoGeometry.fin_kl_div P Q).toReal
      =
    ∑ a : α, (P a).toReal * Real.log ((P a).toReal / (Q a).toReal) := by
  have h_ac : P.toMeasure ≪ Q.toMeasure :=
    pmf_absolutelyContinuous_of_supportFaithful P Q hQ
  have h_mass : P.toMeasure Set.univ = Q.toMeasure Set.univ := by
    simp
  rw [show InfoGeometry.fin_kl_div P Q = InformationTheory.klDiv P.toMeasure Q.toMeasure by
      rfl]
  rw [InformationTheory.toReal_klDiv_of_measure_eq h_ac h_mass]
  have h_rn := InfoGeometry.Measure.DiscreteRN.rnDeriv_pmf_eq_div P Q h_ac
  have h_int :
      (∫ x, MeasureTheory.llr P.toMeasure Q.toMeasure x ∂P.toMeasure)
        =
      ∫ x, Real.log (((P x : ℝ≥0∞) / (Q x : ℝ≥0∞)).toReal) ∂P.toMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [h_rn] with x hx
    simp [MeasureTheory.llr_def, hx]
  rw [h_int, PMF.integral_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  congr 1
  rw [ENNReal.toReal_div]

lemma finiteKLFamily_of_supportFaithful_ref
    (ref : ProbabilityMeasure T)
    (encoder : X → ProbabilityMeasure T)
    (href :
      ∀ x : X, ∀ t : T,
        0 < ((probMeasureToPMF (encoder x)) t).toReal
          → 0 < ((probMeasureToPMF ref) t).toReal) :
    FiniteKLFamily (ref : Measure T) encoder := by
  intro x
  have h :=
    klDiv_ne_top_of_supportFaithful
      (P := probMeasureToPMF (encoder x))
      (Q := probMeasureToPMF ref)
      (hQ := href x)
  rw [show (encoder x : Measure T) = (probMeasureToPMF (encoder x)).toMeasure by
      simpa using (probMeasureToPMF_toMeasure (encoder x)).symm]
  rw [show (ref : Measure T) = (probMeasureToPMF ref).toMeasure by
      simpa using (probMeasureToPMF_toMeasure ref).symm]
  simpa [klDivENN, InfoGeometry.KL.kl_div, InfoGeometry.fin_kl_div] using h

lemma probMeasureToPMF_IBNextMarginal_eq_bind
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T))) :
    probMeasureToPMF (IBNextMarginal pX q_n β D hInt h_meas)
      =
    (probMeasureToPMF pX).bind (fun x => probMeasureToPMF (IBNextEncoder q_n β D hInt x)) := by
  ext t
  rw [probMeasureToPMF_apply]
  rw [IBIteration.IBStep_apply (pX := pX) (qT := q_n) (β := β) (D := D)
    (hInt := hInt) (h_meas := h_meas) (hs := measurableSet_singleton t)]
  have hfun :
      (fun x => ((IBNextEncoder q_n β D hInt x : Measure T) {t}))
        =
      fun x => (probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t := by
    funext x
    symm
    exact probMeasureToPMF_apply (IBNextEncoder q_n β D hInt x) t
  rw [hfun]
  rw [lintegral_eq_tsum_probMeasure
    (P := pX)
    (f := fun x => (probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t)]
  rw [PMF.bind_apply]

lemma integral_exp_neg_distortion_pos
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (x : X) :
    0 < ∫ t, Real.exp (-β * D x t) ∂(q_n : Measure T) := by
  let qpmf := probMeasureToPMF q_n
  obtain ⟨t0, ht0⟩ := qpmf.support_nonempty
  have hq0 : 0 < (qpmf t0).toReal :=
    ENNReal.toReal_pos ((qpmf.mem_support_iff t0).1 ht0) (qpmf.apply_ne_top t0)
  rw [integral_eq_sum_probMeasure (P := q_n) (f := fun t => Real.exp (-β * D x t))]
  have hterm :
      0 < (qpmf t0).toReal * Real.exp (-β * D x t0) := by
    exact mul_pos hq0 (Real.exp_pos _)
  have hle :
      (qpmf t0).toReal * Real.exp (-β * D x t0)
        ≤
      ∑ t : T, (qpmf t).toReal * Real.exp (-β * D x t) := by
    exact Finset.single_le_sum
      (f := fun t : T => (qpmf t).toReal * Real.exp (-β * D x t))
      (s := Finset.univ)
      (by
        intro t _ht
        exact mul_nonneg ENNReal.toReal_nonneg (le_of_lt (Real.exp_pos _)))
      (by simp)
  exact lt_of_lt_of_le hterm hle

lemma probMeasureToPMF_IBNextEncoder_toReal
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (x : X)
    (t : T) :
    ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal
      =
    ((probMeasureToPMF q_n) t).toReal
      * (Real.exp (-β * D x t) / ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T)) := by
  rw [probMeasureToPMF_apply]
  change
    (((InfoGeometry.Canonical.IBMeasure.IBGibbsMeasure (qT := (q_n : Measure T)) β D x) {t}).toReal)
      =
    ((probMeasureToPMF q_n) t).toReal
      * (Real.exp (-β * D x t) / ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T))
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
            Real.exp (-β * D x a) /
              ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T)
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
  have hmass :
      ((q_n : Measure T).real {t}) = ((probMeasureToPMF q_n) t).toReal := by
    simp [probMeasureToPMF_apply, measureReal_def]
  rw [hmass]

lemma IBNextEncoder_positive_of_ref_positive
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (x : X)
    (t : T)
    (hq : 0 < ((probMeasureToPMF q_n) t).toReal) :
    0 < ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal := by
  rw [probMeasureToPMF_IBNextEncoder_toReal
    (q_n := q_n) (β := β) (D := D) (hInt := hInt) (x := x) (t := t)]
  have hZ : 0 < ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T) :=
    integral_exp_neg_distortion_pos q_n β D x
  exact mul_pos hq (div_pos (Real.exp_pos _) hZ)

lemma ref_positive_of_IBNextEncoder_positive
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (x : X)
    (t : T)
    (henc : 0 < ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal) :
    0 < ((probMeasureToPMF q_n) t).toReal := by
  rw [probMeasureToPMF_IBNextEncoder_toReal
    (q_n := q_n) (β := β) (D := D) (hInt := hInt) (x := x) (t := t)] at henc
  have hZ : 0 < ∫ a, Real.exp (-β * D x a) ∂(q_n : Measure T) :=
    integral_exp_neg_distortion_pos q_n β D x
  exact (mul_pos_iff_of_pos_right (div_pos (Real.exp_pos _) hZ)).1 henc

lemma IBNextEncoder_supportFaithful_ref
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T)) :
    ∀ x : X, ∀ t : T,
      0 < ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal
        → 0 < ((probMeasureToPMF q_n) t).toReal :=
  ref_positive_of_IBNextEncoder_positive q_n β D hInt

lemma IBNextMarginal_positive_of_ref_positive
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (t : T)
    (hq : 0 < ((probMeasureToPMF q_n) t).toReal) :
    0 < ((probMeasureToPMF (IBNextMarginal pX q_n β D hInt h_meas)) t).toReal := by
  rw [probMeasureToPMF_IBNextMarginal_eq_bind
    (pX := pX) (q_n := q_n) (β := β) (D := D) (hInt := hInt) (h_meas := h_meas)]
  let pXpmf := probMeasureToPMF pX
  let enc := fun x => probMeasureToPMF (IBNextEncoder q_n β D hInt x)
  obtain ⟨x0, hx0⟩ := pXpmf.support_nonempty
  have hpX_pos : 0 < (pXpmf x0).toReal :=
    ENNReal.toReal_pos ((pXpmf.mem_support_iff x0).1 hx0) (pXpmf.apply_ne_top x0)
  have henc_pos : 0 < (enc x0 t).toReal :=
    IBNextEncoder_positive_of_ref_positive q_n β D hInt x0 t hq
  have hpX_ne : pXpmf x0 ≠ 0 := (PMF.mem_support_iff pXpmf x0).1 hx0
  have henc_ne : enc x0 t ≠ 0 := by
    intro h0
    have : 0 < (enc x0 t).toReal := henc_pos
    simp [h0] at this
  have hterm_pos : 0 < pXpmf x0 * enc x0 t := ENNReal.mul_pos hpX_ne henc_ne
  have hsum_pos : 0 < ∑ x : X, pXpmf x * enc x t := by
    have hle :
        pXpmf x0 * enc x0 t ≤ ∑ x : X, pXpmf x * enc x t := by
      exact Finset.single_le_sum
        (f := fun x : X => pXpmf x * enc x t)
        (s := Finset.univ)
        (fun y _hy => (show 0 ≤ pXpmf y * enc y t by exact zero_le _))
        (by simp)
    exact lt_of_lt_of_le hterm_pos hle
  rw [PMF.bind_apply, tsum_fintype]
  have hne_top : (∑ x : X, pXpmf x * enc x t) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr (fun x _ =>
      ENNReal.mul_ne_top (pXpmf.apply_ne_top x) ((enc x).apply_ne_top t))
  exact ENNReal.toReal_pos hsum_pos.ne' hne_top

lemma IBNextEncoder_supportFaithful_nextMarginal
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T))) :
    ∀ x : X, ∀ t : T,
      0 < ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal
        →
      0 < ((probMeasureToPMF (IBNextMarginal pX q_n β D hInt h_meas)) t).toReal := by
  intro x t henc
  exact IBNextMarginal_positive_of_ref_positive
    (pX := pX) (q_n := q_n) (β := β) (D := D)
    (hInt := hInt) (h_meas := h_meas) (t := t)
    (ref_positive_of_IBNextEncoder_positive q_n β D hInt x t henc)

lemma pmf_bind_apply_toReal
    (pX : PMF X)
    (encoder : X → PMF T)
    (t : T) :
    ((pX.bind encoder) t).toReal
      = ∑ x : X, (pX x).toReal * (encoder x t).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro x hx
    rw [ENNReal.toReal_mul]
  · intro x hx
    exact ENNReal.mul_ne_top (pX.apply_ne_top x) ((encoder x).apply_ne_top t)

lemma pmf_bind_supportFaithful_ref
    (pX : PMF X)
    (encoder : X → PMF T)
    (q : PMF T)
    (hq : ∀ x : X, ∀ t : T, 0 < (encoder x t).toReal → 0 < (q t).toReal) :
    PMFSupportFaithful (pX.bind encoder) q := by
  intro t ht
  rw [pmf_bind_apply_toReal (pX := pX) (encoder := encoder) (t := t)] at ht
  obtain ⟨x, _hx_mem, hx⟩ :
      ∃ x ∈ (Finset.univ : Finset X), (pX x).toReal * (encoder x t).toReal ≠ 0 := by
    refine Finset.exists_ne_zero_of_sum_ne_zero
      (f := fun x : X => (pX x).toReal * (encoder x t).toReal)
      (s := Finset.univ) ?_
    exact ne_of_gt ht
  have hterm_nonneg : 0 ≤ (pX x).toReal * (encoder x t).toReal := by
    exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hterm_pos : 0 < (pX x).toReal * (encoder x t).toReal :=
    lt_of_le_of_ne hterm_nonneg (Ne.symm hx)
  have henc_pos : 0 < (encoder x t).toReal := by
    by_contra hzero
    have hle : (encoder x t).toReal ≤ 0 := by linarith
    have hEq : (encoder x t).toReal = 0 := le_antisymm hle ENNReal.toReal_nonneg
    simp [hEq] at hterm_pos
  exact hq x t henc_pos

lemma IBNextMarginal_supportFaithful_ref
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T))) :
    PMFSupportFaithful
      (probMeasureToPMF (IBNextMarginal pX q_n β D hInt h_meas))
      (probMeasureToPMF q_n) := by
  rw [probMeasureToPMF_IBNextMarginal_eq_bind
    (pX := pX) (q_n := q_n) (β := β) (D := D) (hInt := hInt) (h_meas := h_meas)]
  exact pmf_bind_supportFaithful_ref
    (pX := probMeasureToPMF pX)
    (encoder := fun x => probMeasureToPMF (IBNextEncoder q_n β D hInt x))
    (q := probMeasureToPMF q_n)
    (hq := IBNextEncoder_supportFaithful_ref q_n β D hInt)

lemma IBNextMarginal_positive_of_encoder_positive
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (henc :
      ∀ x : X, ∀ t : T,
        0 < ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal) :
    ∀ t : T,
      0 < ((probMeasureToPMF (IBNextMarginal pX q_n β D hInt h_meas)) t).toReal := by
  intro t
  rw [probMeasureToPMF_IBNextMarginal_eq_bind
    (pX := pX) (q_n := q_n) (β := β) (D := D) (hInt := hInt) (h_meas := h_meas)]
  let pXpmf := probMeasureToPMF pX
  let enc := fun x => probMeasureToPMF (IBNextEncoder q_n β D hInt x)
  obtain ⟨x0, hx0⟩ := pXpmf.support_nonempty
  have hpX_ne : pXpmf x0 ≠ 0 := (PMF.mem_support_iff pXpmf x0).1 hx0
  have henc_ne : enc x0 t ≠ 0 := by
    intro h0
    have hpos := henc x0 t
    simp [enc, h0] at hpos
  have hterm_pos : 0 < pXpmf x0 * enc x0 t := ENNReal.mul_pos hpX_ne henc_ne
  have hsum_pos : 0 < ∑ x : X, pXpmf x * enc x t := by
    have hle :
        pXpmf x0 * enc x0 t ≤ ∑ x : X, pXpmf x * enc x t := by
      exact Finset.single_le_sum
        (fun y _hy => (show 0 ≤ pXpmf y * enc y t by exact zero_le _))
        (Finset.mem_univ x0)
    exact lt_of_lt_of_le hterm_pos hle
  rw [PMF.bind_apply, tsum_fintype]
  have hne_top : (∑ x : X, pXpmf x * enc x t) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr (fun x _ =>
      ENNReal.mul_ne_top (pXpmf.apply_ne_top x) ((enc x).apply_ne_top t))
  exact ENNReal.toReal_pos hsum_pos.ne' hne_top

private lemma log_div_split
    {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.log (a / c) = Real.log (a / b) + Real.log (b / c) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hmul : a / c = (a / b) * (b / c) := by
    field_simp [hb0, hc0]
  rw [hmul, Real.log_mul (by positivity) (by positivity)]

theorem finiteWeightedKL_bind_marginal_decomposition
    (pX : PMF X)
    (encoder : X → PMF T)
    (q : PMF T)
    (hq : ∀ x : X, ∀ t : T, 0 < (encoder x t).toReal → 0 < (q t).toReal)
    (hnext : ∀ x : X, ∀ t : T, 0 < (encoder x t).toReal → 0 < ((pX.bind encoder) t).toReal) :
    (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (encoder x) q).toReal)
      =
    (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (encoder x) (pX.bind encoder)).toReal)
      + (InfoGeometry.fin_kl_div (pX.bind encoder) q).toReal := by
  have hcur :
      ∀ x : X,
        (InfoGeometry.fin_kl_div (encoder x) q).toReal
          =
        ∑ t : T, (encoder x t).toReal * Real.log ((encoder x t).toReal / (q t).toReal) := by
    intro x
    simpa [InfoGeometry.fin_kl_div, InfoGeometry.KL.kl_div] using
      (toReal_fin_klDiv_eq_sum_log_ratio_of_supportFaithful
        (P := encoder x) (Q := q) (hQ := hq x))
  have hnextKL :
      ∀ x : X,
        (InfoGeometry.fin_kl_div (encoder x) (pX.bind encoder)).toReal
          =
        ∑ t : T,
          (encoder x t).toReal * Real.log ((encoder x t).toReal / ((pX.bind encoder) t).toReal) := by
    intro x
    simpa [InfoGeometry.fin_kl_div, InfoGeometry.KL.kl_div] using
      (toReal_fin_klDiv_eq_sum_log_ratio_of_supportFaithful
        (P := encoder x) (Q := pX.bind encoder) (hQ := hnext x))
  have hmarg_support :
      PMFSupportFaithful (pX.bind encoder) q := by
    exact pmf_bind_supportFaithful_ref (pX := pX) (encoder := encoder) (q := q) hq
  have hmarg :
      (InfoGeometry.fin_kl_div (pX.bind encoder) q).toReal
        =
      ∑ t : T, ((pX.bind encoder) t).toReal * Real.log (((pX.bind encoder) t).toReal / (q t).toReal) := by
    simpa [InfoGeometry.fin_kl_div, InfoGeometry.KL.kl_div] using
      (toReal_fin_klDiv_eq_sum_log_ratio_of_supportFaithful
        (P := pX.bind encoder) (Q := q) (hQ := hmarg_support))
  let qNext := pX.bind encoder
  let A : X → ℝ := fun x =>
    ∑ t : T, (encoder x t).toReal * Real.log ((encoder x t).toReal / (qNext t).toReal)
  let B : X → ℝ := fun x =>
    ∑ t : T, (encoder x t).toReal * Real.log ((qNext t).toReal / (q t).toReal)
  have hsplit_inner :
      ∀ x : X,
        ∑ t : T,
          (encoder x t).toReal *
            (Real.log ((encoder x t).toReal / (qNext t).toReal)
              + Real.log ((qNext t).toReal / (q t).toReal))
          = A x + B x := by
    intro x
    unfold A B
    calc
      ∑ t : T,
          (encoder x t).toReal *
            (Real.log ((encoder x t).toReal / (qNext t).toReal)
              + Real.log ((qNext t).toReal / (q t).toReal))
          =
        ∑ t : T,
          (((encoder x t).toReal * Real.log ((encoder x t).toReal / (qNext t).toReal))
            + ((encoder x t).toReal * Real.log ((qNext t).toReal / (q t).toReal))) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              ring
      _ = A x + B x := by
        rw [Finset.sum_add_distrib]
  have hsplit_outer :
      ∑ x : X, (pX x).toReal * (A x + B x)
        =
      (∑ x : X, (pX x).toReal * A x) + (∑ x : X, (pX x).toReal * B x) := by
    calc
      ∑ x : X, (pX x).toReal * (A x + B x)
          =
        ∑ x : X, ((pX x).toReal * A x + (pX x).toReal * B x) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
      _ = (∑ x : X, (pX x).toReal * A x) + (∑ x : X, (pX x).toReal * B x) := by
            rw [Finset.sum_add_distrib]
  have htranspose :
      ∑ x : X, (pX x).toReal * B x
        =
      ∑ t : T,
        (∑ x : X, (pX x).toReal * (encoder x t).toReal) *
          Real.log ((qNext t).toReal / (q t).toReal) := by
    unfold B
    calc
      ∑ x : X,
          (pX x).toReal *
            (∑ t : T, (encoder x t).toReal * Real.log ((qNext t).toReal / (q t).toReal))
          =
        ∑ x : X,
          ∑ t : T,
            ((pX x).toReal * (encoder x t).toReal) * Real.log ((qNext t).toReal / (q t).toReal) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro t ht
              ring
      _ =
        ∑ t : T,
          ∑ x : X,
            ((pX x).toReal * (encoder x t).toReal) * Real.log ((qNext t).toReal / (q t).toReal) := by
              rw [Finset.sum_comm]
      _ =
        ∑ t : T,
          (∑ x : X, (pX x).toReal * (encoder x t).toReal) * Real.log ((qNext t).toReal / (q t).toReal) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              rw [← Finset.sum_mul]
  calc
    (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (encoder x) q).toReal)
        =
      ∑ x : X, (pX x).toReal *
        (∑ t : T, (encoder x t).toReal * Real.log ((encoder x t).toReal / (q t).toReal)) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [hcur x]
    _ =
      ∑ x : X, (pX x).toReal * (A x + B x) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      refine congrArg ((pX x).toReal * ·) ?_
      calc
        ∑ t : T, (encoder x t).toReal * Real.log ((encoder x t).toReal / (q t).toReal)
            =
          ∑ t : T,
            (encoder x t).toReal *
              (Real.log ((encoder x t).toReal / (qNext t).toReal)
                + Real.log ((qNext t).toReal / (q t).toReal)) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              by_cases hzero : (encoder x t).toReal = 0
              · simp [hzero]
              · have henc_pos : 0 < (encoder x t).toReal :=
                  lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
                rw [log_div_split henc_pos (hnext x t henc_pos) (hq x t henc_pos)]
        _ = A x + B x := hsplit_inner x
    _ = (∑ x : X, (pX x).toReal * A x) + (∑ x : X, (pX x).toReal * B x) := hsplit_outer
    _ =
      (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (encoder x) qNext).toReal)
      + (∑ x : X, (pX x).toReal * B x) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x hx
      unfold A
      rw [hnextKL x]
    _ =
      (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (encoder x) qNext).toReal)
      +
      (∑ t : T,
        (∑ x : X, (pX x).toReal * (encoder x t).toReal) *
          Real.log ((qNext t).toReal / (q t).toReal)) := by
      rw [htranspose]
    _ =
      (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (encoder x) (pX.bind encoder)).toReal)
      +
      (∑ t : T,
        (qNext t).toReal * Real.log ((qNext t).toReal / (q t).toReal)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [pmf_bind_apply_toReal]
    _ =
      (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (encoder x) (pX.bind encoder)).toReal)
      + (InfoGeometry.fin_kl_div (pX.bind encoder) q).toReal := by
      simp [qNext, hmarg]

theorem finiteWeightedKL_bind_marginal_decomposition_fullSupport
    (pX : PMF X)
    (encoder : X → PMF T)
    (q : PMF T)
    (hq : ∀ t : T, 0 < (q t).toReal)
    (henc : ∀ x : X, ∀ t : T, 0 < (encoder x t).toReal)
    (hnext : ∀ t : T, 0 < ((pX.bind encoder) t).toReal) :
    (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (encoder x) q).toReal)
      =
    (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (encoder x) (pX.bind encoder)).toReal)
      + (InfoGeometry.fin_kl_div (pX.bind encoder) q).toReal := by
  exact finiteWeightedKL_bind_marginal_decomposition
    (pX := pX) (encoder := encoder) (q := q)
    (hq := fun x t _ => hq t)
    (hnext := fun x t _ => hnext t)

theorem ibMarginalPythagoreanWitness_finite_supportFaithful
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T))) :
    let hKL_current :=
      finiteKLFamily_of_supportFaithful_ref
        q_n
        (IBNextEncoder q_n β D hInt)
        (IBNextEncoder_supportFaithful_ref q_n β D hInt)
    let hKL_next :=
      finiteKLFamily_of_supportFaithful_ref
        (IBNextMarginal pX q_n β D hInt h_meas)
        (IBNextEncoder q_n β D hInt)
        (IBNextEncoder_supportFaithful_nextMarginal pX q_n β D hInt h_meas)
    IBNextMarginalPythagoreanWitness pX q_n β D hInt h_meas hKL_current hKL_next := by
  intro hKL_current hKL_next
  let encoder := IBNextEncoder q_n β D hInt
  let pXpmf : PMF X := probMeasureToPMF pX
  let qpmf : PMF T := probMeasureToPMF q_n
  let encpmf : X → PMF T := fun x => probMeasureToPMF (encoder x)
  let nextpmf : PMF T := pXpmf.bind encpmf
  have hnext_eq :
      probMeasureToPMF (IBNextMarginal pX q_n β D hInt h_meas) = nextpmf := by
    simpa [encoder, pXpmf, encpmf, nextpmf] using
      (probMeasureToPMF_IBNextMarginal_eq_bind
        (pX := pX) (q_n := q_n) (β := β) (D := D)
        (hInt := hInt) (h_meas := h_meas))
  have hcurrent_expand :
      IBGlobalFreeEnergy pX q_n β D encoder hKL_current
        =
      finiteWeightedDistortion pX β D encoder
        + finiteWeightedKL pX q_n encoder := by
    simpa [encoder] using
      (IBGlobalFreeEnergy_eq_finiteWeighted
        (pX := pX) (ref := q_n) (β := β) (D := D)
        (encoder := encoder) (hKL := hKL_current))
  have hnext_expand :
      IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D encoder hKL_next
        =
      finiteWeightedDistortion pX β D encoder
        + finiteWeightedKL pX (IBNextMarginal pX q_n β D hInt h_meas) encoder := by
    simpa [encoder] using
      (IBGlobalFreeEnergy_eq_finiteWeighted
        (pX := pX)
        (ref := IBNextMarginal pX q_n β D hInt h_meas)
        (β := β) (D := D)
        (encoder := encoder) (hKL := hKL_next))
  have hkl_decomp :
      finiteWeightedKL pX q_n encoder
        =
      finiteWeightedKL pX (IBNextMarginal pX q_n β D hInt h_meas) encoder
        + (InfoGeometry.fin_kl_div nextpmf qpmf).toReal := by
    simpa [finiteWeightedKL, pXpmf, qpmf, encpmf, nextpmf, hnext_eq] using
      (finiteWeightedKL_bind_marginal_decomposition
        (pX := pXpmf)
        (encoder := encpmf)
        (q := qpmf)
        (hq := IBNextEncoder_supportFaithful_ref q_n β D hInt)
        (hnext := by
          intro x t hpos
          simpa [hnext_eq, nextpmf] using
            (IBNextEncoder_supportFaithful_nextMarginal
              (pX := pX) (q_n := q_n) (β := β) (D := D)
              (hInt := hInt) (h_meas := h_meas) x t hpos)))
  have hKL_marginal :
      klDivENN
        ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
        (q_n : Measure T) ≠ ⊤ := by
    have h :=
      klDiv_ne_top_of_supportFaithful
        (P := probMeasureToPMF (IBNextMarginal pX q_n β D hInt h_meas))
        (Q := probMeasureToPMF q_n)
        (IBNextMarginal_supportFaithful_ref
          (pX := pX) (q_n := q_n) (β := β) (D := D)
          (hInt := hInt) (h_meas := h_meas))
    rw [show ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
        = (probMeasureToPMF (IBNextMarginal pX q_n β D hInt h_meas)).toMeasure by
          simpa using
            (probMeasureToPMF_toMeasure (IBNextMarginal pX q_n β D hInt h_meas)).symm]
    rw [show (q_n : Measure T) = (probMeasureToPMF q_n).toMeasure by
          simpa using (probMeasureToPMF_toMeasure q_n).symm]
    simpa [klDivENN, InfoGeometry.KL.kl_div, InfoGeometry.fin_kl_div] using h
  have hkl_real :
      klDiv
        ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
        (q_n : Measure T)
        hKL_marginal
        =
      (InfoGeometry.fin_kl_div nextpmf qpmf).toReal := by
    simpa [hnext_eq, nextpmf, qpmf] using
      (klDiv_eq_fin_klDiv_toReal
        (ref := q_n)
        (encoder := IBNextMarginal pX q_n β D hInt h_meas)
        (hKL := hKL_marginal))
  refine ⟨hKL_marginal, ?_⟩
  rw [hnext_expand, hcurrent_expand]
  calc
    finiteWeightedDistortion pX β D encoder
      + finiteWeightedKL pX q_n encoder
      =
    finiteWeightedDistortion pX β D encoder
      + (finiteWeightedKL pX (IBNextMarginal pX q_n β D hInt h_meas) encoder
          + (InfoGeometry.fin_kl_div nextpmf qpmf).toReal) := by
        rw [hkl_decomp]
    _ =
    (finiteWeightedDistortion pX β D encoder
      + finiteWeightedKL pX (IBNextMarginal pX q_n β D hInt h_meas) encoder)
      + (InfoGeometry.fin_kl_div nextpmf qpmf).toReal := by ring
    _ =
    (finiteWeightedDistortion pX β D encoder
      + finiteWeightedKL pX (IBNextMarginal pX q_n β D hInt h_meas) encoder)
      +
    klDiv
      ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
      (q_n : Measure T)
      hKL_marginal := by
        rw [hkl_real]

theorem ibMarginalDescentWitness_finite_supportFaithful
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T))) :
    let hKL_current :=
      finiteKLFamily_of_supportFaithful_ref
        q_n
        (IBNextEncoder q_n β D hInt)
        (IBNextEncoder_supportFaithful_ref q_n β D hInt)
    let hKL_next :=
      finiteKLFamily_of_supportFaithful_ref
        (IBNextMarginal pX q_n β D hInt h_meas)
        (IBNextEncoder q_n β D hInt)
        (IBNextEncoder_supportFaithful_nextMarginal pX q_n β D hInt h_meas)
    IBNextMarginalDescentWitness pX q_n β D hInt h_meas hKL_current hKL_next := by
  intro hKL_current hKL_next
  exact IBMarginalDescentWitness.of_pythagorean
    (pX := pX)
    (q_old := q_n)
    (q_new := IBNextMarginal pX q_n β D hInt h_meas)
    (β := β) (D := D)
    (encoder := IBNextEncoder q_n β D hInt)
    (hKL_old := hKL_current)
    (hKL_new := hKL_next)
    (ibMarginalPythagoreanWitness_finite_supportFaithful
      (pX := pX) (q_n := q_n) (β := β) (D := D)
      (hInt := hInt) (h_meas := h_meas))

theorem ibMarginalDescentWitness_finite_fullSupport
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ)
    (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (hq :
      ∀ t : T, 0 < ((probMeasureToPMF q_n) t).toReal)
    (henc :
      ∀ x : X, ∀ t : T,
        0 < ((probMeasureToPMF (IBNextEncoder q_n β D hInt x)) t).toReal) :
    let hKL_current :=
      finiteKLFamily_of_positive_ref q_n (IBNextEncoder q_n β D hInt) hq
    let hnext :=
      IBNextMarginal_positive_of_encoder_positive
        (pX := pX) (q_n := q_n) (β := β) (D := D) (hInt := hInt)
        (h_meas := h_meas) henc
    let hKL_next :=
      finiteKLFamily_of_positive_ref
        (IBNextMarginal pX q_n β D hInt h_meas)
        (IBNextEncoder q_n β D hInt)
        hnext
    IBNextMarginalDescentWitness pX q_n β D hInt h_meas hKL_current hKL_next := by
  intro hKL_current hnext hKL_next
  let hKL_current' :=
    finiteKLFamily_of_supportFaithful_ref
      q_n
      (IBNextEncoder q_n β D hInt)
      (fun x t hpos => hq t)
  let hKL_next' :=
    finiteKLFamily_of_supportFaithful_ref
      (IBNextMarginal pX q_n β D hInt h_meas)
      (IBNextEncoder q_n β D hInt)
      (fun x t hpos => hnext t)
  simpa [hKL_current', hKL_next'] using
    (ibMarginalDescentWitness_finite_supportFaithful
      (pX := pX) (q_n := q_n) (β := β) (D := D)
      (hInt := hInt) (h_meas := h_meas))

end IBFinitePythagorean
