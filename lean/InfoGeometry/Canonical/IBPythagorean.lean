import InfoGeometry.Canonical.IBIteration
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory
open ProbabilityTheory

namespace InfoGeometry.Canonical.IBPythagorean

open IBFreeEnergy
open IBFunctional
open IBIteration

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T] [Nonempty T]

/-- The Gibbs encoder induced by the current target marginal. -/
noncomputable abbrev IBNextEncoder
    (q_n : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T)) :
    X → ProbabilityMeasure T :=
  globalGibbsEncoder q_n β D hInt

/-- The next target marginal produced by one BA update. -/
noncomputable abbrev IBNextMarginal
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T))) :
    ProbabilityMeasure T :=
  IBStep pX q_n β D hInt h_meas

/-- Kernel promotion of a measurable probability-valued encoder. -/
noncomputable def encoderKernel
    (encoder : X → ProbabilityMeasure T)
    (h_meas : Measurable (fun x => (encoder x : Measure T))) :
    Kernel X T where
  toFun := fun x => (encoder x : Measure T)
  measurable' := h_meas

instance encoderKernel_isMarkovKernel
    (encoder : X → ProbabilityMeasure T)
    (h_meas : Measurable (fun x => (encoder x : Measure T))) :
    IsMarkovKernel (encoderKernel encoder h_meas) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure (((encoder x : ProbabilityMeasure T) : Measure T))
    infer_instance

omit [Nonempty T] in
lemma IBMarginalize_eq_encoderKernel_comp
    (pX : ProbabilityMeasure X)
    (encoder : X → ProbabilityMeasure T)
    (h_meas : Measurable (fun x => (encoder x : Measure T))) :
    (IBMarginalize pX encoder h_meas.aemeasurable : Measure T)
      =
    (encoderKernel encoder h_meas) ∘ₘ (pX : Measure X) := by
  ext s hs
  rw [IBMarginalize_apply (pX := pX) (encoder := encoder) (hae := h_meas.aemeasurable) hs]
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  rfl

omit [Nonempty T] in
private lemma llr_chain_rule
    (p q_mid q_ref : ProbabilityMeasure T)
    (hp : (p : Measure T) ≪ (q_mid : Measure T))
    (hq : (q_mid : Measure T) ≪ (q_ref : Measure T)) :
    MeasureTheory.llr (p : Measure T) (q_ref : Measure T)
      =ᵐ[(p : Measure T)]
    fun t =>
      MeasureTheory.llr (p : Measure T) (q_mid : Measure T) t
        + MeasureTheory.llr (q_mid : Measure T) (q_ref : Measure T) t := by
  filter_upwards
      [hp.ae_le (Measure.rnDeriv_mul_rnDeriv'
          (μ := (p : Measure T))
          (ν := (q_mid : Measure T))
          (κ := (q_ref : Measure T))
          hq),
       Measure.rnDeriv_pos hp,
       hp.ae_le (Measure.rnDeriv_pos hq),
       hp.ae_le (Measure.rnDeriv_lt_top (p : Measure T) (q_mid : Measure T)),
       (hp.trans hq).ae_le (Measure.rnDeriv_lt_top (q_mid : Measure T) (q_ref : Measure T))] with
    t hmul hp_pos hq_pos hp_lt_top hq_lt_top
  rw [MeasureTheory.llr, MeasureTheory.llr, MeasureTheory.llr, ← hmul, Pi.mul_apply,
    ENNReal.toReal_mul]
  · rw [Real.log_mul]
    · exact ENNReal.toReal_ne_zero.mpr ⟨hp_pos.ne', hp_lt_top.ne⟩
    · exact ENNReal.toReal_ne_zero.mpr ⟨hq_pos.ne', hq_lt_top.ne⟩

omit [Nonempty T] in
private lemma klDiv_eq_klDiv_add_integral_llr
    (p q_new q_old : ProbabilityMeasure T)
    (hKL_old : klDivENN (p : Measure T) (q_old : Measure T) ≠ ⊤)
    (hKL_new : klDivENN (p : Measure T) (q_new : Measure T) ≠ ⊤)
    (hKL_marginal : klDivENN (q_new : Measure T) (q_old : Measure T) ≠ ⊤) :
    klDiv (p : Measure T) (q_old : Measure T) hKL_old
      =
    klDiv (p : Measure T) (q_new : Measure T) hKL_new
      + ∫ t, MeasureTheory.llr (q_new : Measure T) (q_old : Measure T) t ∂(p : Measure T) := by
  have h_old_ne_top :
      InformationTheory.klDiv (p : Measure T) (q_old : Measure T) ≠ ⊤ := by
    simpa [klDivENN, InfoGeometry.KL.kl_div] using hKL_old
  have h_new_ne_top :
      InformationTheory.klDiv (p : Measure T) (q_new : Measure T) ≠ ⊤ := by
    simpa [klDivENN, InfoGeometry.KL.kl_div] using hKL_new
  have h_marginal_ne_top :
      InformationTheory.klDiv (q_new : Measure T) (q_old : Measure T) ≠ ⊤ := by
    simpa [klDivENN, InfoGeometry.KL.kl_div] using hKL_marginal
  have hp_old :
      (p : Measure T) ≪ (q_old : Measure T) :=
    (InformationTheory.klDiv_ne_top_iff.mp h_old_ne_top).1
  have hp_new :
      (p : Measure T) ≪ (q_new : Measure T) :=
    (InformationTheory.klDiv_ne_top_iff.mp h_new_ne_top).1
  have hq :
      (q_new : Measure T) ≪ (q_old : Measure T) :=
    (InformationTheory.klDiv_ne_top_iff.mp h_marginal_ne_top).1
  have h_int_old :
      Integrable (MeasureTheory.llr (p : Measure T) (q_old : Measure T)) (p : Measure T) :=
    (InformationTheory.klDiv_ne_top_iff.mp h_old_ne_top).2
  have h_int_new :
      Integrable (MeasureTheory.llr (p : Measure T) (q_new : Measure T)) (p : Measure T) :=
    (InformationTheory.klDiv_ne_top_iff.mp h_new_ne_top).2
  have hllr :=
    llr_chain_rule (p := p) (q_mid := q_new) (q_ref := q_old) hp_new hq
  have hdiff :
      (fun t => MeasureTheory.llr (q_new : Measure T) (q_old : Measure T) t)
        =ᵐ[(p : Measure T)]
      fun t =>
        MeasureTheory.llr (p : Measure T) (q_old : Measure T) t
          - MeasureTheory.llr (p : Measure T) (q_new : Measure T) t := by
    filter_upwards [hllr] with t ht
    linarith
  have h_int_shift :
      Integrable (fun t => MeasureTheory.llr (q_new : Measure T) (q_old : Measure T) t)
        (p : Measure T) := by
    rw [integrable_congr hdiff]
    exact h_int_old.sub h_int_new
  calc
    klDiv (p : Measure T) (q_old : Measure T) hKL_old
      = ∫ t, MeasureTheory.llr (p : Measure T) (q_old : Measure T) t ∂(p : Measure T) := by
          simpa [klDiv, klDivENN, InfoGeometry.KL.kl_div] using
            (InformationTheory.toReal_klDiv_of_measure_eq
              (μ := (p : Measure T))
              (ν := (q_old : Measure T))
              hp_old
              (by simp))
    _ =
      ∫ t,
        (MeasureTheory.llr (p : Measure T) (q_new : Measure T) t
          + MeasureTheory.llr (q_new : Measure T) (q_old : Measure T) t) ∂(p : Measure T) := by
            refine integral_congr_ae hllr
    _ =
      (∫ t, MeasureTheory.llr (p : Measure T) (q_new : Measure T) t ∂(p : Measure T))
        +
      (∫ t, MeasureTheory.llr (q_new : Measure T) (q_old : Measure T) t ∂(p : Measure T)) := by
            rw [integral_add h_int_new h_int_shift]
    _ =
      klDiv (p : Measure T) (q_new : Measure T) hKL_new
        + ∫ t, MeasureTheory.llr (q_new : Measure T) (q_old : Measure T) t ∂(p : Measure T) := by
            congr 1
            symm
            simpa [klDiv, klDivENN, InfoGeometry.KL.kl_div] using
              (InformationTheory.toReal_klDiv_of_measure_eq
                (μ := (p : Measure T))
                (ν := (q_new : Measure T))
                hp_new
                (by simp))

omit [MeasurableSpace X] [Nonempty T] in
private lemma IBLocalFreeEnergy_eq_add_marginal_llr
    (q_old q_new : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ) (x : X)
    (p : ProbabilityMeasure T)
    (hKL_old : klDivENN (p : Measure T) (q_old : Measure T) ≠ ⊤)
    (hKL_new : klDivENN (p : Measure T) (q_new : Measure T) ≠ ⊤)
    (hKL_marginal : klDivENN (q_new : Measure T) (q_old : Measure T) ≠ ⊤) :
    IBLocalFreeEnergy (q_old : Measure T) β D x p hKL_old
      =
    IBLocalFreeEnergy (q_new : Measure T) β D x p hKL_new
      + ∫ t, MeasureTheory.llr (q_new : Measure T) (q_old : Measure T) t ∂(p : Measure T) := by
  unfold IBLocalFreeEnergy
  rw [klDiv_eq_klDiv_add_integral_llr
    (p := p) (q_new := q_new) (q_old := q_old)
    (hKL_old := hKL_old) (hKL_new := hKL_new) (hKL_marginal := hKL_marginal)]
  ring

/--
Analytic witness for the KL/Pythagorean marginal-descent step at fixed encoder.

This isolates the genuine measure-theoretic content away from the purely algebraic
composition theorem in `IBMonotonicity`.
-/
structure IBMarginalPythagoreanWitness
    (pX : ProbabilityMeasure X)
    (q_old q_new : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (encoder : X → ProbabilityMeasure T)
    (hKL_old : FiniteKLFamily (q_old : Measure T) encoder)
    (hKL_new : FiniteKLFamily (q_new : Measure T) encoder) : Prop where
  hKL_marginal : klDivENN (q_new : Measure T) (q_old : Measure T) ≠ ⊤
  decomposition :
    IBGlobalFreeEnergy pX q_old β D encoder hKL_old
      =
    IBGlobalFreeEnergy pX q_new β D encoder hKL_new
      + klDiv (q_new : Measure T) (q_old : Measure T) hKL_marginal

/--
Analytic witness for the KL/Pythagorean marginal-descent step at fixed encoder.

This is the inequality-level corollary of the exact Pythagorean decomposition.
-/
structure IBMarginalDescentWitness
    (pX : ProbabilityMeasure X)
    (q_old q_new : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (encoder : X → ProbabilityMeasure T)
    (hKL_old : FiniteKLFamily (q_old : Measure T) encoder)
    (hKL_new : FiniteKLFamily (q_new : Measure T) encoder) : Prop where
  descent :
    IBGlobalFreeEnergy pX q_new β D encoder hKL_new
      ≤
    IBGlobalFreeEnergy pX q_old β D encoder hKL_old

omit [Nonempty T] in
theorem ibMarginalPythagorean_identity_of_marginalization
    (pX : ProbabilityMeasure X)
    (q_old : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (encoder : X → ProbabilityMeasure T)
    (h_meas : Measurable (fun x => (encoder x : Measure T)))
    (hKL_old : FiniteKLFamily (q_old : Measure T) encoder)
    (hKL_new :
      FiniteKLFamily
        ((IBMarginalize pX encoder h_meas.aemeasurable : ProbabilityMeasure T) : Measure T)
        encoder)
    (hKL_marginal :
      klDivENN
        ((IBMarginalize pX encoder h_meas.aemeasurable : ProbabilityMeasure T) : Measure T)
        (q_old : Measure T) ≠ ⊤)
    (h_local_new :
      Integrable
        (fun x =>
          IBLocalFreeEnergy
            ((IBMarginalize pX encoder h_meas.aemeasurable : ProbabilityMeasure T) : Measure T)
            β D x (encoder x) (hKL_new x))
        (pX : Measure X)) :
    IBGlobalFreeEnergy pX q_old β D encoder hKL_old
      =
    IBGlobalFreeEnergy
        pX
        (IBMarginalize pX encoder h_meas.aemeasurable)
        β D
        encoder
        hKL_new
      +
    klDiv
      (((IBMarginalize pX encoder h_meas.aemeasurable : ProbabilityMeasure T) : Measure T))
      (q_old : Measure T)
      hKL_marginal := by
  let q_new : ProbabilityMeasure T := IBMarginalize pX encoder h_meas.aemeasurable
  let f : T → ℝ := fun t => MeasureTheory.llr (q_new : Measure T) (q_old : Measure T) t
  have h_local :
      ∀ x,
        IBLocalFreeEnergy (q_old : Measure T) β D x (encoder x) (hKL_old x)
          =
        IBLocalFreeEnergy (q_new : Measure T) β D x (encoder x) (hKL_new x)
          + ∫ t, f t ∂(encoder x : Measure T) := by
    intro x
    simpa [q_new, f] using
      (IBLocalFreeEnergy_eq_add_marginal_llr
        (q_old := q_old)
        (q_new := q_new)
        (β := β) (D := D) (x := x)
        (p := encoder x)
        (hKL_old := hKL_old x)
        (hKL_new := hKL_new x)
        (hKL_marginal := hKL_marginal))
  have h_marginal_ne_top :
      InformationTheory.klDiv (q_new : Measure T) (q_old : Measure T) ≠ ⊤ := by
    simpa [q_new, klDivENN, InfoGeometry.KL.kl_div] using hKL_marginal
  have h_marginal_ac :
      (q_new : Measure T) ≪ (q_old : Measure T) :=
    (InformationTheory.klDiv_ne_top_iff.mp h_marginal_ne_top).1
  have h_marginal_int :
      Integrable f (q_new : Measure T) := by
    simpa [q_new, f] using
      (InformationTheory.klDiv_ne_top_iff.mp h_marginal_ne_top).2
  have h_comp :
      ((encoderKernel encoder h_meas) ∘ₖ Kernel.const Unit (pX : Measure X)) ()
        = (q_new : Measure T) := by
    calc
      ((encoderKernel encoder h_meas) ∘ₖ Kernel.const Unit (pX : Measure X)) ()
        = (encoderKernel encoder h_meas) ∘ₘ (pX : Measure X) := by
            symm
            exact Measure.comp_eq_comp_const_apply
      _ = (q_new : Measure T) := by
            simpa [q_new] using
              (IBMarginalize_eq_encoderKernel_comp
                (pX := pX) (encoder := encoder) (h_meas := h_meas)).symm
  have h_comp_int :
      Integrable f (((encoderKernel encoder h_meas) ∘ₖ Kernel.const Unit (pX : Measure X)) ()) := by
    simpa [h_comp] using h_marginal_int
  have h_shift_int :
      Integrable (fun x => ∫ t, f t ∂(encoder x : Measure T)) (pX : Measure X) := by
    simpa [encoderKernel] using h_comp_int.integral_comp
  have h_avg :
      ∫ x, ∫ t, f t ∂(encoder x : Measure T) ∂(pX : Measure X)
        =
      ∫ t, f t ∂(q_new : Measure T) := by
    calc
      ∫ x, ∫ t, f t ∂(encoder x : Measure T) ∂(pX : Measure X)
        =
      ∫ x, ∫ t, f t ∂(encoderKernel encoder h_meas x) ∂(Kernel.const Unit (pX : Measure X) ()) := by
          simp [encoderKernel]
      _ =
      ∫ t, f t ∂(((encoderKernel encoder h_meas) ∘ₖ Kernel.const Unit (pX : Measure X)) ()) := by
          symm
          exact Kernel.integral_comp
            (a := ())
            (κ := Kernel.const Unit (pX : Measure X))
            (η := encoderKernel encoder h_meas)
            h_comp_int
      _ = ∫ t, f t ∂(q_new : Measure T) := by
          rw [h_comp]
  have h_kl_real :
      ∫ t, f t ∂(q_new : Measure T)
        =
      klDiv (q_new : Measure T) (q_old : Measure T) hKL_marginal := by
    symm
    simpa [q_new, f, klDiv, klDivENN, InfoGeometry.KL.kl_div] using
      (InformationTheory.toReal_klDiv_of_measure_eq
        (μ := (q_new : Measure T))
        (ν := (q_old : Measure T))
        h_marginal_ac
        (by simp))
  calc
    IBGlobalFreeEnergy pX q_old β D encoder hKL_old
      =
    ∫ x,
      (IBLocalFreeEnergy (q_new : Measure T) β D x (encoder x) (hKL_new x)
        + ∫ t, f t ∂(encoder x : Measure T)) ∂(pX : Measure X) := by
          unfold IBGlobalFreeEnergy
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall h_local
    _ =
    (∫ x, IBLocalFreeEnergy (q_new : Measure T) β D x (encoder x) (hKL_new x) ∂(pX : Measure X))
      + ∫ x, ∫ t, f t ∂(encoder x : Measure T) ∂(pX : Measure X) := by
          rw [integral_add h_local_new h_shift_int]
    _ =
    IBGlobalFreeEnergy pX q_new β D encoder hKL_new
      + ∫ x, ∫ t, f t ∂(encoder x : Measure T) ∂(pX : Measure X) := by
          rfl
    _ =
    IBGlobalFreeEnergy pX q_new β D encoder hKL_new
      + ∫ t, f t ∂(q_new : Measure T) := by
          rw [h_avg]
    _ =
    IBGlobalFreeEnergy pX q_new β D encoder hKL_new
      + klDiv (q_new : Measure T) (q_old : Measure T) hKL_marginal := by
          rw [h_kl_real]

omit [Nonempty T] in
theorem ibMarginalPythagoreanWitness_of_marginalization
    (pX : ProbabilityMeasure X)
    (q_old : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (encoder : X → ProbabilityMeasure T)
    (h_meas : Measurable (fun x => (encoder x : Measure T)))
    (hKL_old : FiniteKLFamily (q_old : Measure T) encoder)
    (hKL_new :
      FiniteKLFamily
        ((IBMarginalize pX encoder h_meas.aemeasurable : ProbabilityMeasure T) : Measure T)
        encoder)
    (hKL_marginal :
      klDivENN
        ((IBMarginalize pX encoder h_meas.aemeasurable : ProbabilityMeasure T) : Measure T)
        (q_old : Measure T) ≠ ⊤)
    (h_local_new :
      Integrable
        (fun x =>
          IBLocalFreeEnergy
            ((IBMarginalize pX encoder h_meas.aemeasurable : ProbabilityMeasure T) : Measure T)
            β D x (encoder x) (hKL_new x))
        (pX : Measure X)) :
    IBMarginalPythagoreanWitness
      pX
      q_old
      (IBMarginalize pX encoder h_meas.aemeasurable)
      β D
      encoder
      hKL_old
      hKL_new := by
  refine ⟨hKL_marginal, ?_⟩
  exact ibMarginalPythagorean_identity_of_marginalization
    (pX := pX)
    (q_old := q_old)
    (β := β)
    (D := D)
    (encoder := encoder)
    (h_meas := h_meas)
    (hKL_old := hKL_old)
    (hKL_new := hKL_new)
    (hKL_marginal := hKL_marginal)
    (h_local_new := h_local_new)

theorem ibNextMarginalPythagoreanWitness_of_marginalization
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (hKL_current : FiniteKLFamily (q_n : Measure T) (IBNextEncoder q_n β D hInt))
    (hKL_next :
      FiniteKLFamily
        ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
        (IBNextEncoder q_n β D hInt))
    (hKL_marginal :
      klDivENN
        ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
        (q_n : Measure T) ≠ ⊤)
    (h_local_next :
      Integrable
        (fun x =>
          IBLocalFreeEnergy
            ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
            β D x
            (IBNextEncoder q_n β D hInt x)
            (hKL_next x))
        (pX : Measure X)) :
    IBMarginalPythagoreanWitness
      pX q_n (IBNextMarginal pX q_n β D hInt h_meas)
      β D (IBNextEncoder q_n β D hInt) hKL_current hKL_next := by
  simpa [IBNextEncoder, IBNextMarginal] using
    (ibMarginalPythagoreanWitness_of_marginalization
      (pX := pX)
      (q_old := q_n)
      (β := β)
      (D := D)
      (encoder := IBNextEncoder q_n β D hInt)
      (h_meas := h_meas)
      (hKL_old := hKL_current)
      (hKL_new := hKL_next)
      (hKL_marginal := hKL_marginal)
      (h_local_new := h_local_next))

omit [Nonempty T] in
theorem IBMarginalDescentWitness.of_pythagorean
    (pX : ProbabilityMeasure X)
    (q_old q_new : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (encoder : X → ProbabilityMeasure T)
    (hKL_old : FiniteKLFamily (q_old : Measure T) encoder)
    (hKL_new : FiniteKLFamily (q_new : Measure T) encoder)
    (h :
      IBMarginalPythagoreanWitness
        pX q_old q_new β D encoder hKL_old hKL_new) :
    IBMarginalDescentWitness pX q_old q_new β D encoder hKL_old hKL_new := by
  refine ⟨?_⟩
  rw [h.decomposition]
  exact le_add_of_nonneg_right
    (klDiv_nonneg (q_new : Measure T) (q_old : Measure T) h.hKL_marginal)

omit [Nonempty T] in
theorem IB_marginal_descent_from_witness
    (pX : ProbabilityMeasure X)
    (q_old q_new : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (encoder : X → ProbabilityMeasure T)
    (hKL_old : FiniteKLFamily (q_old : Measure T) encoder)
    (hKL_new : FiniteKLFamily (q_new : Measure T) encoder)
    (h : IBMarginalDescentWitness pX q_old q_new β D encoder hKL_old hKL_new) :
    IBGlobalFreeEnergy pX q_new β D encoder hKL_new
      ≤
    IBGlobalFreeEnergy pX q_old β D encoder hKL_old :=
  h.descent

omit [Nonempty T] in
theorem IB_marginal_descent_of_pythagorean
    (pX : ProbabilityMeasure X)
    (q_old q_new : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (encoder : X → ProbabilityMeasure T)
    (hKL_old : FiniteKLFamily (q_old : Measure T) encoder)
    (hKL_new : FiniteKLFamily (q_new : Measure T) encoder)
    (h :
      IBMarginalPythagoreanWitness
        pX q_old q_new β D encoder hKL_old hKL_new) :
    IBGlobalFreeEnergy pX q_new β D encoder hKL_new
      ≤
    IBGlobalFreeEnergy pX q_old β D encoder hKL_old :=
  (IBMarginalDescentWitness.of_pythagorean
    (pX := pX) (q_old := q_old) (q_new := q_new)
    (β := β) (D := D) (encoder := encoder)
    (hKL_old := hKL_old) (hKL_new := hKL_new) h).descent

theorem IB_next_marginal_descent_from_witness
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (hKL_current : FiniteKLFamily (q_n : Measure T) (IBNextEncoder q_n β D hInt))
    (hKL_next :
      FiniteKLFamily
        ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
        (IBNextEncoder q_n β D hInt))
    (h :
      IBMarginalDescentWitness
        pX q_n (IBNextMarginal pX q_n β D hInt h_meas)
        β D (IBNextEncoder q_n β D hInt) hKL_current hKL_next) :
    IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D
      (IBNextEncoder q_n β D hInt) hKL_next
      ≤
    IBGlobalFreeEnergy pX q_n β D
      (IBNextEncoder q_n β D hInt) hKL_current :=
  h.descent

theorem IB_next_marginal_descent_of_pythagorean
    (pX : ProbabilityMeasure X)
    (q_n : ProbabilityMeasure T)
    (β : ℝ) (D : X → T → ℝ)
    (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (q_n : Measure T))
    (h_meas : Measurable (fun x => (IBNextEncoder q_n β D hInt x : Measure T)))
    (hKL_current : FiniteKLFamily (q_n : Measure T) (IBNextEncoder q_n β D hInt))
    (hKL_next :
      FiniteKLFamily
        ((IBNextMarginal pX q_n β D hInt h_meas : ProbabilityMeasure T) : Measure T)
        (IBNextEncoder q_n β D hInt))
    (h :
      IBMarginalPythagoreanWitness pX q_n (IBNextMarginal pX q_n β D hInt h_meas) β D (IBNextEncoder q_n β D hInt) hKL_current hKL_next) :
    IBGlobalFreeEnergy pX (IBNextMarginal pX q_n β D hInt h_meas) β D
      (IBNextEncoder q_n β D hInt) hKL_next
      ≤
    IBGlobalFreeEnergy pX q_n β D
      (IBNextEncoder q_n β D hInt) hKL_current :=
  (IBMarginalDescentWitness.of_pythagorean
    (pX := pX)
    (q_old := q_n)
    (q_new := IBNextMarginal pX q_n β D hInt h_meas)
    (β := β) (D := D)
    (encoder := IBNextEncoder q_n β D hInt)
    (hKL_old := hKL_current) (hKL_new := hKL_next) h).descent

end InfoGeometry.Canonical.IBPythagorean
