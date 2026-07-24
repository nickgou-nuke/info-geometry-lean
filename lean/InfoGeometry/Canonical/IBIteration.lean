import InfoGeometry.Canonical.IBFunctional
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.CompNotation
set_option linter.unusedSectionVars false

open MeasureTheory
open ProbabilityTheory

namespace InfoGeometry.Canonical.IBIteration

open IBFunctional
open IBMeasure

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T] [Nonempty T]

section Step

variable (pX : ProbabilityMeasure X)
variable (qT : ProbabilityMeasure T)
variable (β : ℝ) (D : X → T → ℝ)
variable (hInt : ∀ x, Integrable (fun t => Real.exp (-β * D x t)) (qT : Measure T))

/-- Slice-wise Gibbs encoder for a fixed target marginal `qT`. -/
noncomputable def globalGibbsEncoder : X → ProbabilityMeasure T :=
  fun x => IBGibbsProb (qT := (qT : Measure T)) β D x <| by
    simpa [distortionRV, mul_comm, mul_left_comm, mul_assoc] using hInt x

variable (h_meas : Measurable (fun x => (globalGibbsEncoder qT β D hInt x : Measure T)))

/-- Canonical Markov-kernel promotion of the Gibbs encoder. -/
noncomputable def IBKernel : Kernel X T where
  toFun := fun x => (globalGibbsEncoder qT β D hInt x : Measure T)
  measurable' := h_meas

instance IBKernel_isMarkovKernel : IsMarkovKernel (IBKernel qT β D hInt h_meas) where
  isProbabilityMeasure x := by
    simpa [IBKernel, globalGibbsEncoder] using
      (show IsProbabilityMeasure
        (((IBGibbsProb (qT := (qT : Measure T)) β D x
            (by simpa [distortionRV, mul_comm, mul_left_comm, mul_assoc] using hInt x)
            : ProbabilityMeasure T) : Measure T)) by
        infer_instance)

/-- Raw BA marginal update written on the measure layer via `Measure.bind`. -/
noncomputable def IBStepMeasure : Measure T :=
  Measure.bind (pX : Measure X) (fun x => (globalGibbsEncoder qT β D hInt x : Measure T))

theorem IBStepMeasure_isProbabilityMeasure
    (h_meas : Measurable (fun x => (globalGibbsEncoder qT β D hInt x : Measure T))) :
    IsProbabilityMeasure (IBStepMeasure pX qT β D hInt) := by
  unfold IBStepMeasure
  refine MeasureTheory.isProbabilityMeasure_bind (Measurable.aemeasurable h_meas) ?_
  exact Filter.Eventually.of_forall (fun x => by
    infer_instance)

/-- One Blahut-Arimoto marginal update induced by the Gibbs encoder. -/
noncomputable def IBStep : ProbabilityMeasure T :=
  ⟨IBStepMeasure pX qT β D hInt, IBStepMeasure_isProbabilityMeasure pX qT β D hInt h_meas⟩

lemma IBStep_apply {s : Set T} (hs : MeasurableSet s) :
    (IBStep pX qT β D hInt h_meas : Measure T) s
      = ∫⁻ x, (globalGibbsEncoder qT β D hInt x : Measure T) s ∂(pX : Measure X) := by
  simpa [IBStep, IBStepMeasure] using
    (Measure.bind_apply
      (m := (pX : Measure X))
      (s := s)
      (hs := hs)
      (hf := Measurable.aemeasurable h_meas))

lemma IBStepMeasure_eq_comp :
    IBStepMeasure pX qT β D hInt = (IBKernel qT β D hInt h_meas) ∘ₘ (pX : Measure X) := by
  rfl

end Step

end InfoGeometry.Canonical.IBIteration
