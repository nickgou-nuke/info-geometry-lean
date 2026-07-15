import InfoGeometry.Canonical.IBFreeEnergy
import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory

namespace IBFunctional

open IBFreeEnergy

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T] [Nonempty T]

section Global

variable (pX : ProbabilityMeasure X)
variable (qT : ProbabilityMeasure T)
variable (β : ℝ) (D : X → T → ℝ)

/-- Pointwise finiteness witness for the encoder KL term against a reference measure. -/
def FiniteKLFamily
    (ref : Measure T)
    (encoder : X → ProbabilityMeasure T) : Prop :=
  ∀ x, klDivENN (encoder x : Measure T) ref ≠ ⊤

/-- Global IB free energy obtained by integrating the local slice functional over `pX`. -/
noncomputable def IBGlobalFreeEnergy
    (encoder : X → ProbabilityMeasure T)
    (hKL : FiniteKLFamily (qT : Measure T) encoder) : ℝ :=
  ∫ x, IBLocalFreeEnergy (qT : Measure T) β D x (encoder x) (hKL x) ∂(pX : Measure X)

end Global

section Marginalization

variable (pX : ProbabilityMeasure X)
variable (encoder : X → ProbabilityMeasure T)

/-- Marginal target law obtained by binding the source law through the encoder. -/
noncomputable def bindEncoderMeasure : Measure T :=
  (pX : Measure X).bind (fun x => (encoder x : Measure T))

omit [Nonempty T] in
lemma bindEncoderMeasure_univ
    (hae : AEMeasurable (fun x => (encoder x : Measure T)) (pX : Measure X)) :
    (bindEncoderMeasure pX encoder) Set.univ = 1 := by
  unfold bindEncoderMeasure
  rw [Measure.bind_apply MeasurableSet.univ hae]
  simp

/-- Bundled probability version of the encoder marginalization step. -/
noncomputable def IBMarginalize
    (hae : AEMeasurable (fun x => (encoder x : Measure T)) (pX : Measure X)) :
    ProbabilityMeasure T :=
  ⟨bindEncoderMeasure pX encoder, by
    refine ⟨bindEncoderMeasure_univ (pX := pX) (encoder := encoder) hae⟩⟩

omit [Nonempty T] in
lemma IBMarginalize_apply
    (hae : AEMeasurable (fun x => (encoder x : Measure T)) (pX : Measure X))
    {s : Set T} (hs : MeasurableSet s) :
    (IBMarginalize pX encoder hae : Measure T) s
      = ∫⁻ x, (encoder x : Measure T) s ∂(pX : Measure X) := by
  unfold IBMarginalize bindEncoderMeasure
  exact Measure.bind_apply hs hae

omit [Nonempty T] in
lemma IBMarginalize_congr
    (hae : AEMeasurable (fun x => (encoder x : Measure T)) (pX : Measure X))
    (encoder₂ : X → ProbabilityMeasure T)
    (hae₂ : AEMeasurable (fun x => (encoder₂ x : Measure T)) (pX : Measure X))
    (h_ae :
      (fun x => (encoder x : Measure T)) =ᵐ[(pX : Measure X)]
        (fun x => (encoder₂ x : Measure T))) :
    (IBMarginalize pX encoder hae : Measure T)
      = (IBMarginalize pX encoder₂ hae₂ : Measure T) := by
  unfold IBMarginalize bindEncoderMeasure
  exact Measure.bind_congr_right h_ae

end Marginalization

end IBFunctional
