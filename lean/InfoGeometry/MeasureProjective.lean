import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
open scoped ENNReal

namespace MeasureProjective

open MeasureTheory

section States

variable {α : Type*} [MeasurableSpace α] [Nonempty α]

abbrev UState (α : Type*) [MeasurableSpace α] := FiniteMeasure α

def NonzeroUState (α : Type*) [MeasurableSpace α] :=
  { μ : UState α // μ ≠ 0 }

def SameRay {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μ ν : NonzeroUState α) : Prop :=
  μ.1.normalize = ν.1.normalize

instance sameRaySetoid {α : Type*} [MeasurableSpace α] [Nonempty α] :
    Setoid (NonzeroUState α) where
  r := SameRay
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro μ; rfl
    · intro μ ν h; exact h.symm
    · intro μ ν κ hμν hνκ; exact hμν.trans hνκ

abbrev ProjectiveState (α : Type*) [MeasurableSpace α] [Nonempty α] :=
  Quotient (sameRaySetoid (α := α))

noncomputable def ProjectiveState.normalize
    {α : Type*} [MeasurableSpace α] [Nonempty α] :
    ProjectiveState α → ProbabilityMeasure α :=
  Quotient.lift
    (fun μ : NonzeroUState α => μ.1.normalize)
    (by
      intro μ ν h
      exact h)

@[simp] theorem ProjectiveState.normalize_mk
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μ : NonzeroUState α) :
    ProjectiveState.normalize (Quotient.mk (sameRaySetoid (α := α)) μ) = μ.1.normalize := rfl

theorem self_eq_mass_smul_normalize
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μ : UState α) :
    μ = μ.mass • μ.normalize.toFiniteMeasure :=
  MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize μ

end States

section Potentials

variable {α : Type*} [MeasurableSpace α]

noncomputable def logPotential (μ ν : Measure α) : α → ℝ :=
  fun x => -MeasureTheory.llr μ ν x

@[simp] theorem logPotential_eq_neg_llr (μ ν : Measure α) (x : α) :
    logPotential μ ν x = -MeasureTheory.llr μ ν x :=
  rfl

/-- Gauge relation modulo additive constants, with respect to a fixed base measure. -/
def AEAddConst (μ : Measure α) (f g : α → ℝ) : Prop :=
  ∃ c : ℝ, f =ᶠ[ae μ] fun x => g x + c

instance aeAddConstSetoid (μ : Measure α) : Setoid (α → ℝ) where
  r := AEAddConst μ
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro f
      refine ⟨0, ?_⟩
      filter_upwards with x
      simp
    · intro f g h
      rcases h with ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      filter_upwards [hc] with x hx
      linarith
    · intro f g h hfg hgh
      rcases hfg with ⟨c₁, hc₁⟩
      rcases hgh with ⟨c₂, hc₂⟩
      refine ⟨c₁ + c₂, ?_⟩
      filter_upwards [hc₁, hc₂] with x hx₁ hx₂
      linarith

abbrev PotentialClass (μ : Measure α) :=
  Quotient (aeAddConstSetoid μ)

noncomputable def logPotentialClass (μ ν : Measure α) : PotentialClass ν :=
  Quotient.mk (aeAddConstSetoid ν) (logPotential μ ν)

@[simp] theorem logPotentialClass_mk
    (μ ν : Measure α) :
    logPotentialClass μ ν =
      Quotient.mk (aeAddConstSetoid ν) (logPotential μ ν) := rfl

end Potentials

section SourceGaugeLaws

variable {α : Type*} [MeasurableSpace α]
variable {μ ν : Measure α}
variable [IsFiniteMeasure μ] [μ.HaveLebesgueDecomposition ν]

/--
This is the correct gauge law for left scaling: the additive constant is only
available `μ`-a.e., because that is exactly the domain of `llr_smul_left`.
-/
lemma logPotential_smul_left_ae
    (hμν : μ.AbsolutelyContinuous ν)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ⊤) :
    AEAddConst μ (logPotential (c • μ) ν) (logPotential μ ν) := by
  refine ⟨-Real.log c.toReal, ?_⟩
  filter_upwards [MeasureTheory.llr_smul_left hμν c hc hc_ne_top] with x hx
  have hx' := congrArg (fun t : ℝ => -t) hx
  simpa [logPotential, sub_eq_add_neg, add_comm] using hx'

/--
Likewise for right scaling: the natural statement is again `μ`-a.e.
-/
lemma logPotential_smul_right_ae
    (hμν : μ.AbsolutelyContinuous ν)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ⊤) :
    AEAddConst μ (logPotential μ (c • ν)) (logPotential μ ν) := by
  refine ⟨Real.log c.toReal, ?_⟩
  filter_upwards [MeasureTheory.llr_smul_right hμν c hc hc_ne_top] with x hx
  have hx' := congrArg (fun t : ℝ => -t) hx
  simpa [logPotential, sub_eq_add_neg, add_comm] using hx'

end SourceGaugeLaws

section Descend

variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/--
The logarithmic RN generator between projective states is defined by passing to
their canonical normalized representatives.
-/
noncomputable def ProjectiveState.logGenerator
    (base ξ : ProjectiveState α) : α → ℝ :=
  logPotential
    (((ProjectiveState.normalize ξ : ProbabilityMeasure α) : Measure α))
    (((ProjectiveState.normalize base : ProbabilityMeasure α) : Measure α))

/--
The descended generator, viewed as a gauge class over the normalized base ray.
-/
noncomputable def ProjectiveState.logGeneratorClass
    (base ξ : ProjectiveState α) :
    PotentialClass (((ProjectiveState.normalize base : ProbabilityMeasure α) : Measure α)) :=
  Quotient.mk
    (aeAddConstSetoid (((ProjectiveState.normalize base : ProbabilityMeasure α) : Measure α)))
    (ProjectiveState.logGenerator base ξ)

@[simp] theorem ProjectiveState.logGenerator_mk
    (base ξ : NonzeroUState α) :
    ProjectiveState.logGenerator
        (Quotient.mk (sameRaySetoid (α := α)) base)
        (Quotient.mk (sameRaySetoid (α := α)) ξ)
      =
      logPotential
        (((ξ.1.normalize : ProbabilityMeasure α) : Measure α))
        (((base.1.normalize : ProbabilityMeasure α) : Measure α)) := rfl

@[simp] theorem ProjectiveState.logGenerator_self
    (ξ : ProjectiveState α) :
    ProjectiveState.logGenerator ξ ξ
      =ᶠ[ae (((ProjectiveState.normalize ξ : ProbabilityMeasure α) : Measure α))] 0 := by
  have h := MeasureTheory.llr_self
        (((ProjectiveState.normalize ξ : ProbabilityMeasure α) : Measure α))
  filter_upwards [h] with x hx
  simp only [ProjectiveState.logGenerator, logPotential, hx, Pi.zero_apply, neg_zero]

end Descend

end MeasureProjective
