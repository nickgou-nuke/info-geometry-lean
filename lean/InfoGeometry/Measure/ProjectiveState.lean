import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false

open scoped ENNReal

namespace InfoGeometry.MeasureProjective

open MeasureTheory

section States

variable {α : Type*} [MeasurableSpace α] [Nonempty α]

/-- Unnormalized positive states: finite measures. -/
abbrev UState (α : Type*) [MeasurableSpace α] := FiniteMeasure α

/-- Nonzero unnormalized states. -/
def NonzeroUState (α : Type*) [MeasurableSpace α] :=
  {μ : UState α // μ ≠ 0}

/-- Same projective ray iff the normalized probability measures agree. -/
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

/-- Projective states = rays in the cone of nonzero finite measures. -/
abbrev ProjectiveState (α : Type*) [MeasurableSpace α] [Nonempty α] :=
  Quotient (sameRaySetoid (α := α))

/-- Canonical normalized representative of a ray. -/
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

/-- A nonzero finite measure is its mass times its normalized slice. -/
theorem self_eq_mass_smul_normalize
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μ : UState α) :
    μ = μ.mass • μ.normalize.toFiniteMeasure :=
  MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize μ

end States

section Potentials

variable {α : Type*} [MeasurableSpace α]

/-- Logarithmic RN potential, with the sign chosen for geometric generation. -/
noncomputable def logPotential (μ ν : Measure α) : α → ℝ :=
  fun x => -MeasureTheory.llr μ ν x

/-- Gauge relation: potentials differ by an a.e. additive constant. -/
def AEAddConst (μ : Measure α) (f g : α → ℝ) : Prop :=
  ∃ c : ℝ, f =ᵐ[μ] fun x => g x + c

def aeAddConstSetoid (μ : Measure α) : Setoid (α → ℝ) where
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
      calc
        g x = (g x + c) - c := by
          symm
          simp
        _ = f x - c := by simp [hx]
        _ = f x + (-c) := by simp [sub_eq_add_neg]
    · intro f g h hfg hgh
      rcases hfg with ⟨c₁, hc₁⟩
      rcases hgh with ⟨c₂, hc₂⟩
      refine ⟨c₂ + c₁, ?_⟩
      filter_upwards [hc₁, hc₂] with x hx₁ hx₂
      calc
        f x = g x + c₁ := hx₁
        _ = (h x + c₂) + c₁ := by simp [hx₂]
        _ = h x + (c₂ + c₁) := by simp [add_assoc]

/-- Projective/gauge class of real potentials modulo AE additive constants. -/
abbrev PotentialClass (μ : Measure α) :=
  Quotient (aeAddConstSetoid μ)

/-- The logarithmic potential as a gauge class over the base measure `ν`. -/
noncomputable def logPotentialClass (μ ν : Measure α) : PotentialClass ν :=
  Quotient.mk (aeAddConstSetoid ν) (logPotential μ ν)

@[simp] theorem logPotentialClass_mk (μ ν : Measure α) :
    logPotentialClass μ ν = Quotient.mk (aeAddConstSetoid ν) (logPotential μ ν) := rfl

end Potentials

end InfoGeometry.MeasureProjective
