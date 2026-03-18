import InfoGeometry.Measure.Potential
set_option linter.unnecessarySimpa false

/-!
# Projective potentials and measure rays

Defines the additive-constant quotient on potentials and a positive-scaling
ray relation on measures.
-/

namespace InfoGeometry.Measure

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- Potentials are projectively equivalent if they differ by an a.e. constant. -/
def AEAddConst (ν : Measure α) (f g : α → ℝ) : Prop :=
  ∃ c : ℝ, f =ᵐ[ν] fun x => g x + c

lemma AEAddConst.refl (ν : Measure α) (f : α → ℝ) : AEAddConst ν f f :=
  ⟨0, by simp⟩

lemma AEAddConst.symm {ν : Measure α} {f g : α → ℝ} (h : AEAddConst ν f g) :
    AEAddConst ν g f := by
  rcases h with ⟨c, hfg⟩
  refine ⟨-c, ?_⟩
  filter_upwards [hfg] with x hx
  calc
    g x = (g x + c) - c := by
      symm
      simpa using (add_sub_cancel (g x) c)
    _ = f x - c := by simpa [hx]
    _ = f x + (-c) := by simp [sub_eq_add_neg]

lemma AEAddConst.trans {ν : Measure α} {f g h : α → ℝ}
    (hfg : AEAddConst ν f g) (hgh : AEAddConst ν g h) :
    AEAddConst ν f h := by
  rcases hfg with ⟨c1, hfg⟩
  rcases hgh with ⟨c2, hgh⟩
  refine ⟨c2 + c1, ?_⟩
  filter_upwards [hfg, hgh] with x hx1 hx2
  calc
    f x = g x + c1 := hx1
    _ = (h x + c2) + c1 := by simpa [hx2]
    _ = h x + (c2 + c1) := by simp [add_assoc]

def AEAddConstSetoid (ν : Measure α) : Setoid (α → ℝ) where
  r := AEAddConst ν
  iseqv := by
    refine ⟨AEAddConst.refl ν, ?_, ?_⟩
    · intro f g h; exact AEAddConst.symm h
    · intro f g h hfg hgh; exact AEAddConst.trans hfg hgh

/-- Projective potentials: quotient by additive a.e. constants. -/
abbrev ProjectivePotential (ν : Measure α) : Type _ :=
  Quotient (AEAddConstSetoid ν)

/-- Positive-scaling ray relation for measures. -/
def SameRay (μ ν : Measure α) : Prop :=
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν

lemma SameRay.refl (μ : Measure α) : SameRay μ μ := by
  refine ⟨1, one_ne_zero, ENNReal.one_ne_top, ?_⟩
  simp

lemma SameRay.symm {μ ν : Measure α} (h : SameRay μ ν) : SameRay ν μ := by
  rcases h with ⟨c, hc0, hc_top, hμν⟩
  refine ⟨c⁻¹, (ENNReal.inv_ne_zero.mpr hc_top), (ENNReal.inv_ne_top.mpr hc0), ?_⟩
  have : c⁻¹ • μ = ν := by
    calc
      c⁻¹ • μ = c⁻¹ • (c • ν) := by simp [hμν]
      _ = (c⁻¹ * c) • ν := by simp [smul_smul]
      _ = (1 : ℝ≥0∞) • ν := by simp [ENNReal.inv_mul_cancel hc0 hc_top]
      _ = ν := by simp
  simpa [this]

lemma SameRay.trans {μ ν κ : Measure α} (h₁ : SameRay μ ν) (h₂ : SameRay ν κ) :
    SameRay μ κ := by
  rcases h₁ with ⟨c₁, hc₁0, hc₁top, h₁⟩
  rcases h₂ with ⟨c₂, hc₂0, hc₂top, h₂⟩
  refine ⟨c₁ * c₂, mul_ne_zero hc₁0 hc₂0, ENNReal.mul_ne_top hc₁top hc₂top, ?_⟩
  calc
    μ = c₁ • ν := h₁
    _ = c₁ • (c₂ • κ) := by simpa [h₂]
    _ = (c₁ * c₂) • κ := by simp [smul_smul]

instance : Setoid (Measure α) where
  r := SameRay (α := α)
  iseqv := by
    refine ⟨SameRay.refl, ?_, ?_⟩
    · intro μ ν h; exact SameRay.symm h
    · intro μ ν κ hμν hνκ; exact SameRay.trans hμν hνκ

/-- Projective measure rays: quotient by positive scalings. -/
abbrev MeasureRay (α : Type*) [MeasurableSpace α] : Type _ :=
  Quotient (inferInstance : Setoid (Measure α))

section Gauge

open InfoGeometry.Measure

variable {μ ν : Measure α}
variable [IsFiniteMeasure μ] [μ.HaveLebesgueDecomposition ν]
lemma rn_potential_AEAddConst_smul_left
    (hμν : μ.AbsolutelyContinuous ν)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ⊤) :
    AEAddConst μ
      (rn_potential (μ := c • μ) (ν := ν))
      (rn_potential (μ := μ) (ν := ν)) := by
  refine ⟨-Real.log c.toReal, ?_⟩
  simpa [rn_potential, sub_eq_add_neg] using
    (rn_potential_smul_left_ae (μ := μ) (ν := ν) hμν c hc hc_ne_top)

lemma rn_potential_AEAddConst_smul_right
    (hμν : μ.AbsolutelyContinuous ν)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ⊤) :
    AEAddConst μ
      (rn_potential (μ := μ) (ν := c • ν))
      (rn_potential (μ := μ) (ν := ν)) := by
  refine ⟨Real.log c.toReal, ?_⟩
  simpa [rn_potential] using
    (rn_potential_smul_right_ae (μ := μ) (ν := ν) hμν c hc hc_ne_top)

end Gauge

end InfoGeometry.Measure
