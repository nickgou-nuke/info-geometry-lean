import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Quantitative implementation contracts

This augments (rather than redefines) the existing exact `KernelRefinement`
contract: error bounds are hypotheses to be proved for an implementation.
No tolerance test is promoted into a universal proof. Native metric and
Lipschitz APIs provide composition and observation error accounting.
-/

namespace InfoGeometry.MassSpectrometry.NumericalEvidence

/-- Uniform certified deviation from a specified map. -/
structure UniformErrorBound {Input Output : Type*} [PseudoMetricSpace Output]
    (specification implementation : Input → Output) where
  error : ℝ≥0
  bound : ∀ x, dist (implementation x) (specification x) ≤ (error : ℝ)

namespace UniformErrorBound
variable {X Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- Composition amplifies upstream error only through the specified downstream
Lipschitz constant: e₂ + L e₁. -/
def comp {f₁ g₁ : X → Y} {f₂ g₂ : Y → Z}
    (B₁ : UniformErrorBound f₁ g₁) (B₂ : UniformErrorBound f₂ g₂)
    {L : ℝ≥0} (hL : LipschitzWith L f₂) :
    UniformErrorBound (f₂ ∘ f₁) (g₂ ∘ g₁) where
  error := B₂.error + L * B₁.error
  bound x := by
    calc
      dist (g₂ (g₁ x)) (f₂ (f₁ x)) ≤
          dist (g₂ (g₁ x)) (f₂ (g₁ x)) + dist (f₂ (g₁ x)) (f₂ (f₁ x)) :=
        dist_triangle _ _ _
      _ ≤ (B₂.error : ℝ) + (L : ℝ) * (B₁.error : ℝ) := by
        exact add_le_add (B₂.bound (g₁ x))
          ((hL.dist_le_mul _ _).trans
            (mul_le_mul_of_nonneg_left (B₁.bound x) L.coe_nonneg))
      _ = ((B₂.error + L * B₁.error : ℝ≥0) : ℝ) := by simp

/-- Native metric separation turns zero error into actual function equality. -/
theorem eq_of_zero_error {Y : Type*} [MetricSpace Y] {f g : X → Y}
    (B : UniformErrorBound f g) (h : B.error = 0) : g = f := by
  funext x
  apply dist_eq_zero.mp
  have hb := B.bound x
  rw [h] at hb
  exact le_antisymm (by simpa using hb) dist_nonneg

/-- Exact function equality is the zero-error special case. -/
def of_eq {f g : X → Y} (h : g = f) : UniformErrorBound f g where
  error := 0
  bound x := by simp [h]

end UniformErrorBound

/-- Measurement, preprocessing and simulation errors are additive in a common
observation metric. Their numerical values and validity are not invented here. -/
theorem three_stage_error_budget {Y : Type*} [PseudoMetricSpace Y]
    {observed processed predicted ideal : Y} {e₁ e₂ e₃ : ℝ}
    (h₁ : dist observed processed ≤ e₁)
    (h₂ : dist processed predicted ≤ e₂)
    (h₃ : dist predicted ideal ≤ e₃) :
    dist observed ideal ≤ e₁ + e₂ + e₃ := by
  calc
    dist observed ideal ≤ dist observed predicted + dist predicted ideal :=
      dist_triangle _ _ _
    _ ≤ (dist observed processed + dist processed predicted) +
        dist predicted ideal := add_le_add_right (dist_triangle _ _ _) _
    _ ≤ e₁ + e₂ + e₃ := add_le_add (add_le_add h₁ h₂) h₃

end InfoGeometry.MassSpectrometry.NumericalEvidence
