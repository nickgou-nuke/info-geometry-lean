import Mathlib

/-!
# Conditional metric compatibility for a soldered two-leg frame

This owner is deliberately limited to the checked Hilbert-space statement.
It does not identify the Hilbert inner product with the abstract
`KaehlerInformationGeometry.H.metric`, nor does it construct a differential
spin connection on a manifold.
-/

namespace InfoGeometry.Canonical

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Covariant derivative of the positive frame leg in the two-leg model. -/
def covariantDerivativePlus
    (ePlus eMinus : E) (dePlus : E →L[ℝ] E)
    (omega : E →L[ℝ] ℝ) (v : E) : E :=
  dePlus v + (omega v) • eMinus

/-- Covariant derivative of the negative frame leg in the two-leg model. -/
def covariantDerivativeMinus
    (ePlus eMinus : E) (deMinus : E →L[ℝ] E)
    (omega : E →L[ℝ] ℝ) (v : E) : E :=
  deMinus v + (omega v) • ePlus

theorem soldered_metric_compatibility
    (ePlus eMinus : E) (dePlus deMinus : E →L[ℝ] E)
    (omega : E →L[ℝ] ℝ)
    (hPlus : ∀ v, covariantDerivativePlus ePlus eMinus dePlus omega v = 0)
    (hMinus : ∀ v, covariantDerivativeMinus ePlus eMinus deMinus omega v = 0)
    (hOrthogonal : ⟪ePlus, eMinus⟫_ℝ = 0) (v : E) :
    ⟪dePlus v, ePlus⟫_ℝ = 0 ∧ ⟪deMinus v, eMinus⟫_ℝ = 0 := by
  have hPlus' : dePlus v = -((omega v) • eMinus) := by
    have h := hPlus v
    exact eq_neg_of_add_eq_zero_left h
  have hMinus' : deMinus v = -((omega v) • ePlus) := by
    have h := hMinus v
    exact eq_neg_of_add_eq_zero_left h
  constructor
  · rw [hPlus', inner_neg_left, real_inner_smul_left, real_inner_comm,
      hOrthogonal, mul_zero, neg_zero]
  · rw [hMinus', inner_neg_left, real_inner_smul_left, hOrthogonal,
      mul_zero, neg_zero]

end
end InfoGeometry.Canonical
