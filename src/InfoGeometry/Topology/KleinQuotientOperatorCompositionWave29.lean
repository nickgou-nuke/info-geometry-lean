/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinRealOperatorDescent

noncomputable section

namespace InfoGeometry.Topology.KleinRealOperatorDescent

open KleinBrillouinBase KleinBottleOrbitQuotient

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Restriction to glide-invariant fields preserves composition of operators. -/
theorem restrictOperator_mul_wave29
    (operator₁ operator₂ : Module.End ℝ (BrillouinTorus → V))
    (preserves₁ : ∀ field : invariantFields (V := V),
      operator₁ field ∈ invariantFields)
    (preserves₂ : ∀ field : invariantFields (V := V),
      operator₂ field ∈ invariantFields) :
    restrictOperator operator₁ preserves₁ * restrictOperator operator₂ preserves₂ =
      restrictOperator (operator₁ * operator₂) (by
        intro field
        exact preserves₁ ⟨operator₂ field, preserves₂ field⟩) := by
  apply LinearMap.ext
  intro field
  apply Subtype.ext
  rfl

/-- Quotient descent preserves composition of glide-compatible operators. -/
theorem quotientOperator_mul_wave29
    (operator₁ operator₂ : Module.End ℝ (BrillouinTorus → V))
    (preserves₁ : ∀ field : invariantFields (V := V),
      operator₁ field ∈ invariantFields)
    (preserves₂ : ∀ field : invariantFields (V := V),
      operator₂ field ∈ invariantFields) :
    quotientOperator (operator₁ * operator₂) (by
        intro field
        exact preserves₁ ⟨operator₂ field, preserves₂ field⟩) =
      quotientOperator operator₁ preserves₁ * quotientOperator operator₂ preserves₂ := by
  unfold quotientOperator
  rw [← map_mul]
  exact congrArg (LinearEquiv.conjAlgEquiv ℝ (fieldEquiv (V := V)).symm)
    (restrictOperator_mul_wave29 operator₁ operator₂ preserves₁ preserves₂).symm

end InfoGeometry.Topology.KleinRealOperatorDescent
