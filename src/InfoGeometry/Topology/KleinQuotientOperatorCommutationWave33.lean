/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinQuotientOperatorCompositionWave29

noncomputable section

namespace InfoGeometry.Topology.KleinRealOperatorDescent

open KleinBrillouinBase KleinBottleOrbitQuotient

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Quotient descent preserves commutation of glide-compatible operators. -/
theorem quotientOperator_commutes_wave33
    (operator₁ operator₂ : Module.End ℝ (BrillouinTorus → V))
    (preserves₁ : ∀ field : invariantFields (V := V),
      operator₁ field ∈ invariantFields)
    (preserves₂ : ∀ field : invariantFields (V := V),
      operator₂ field ∈ invariantFields)
    (hcomm : operator₁ * operator₂ = operator₂ * operator₁) :
    quotientOperator operator₁ preserves₁ * quotientOperator operator₂ preserves₂ =
      quotientOperator operator₂ preserves₂ * quotientOperator operator₁ preserves₁ := by
  let hcomp₁₂ : ∀ field : invariantFields (V := V),
      (operator₁ * operator₂) field ∈ invariantFields := by
    intro field
    exact preserves₁ ⟨operator₂ field, preserves₂ field⟩
  let hcomp₂₁ : ∀ field : invariantFields (V := V),
      (operator₂ * operator₁) field ∈ invariantFields := by
    intro field
    exact preserves₂ ⟨operator₁ field, preserves₁ field⟩
  calc
    quotientOperator operator₁ preserves₁ * quotientOperator operator₂ preserves₂ =
        quotientOperator (operator₁ * operator₂) hcomp₁₂ := by
      exact (quotientOperator_mul_wave29 operator₁ operator₂ preserves₁ preserves₂).symm
    _ = quotientOperator (operator₂ * operator₁) hcomp₂₁ := by
      apply quotientOperator_unique
      intro field point
      exact congrFun (congrArg (fun op => op
        (fun representative => field (quotientMap representative))) hcomm) point
    _ = quotientOperator operator₂ preserves₂ * quotientOperator operator₁ preserves₁ := by
      exact quotientOperator_mul_wave29 operator₂ operator₁ preserves₂ preserves₁

end InfoGeometry.Topology.KleinRealOperatorDescent
