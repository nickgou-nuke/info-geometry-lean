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

/-- Quotient descent preserves addition of glide-compatible operators. -/
theorem quotientOperator_add_wave37
    (operator₁ operator₂ : Module.End ℝ (BrillouinTorus → V))
    (preserves₁ : ∀ field : invariantFields (V := V),
      operator₁ field ∈ invariantFields)
    (preserves₂ : ∀ field : invariantFields (V := V),
      operator₂ field ∈ invariantFields) :
    quotientOperator (operator₁ + operator₂) (by
        intro field
        exact (invariantFields (V := V)).add_mem
          (preserves₁ field) (preserves₂ field)) =
      quotientOperator operator₁ preserves₁ +
        quotientOperator operator₂ preserves₂ := by
  symm
  apply quotientOperator_unique
  intro field point
  change quotientOperator operator₁ preserves₁ field (quotientMap point) +
      quotientOperator operator₂ preserves₂ field (quotientMap point) =
    (operator₁ + operator₂)
      (fun representative => field (quotientMap representative)) point
  rw [quotientOperator_apply, quotientOperator_apply, LinearMap.add_apply]
  rfl

/-- Quotient descent preserves real scalar multiplication of
-glide-compatible operators. -/
theorem quotientOperator_smul_wave37
    (scalar : ℝ) (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields) :
    quotientOperator (scalar • operator) (by
        intro field
        exact (invariantFields (V := V)).smul_mem scalar
          (preserves field)) =
      scalar • quotientOperator operator preserves := by
  symm
  apply quotientOperator_unique
  intro field point
  change scalar •
      (quotientOperator operator preserves field (quotientMap point)) =
    (scalar • operator)
      (fun representative => field (quotientMap representative)) point
  rw [quotientOperator_apply, LinearMap.smul_apply]
  rfl

end InfoGeometry.Topology.KleinRealOperatorDescent
