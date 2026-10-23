/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.SuperGrassmannianSusy

/-!
# Characteristic-two boundary for reflection/tangent equivalence

The reflection identity is always twice the Grassmannian tangent defect.  It
therefore cannot characterize tangency without an injectivity hypothesis for
doubling.  This file records an explicit kernel-checked counterexample over
`ZMod 2`, so the repaired theorem in `PeirceTangent` has a concrete boundary
case rather than an informal characteristic warning.
-/

namespace InfoGeometry.Core.PeirceTangent

open InfoGeometry.Core.SuperGrassmannianSusy

/-- Doubling is not injective in characteristic two. -/
theorem zmodTwo_doubling_not_injective :
    ¬ Function.Injective (fun y : ZMod 2 => (2 : ℕ) • y) := by
  intro h
  have h01 : (0 : ZMod 2) = 1 := by
    apply h
    decide
  norm_num at h01

/-- In characteristic two, reflection anticommutation can hold while the
first-order idempotent/tangent equation fails. -/
theorem zmodTwo_reflection_anticommutation_not_tangent :
    (¬ IsGrassmannianTangent (0 : ZMod 2) 1) ∧
      ((2 * (0 : ZMod 2) - 1) * 1 +
          1 * (2 * (0 : ZMod 2) - 1) = 0) := by
  constructor
  · intro h
    norm_num [IsGrassmannianTangent, jordanProd] at h
  · decide

/-- The counterexample is exactly the failure of the missing doubling
injectivity premise in the reflection characterization. -/
theorem zmodTwo_reflection_boundary :
    ¬ Function.Injective (fun y : ZMod 2 => (2 : ℕ) • y) ∧
      (¬ IsGrassmannianTangent (0 : ZMod 2) 1 ∧
        ((2 * (0 : ZMod 2) - 1) * 1 +
            1 * (2 * (0 : ZMod 2) - 1) = 0)) := by
  exact ⟨zmodTwo_doubling_not_injective,
    zmodTwo_reflection_anticommutation_not_tangent⟩

end InfoGeometry.Core.PeirceTangent
