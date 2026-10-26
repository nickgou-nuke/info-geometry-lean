/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornAlternativeLaws
import Mathlib.Tactic

/-!
# Zorn traceless two-mode polynomial flow

In the repository's actual Zorn multiplication convention the Casimir is
`α² + dot v w`, not `α² - dot v w`. This is a polynomial two-mode flow,
not a general analytic exponential or a global Lie-group representation.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-- Concrete coordinates of `zornTracelessExp`. -/
theorem zornTracelessExp_coordinates (c s α : R) (v w : ZornVec3 R) :
    zornTracelessExp c s α v w =
      ⟨c + s * α, (fun i => s * v i), (fun i => s * w i), c - s * α⟩ :=
  (zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 α v w).1

/-- Two-mode Cayley--Hamilton multiplication in a common generator. -/
theorem zornTracelessExp_mul
    (c₁ s₁ c₂ s₂ α : R) (v w : ZornVec3 R) :
    zornTracelessExp c₁ s₁ α v w * zornTracelessExp c₂ s₂ α v w =
      zornTracelessExp
        (c₁ * c₂ + s₁ * s₂ * zornTracelessCasimir α v w)
        (c₁ * s₂ + s₁ * c₂) α v w :=
  (zornTracelessExp_coords_casimir_norm_and_group_law 0 0 c₁ s₁ c₂ s₂ α v w).2.2.1

/-- Inverse candidate and its scalar norm obstruction; no invertibility is assumed. -/
theorem zornTracelessExp_mul_opposite
    (c s α : R) (v w : ZornVec3 R) :
    zornTracelessExp c s α v w * zornTracelessExp c (-s) α v w =
      (c * c - s * s * zornTracelessCasimir α v w) •
        (one : ZornVectorMatrix R) :=
  (zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 α v w).2.2.2

end InfoGeometry.Algebra.ZornVectorMatrix
