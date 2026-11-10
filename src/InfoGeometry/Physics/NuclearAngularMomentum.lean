/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

/-!
# Integer triangle inequalities for angular momentum labels

This module proves the natural-number triangle constraints on a coupled
angular-momentum label. Clebsch–Gordan coefficients and the Wigner–Eckart
theorem are not formalized here.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearAngularMomentum

/- The triangle inequalities are stated both in subtraction form and in the
addition form that avoids truncated subtraction. -/

/-- Equivalent forms of the natural-number triangle inequalities. -/
theorem angular_momentum_triangle_iff (j₁ j₂ J : ℕ) :
    (j₁ - j₂ ≤ J ∧ j₂ - j₁ ≤ J ∧ J ≤ j₁ + j₂) ↔
      (j₁ ≤ J + j₂ ∧ j₂ ≤ J + j₁ ∧ J ≤ j₁ + j₂) := by
  omega

/-- Convert the three triangle bounds into their equivalent subtraction form. -/
theorem angular_momentum_triangle (j₁ j₂ J : ℕ)
    (hJ : J ≤ j₁ + j₂) (hJ₁ : j₁ ≤ J + j₂) (hJ₂ : j₂ ≤ J + j₁) :
    j₁ - j₂ ≤ J ∧ j₂ - j₁ ≤ J ∧ J ≤ j₁ + j₂ := by
  exact (angular_momentum_triangle_iff j₁ j₂ J).2 ⟨hJ₁, hJ₂, hJ⟩

end InfoGeometry.Physics.NuclearAngularMomentum
