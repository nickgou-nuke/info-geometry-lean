/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

namespace Omega.Zeta

/-- A function that eventually exceeds every linear function cannot itself have an eventual
linear upper bound. The hypothesis is the precise growth input; this theorem makes no claim about
which concrete counting functions satisfy it. -/
theorem not_eventually_linear_bounded_of_superlinear
    (f : ℕ → ℕ)
    (hsuper : ∀ C T0 : ℕ, ∃ T ≥ T0, C * T < f T) :
    ¬ ∃ C T0 : ℕ, ∀ T ≥ T0, f T ≤ C * T := by
  rintro ⟨C, T0, hbound⟩
  obtain ⟨T, hT, hlt⟩ := hsuper C T0
  exact (Nat.not_lt_of_ge (hbound T hT)) hlt

/-- Concrete counting model for the finite-generation obstruction: a finitely generated
addressability mechanism is represented by an eventual linear bound. The superlinear growth
property below is an explicit input, not established here as an analytic theorem about zeta zeros. -/
structure xi_addressability_counting_obstruction_data where
  zero_count : ℕ → ℕ
  strip_linear_constant : ℕ
  classical_superlinear :
    ∀ C T0 : ℕ, ∃ T ≥ T0, C * T < zero_count T

/-- Eventual `O(T)` growth in a fixed strip, as predicted by a finitely generated addressability
model. -/
def xi_addressability_counting_obstruction_data.finitely_generated_addressable
    (D : xi_addressability_counting_obstruction_data) : Prop :=
  ∃ T0 : ℕ, ∀ T ≥ T0, D.zero_count T ≤ D.strip_linear_constant * T

/-- Paper label: `prop:xi-addressability-counting-obstruction`.
Given the supplied superlinear-growth property, no finite-generation addressability model
represented by the stated eventual linear bound can hold. The analytic growth property is an
assumption of `D`, not a result proved by this theorem. -/
theorem paper_xi_addressability_counting_obstruction
    (D : xi_addressability_counting_obstruction_data) : ¬ D.finitely_generated_addressable := by
  intro hfg
  apply not_eventually_linear_bounded_of_superlinear D.zero_count D.classical_superlinear
  exact ⟨D.strip_linear_constant, hfg⟩

end Omega.Zeta
