/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
import Mathlib.Tactic

/-!
# Noncommutative Dirac and cyclic supertrace identities

This owner states the algebraic core of the transcript's graded-Dirac
archetype for arbitrary associative operator rings. It does not infer a heat
kernel formula, a Fredholm index, an Atiyah--Singer theorem, or characteristic
numbers from finite matrix calculations.
-/

namespace InfoGeometry.Canonical.AtiyahSingerDirac

open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace

variable {A : Type*} [Ring A]

/-- An odd Dirac operator has an even square: anticommutation with a grading
implies that the squared operator commutes with that grading. -/
theorem dirac_sq_grading_commutes {D γ : A}
    (h_odd : D * γ + γ * D = 0) :
    D * D * γ - γ * (D * D) = 0 := by
  have hswap : D * γ = -(γ * D) := eq_neg_of_add_eq_zero_left h_odd
  have hsquare : D * D * γ = γ * (D * D) := by
    calc
      D * D * γ = D * (D * γ) := by rw [mul_assoc]
      _ = D * (-(γ * D)) := by rw [hswap]
      _ = -(D * (γ * D)) := by rw [mul_neg]
      _ = -((D * γ) * D) := by rw [mul_assoc]
      _ = -((-(γ * D)) * D) := by rw [hswap]
      _ = γ * (D * D) := by simp [mul_assoc]
  rw [hsquare]
  exact sub_self _

/-- McKean--Singer's algebraic graded-trace cancellation for an odd operator
and an even observable. The conclusion is a cyclic-functional identity; it
does not assert heat-kernel or index invariance. -/
theorem mckean_singer_algebraic_cancellation {R : Type*}
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ)
    {γ D X : A} (hγD : γ * D = -(D * γ))
    (hγX : γ * X = X * γ) :
    gradedTrace τ γ (operatorAnticommutator D X) = 0 := by
  exact gradedTrace_anticommutator_eq_zero τ hτ hγD hγX

/-- The companion cyclic cancellation for a commutator whose first factor is
even under the grading. -/
theorem graded_commutator_cancellation {R : Type*}
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ)
    {γ B C : A} (hγB : γ * B = B * γ) :
    gradedTrace τ γ (operatorCommutator B C) = 0 := by
  exact gradedTrace_commutator_eq_zero τ hτ hγB

/-- The algebraic Drazin-style corner cancellation used in finite
McKean--Singer calculations: odd Peirce corners have zero cyclic graded
trace, while the even corner preserves it. -/
theorem graded_trace_peirce_split {R : Type*}
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ)
    {γ p X : A} (hp : p * p = p) (hγp : γ * p = p * γ) :
    gradedTrace τ γ (oddCorner p X) = 0 ∧
    gradedTrace τ γ (evenCorner p X) = gradedTrace τ γ X := by
  exact ⟨gradedTrace_oddCorner_eq_zero τ hτ hp hγp,
    gradedTrace_evenCorner_eq τ hτ hp hγp⟩

end InfoGeometry.Canonical.AtiyahSingerDirac
