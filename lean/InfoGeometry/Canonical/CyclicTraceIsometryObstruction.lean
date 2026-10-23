import Mathlib.Algebra.Ring.Basic

namespace InfoGeometry.Canonical.CyclicTraceIsometryObstruction

/-!
An abstract form of the finite Cuntz/CCR trace obstruction.  The carrier is
an arbitrary associative ring; no matrix coordinates, diagonalization, or
commutativity of the carrier is used.
-/

variable {A C : Type*} [Ring A] [Ring C] [Nontrivial C]

/-- Two one-sided inverses whose range idempotents partition the unit force
every cyclic additive trace to vanish on the unit. -/
theorem cyclic_additive_trace_vanishes_on_unit
    (x₀ y₀ x₁ y₁ : A) (τ : A →+ C)
    (hcyc : ∀ a b : A, τ (a * b) = τ (b * a))
    (h₀ : y₀ * x₀ = 1) (h₁ : y₁ * x₁ = 1)
    (hsum : x₀ * y₀ + x₁ * y₁ = 1) :
    τ 1 = 0 := by
  have ht₀ : τ (x₀ * y₀) = τ 1 := by
    rw [hcyc, h₀]
  have ht₁ : τ (x₁ * y₁) = τ 1 := by
    rw [hcyc, h₁]
  have hτsum := congrArg τ hsum
  rw [map_add, ht₀, ht₁] at hτsum
  have h : τ 1 + τ 1 = τ 1 + 0 := by simpa using hτsum
  exact add_left_cancel h

/-- Consequently, a normalized cyclic additive trace cannot exist for such a
two-range partition in a nontrivial target ring. -/
theorem no_normalized_cyclic_additive_trace
    (x₀ y₀ x₁ y₁ : A) (τ : A →+ C)
    (hcyc : ∀ a b : A, τ (a * b) = τ (b * a))
    (h₀ : y₀ * x₀ = 1) (h₁ : y₁ * x₁ = 1)
    (hsum : x₀ * y₀ + x₁ * y₁ = 1)
    (hnorm : τ 1 = 1) : False := by
  have hzero := cyclic_additive_trace_vanishes_on_unit x₀ y₀ x₁ y₁ τ hcyc h₀ h₁ hsum
  exact zero_ne_one (hzero.symm.trans hnorm)

end InfoGeometry.Canonical.CyclicTraceIsometryObstruction
