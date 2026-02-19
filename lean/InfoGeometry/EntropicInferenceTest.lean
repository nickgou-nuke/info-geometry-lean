import InfoGeometry.EntropicInference
import Mathlib.Tactic

open InfoGeometry.EntropicInference

-- Test: marginalX and marginalΘ sum to 1 and are nonnegative
example {X Θ : Type} [Fintype X] [Fintype Θ] (p : FinProb (X × Θ)) :
  (∀ x, 0 ≤ marginalX p x) ∧ (∀ θ, 0 ≤ marginalΘ p θ) ∧ (∑ x, marginalX p x = 1) ∧ (∑ θ, marginalΘ p θ = 1) :=
by
  constructor
  · intro x; exact (marginalX p).nonneg x
  constructor
  · intro θ; exact (marginalΘ p).nonneg θ
  constructor
  · exact (marginalX p).sum_eq_one
  · exact (marginalΘ p).sum_eq_one

-- Test: assemble produces a valid joint
example {X Θ : Type} [Fintype X] [Fintype Θ] (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) :
  (∀ xt, 0 ≤ assemble pX pΘ_givenX xt) ∧ (∑ xt, assemble pX pΘ_givenX xt = 1) :=
by
  constructor
  · intro xt; exact (assemble pX pΘ_givenX).nonneg xt
  · exact (assemble pX pΘ_givenX).sum_eq_one

-- Test: normalize produces a valid FinProb
example {α : Type} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hZ : 0 < ∑ a, w a) :
  (∀ a, 0 ≤ normalize w hw hZ a) ∧ (∑ a, normalize w hw hZ a = 1) :=
by
  constructor
  · intro a; exact (normalize w hw hZ).nonneg a
  · exact (normalize w hw hZ).sum_eq_one
