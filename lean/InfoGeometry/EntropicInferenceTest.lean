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
  · exact (marginalX p).sum_one
  · exact (marginalΘ p).sum_one

-- Test: assemble produces a valid joint
example {X Θ : Type} [Fintype X] [Fintype Θ] (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) :
  (∀ xt, 0 ≤ assemble pX pΘ_givenX xt) ∧ (∑ xt, assemble pX pΘ_givenX xt = 1) :=
by
  constructor
  · intro xt; exact (assemble pX pΘ_givenX).nonneg xt
  · exact (assemble pX pΘ_givenX).sum_one

-- Test: marginal of an assembled joint is the original marginal
example {X Θ : Type} [Fintype X] [Fintype Θ] (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) :
  marginalX (assemble pX pΘ_givenX) = pX := by
  exact marginalX_assemble pX pΘ_givenX

-- Test: `condΘGivenX` uses the expected pointwise division formula
example {X Θ : Type} [Fintype X] [Fintype Θ] (p : FinProb (X × Θ)) (x : X)
    (hx : 0 < (marginalX p).toFun x) (θ : Θ) :
  (condΘGivenX p x hx).toFun θ = p.toFun (x, θ) / (marginalX p).toFun x :=
by
  simp [condΘGivenX_toFun]

-- KL chain-rule (pointwise decomposition test)
example {X Θ : Type} [Fintype X] [Fintype Θ]
    (p q : FinProb (X × Θ))
    (hp : ∀ x, 0 < (marginalX p).toFun x)
    (hq : ∀ x, 0 < (marginalX q).toFun x) :
  KL p q = KL (marginalX p) (marginalX q) + ∑ x, (marginalX p).toFun x *
    KL (condΘGivenX p x (hp x)) (condΘGivenX q x (hq x)) := by
  exact KL_chain_rule p q hq hp

-- Test: normalize produces a valid FinProb
example {α : Type} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hZ : 0 < ∑ a, w a) :
  (∀ a, 0 ≤ normalize w hw hZ a) ∧ (∑ a, normalize w hw hZ a = 1) :=
by
  constructor
  · intro a; exact (normalize w hw hZ).nonneg a
  · exact (normalize w hw hZ).sum_one

-- Test: round-trip conversions between `FinProb` and `ProbabilityDist`
example {α : Type} [Fintype α] (p : FinProb α) :
  ((p : InfoGeometry.ProbabilityDist α).toFinProb = p) := by simp

example {α : Type} [Fintype α] (P : InfoGeometry.ProbabilityDist α) :
  ((P.toFinProb : InfoGeometry.ProbabilityDist α) = P) := by simp

-- Test: expectation compatibility for coercions
example {α : Type} [Fintype α] [DecidableEq α] (p : FinProb α) (f : α → ℝ) :
  InfoGeometry.expectation (p : InfoGeometry.ProbabilityDist α) f = ∑ x, p.toFun x * f x := by simp
