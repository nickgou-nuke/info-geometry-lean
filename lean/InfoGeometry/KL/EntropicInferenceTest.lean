import InfoGeometry.EntropicInference

namespace InfoGeometry.KL.EntropicInferenceTest

open InfoGeometry.EntropicInference
open scoped BigOperators

-- Test: marginal_x and marginal_theta sum to 1 and are nonnegative
example {X Θ : Type} [Fintype X] [Fintype Θ] (p : FinProb (X × Θ)) :
  (∀ x, 0 ≤ marginal_x p x) ∧ (∀ θ, 0 ≤ marginal_theta p θ) ∧ (∑ x, marginal_x p x = 1) ∧ (∑ θ, marginal_theta p θ = 1) :=
by
  constructor
  · intro x; exact (marginal_x p).nonneg x
  constructor
  · intro θ; exact (marginal_theta p).nonneg θ
  constructor
  · exact (marginal_x p).sum_one
  · exact (marginal_theta p).sum_one

-- Test: assemble produces a valid joint
example {X Θ : Type} [Fintype X] [Fintype Θ] (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) :
  (∀ xt, 0 ≤ assemble pX pΘ_givenX xt) ∧ (∑ xt, assemble pX pΘ_givenX xt = 1) :=
by
  constructor
  · intro xt; exact (assemble pX pΘ_givenX).nonneg xt
  · exact (assemble pX pΘ_givenX).sum_one

-- Test: marginal of an assembled joint is the original marginal
example {X Θ : Type} [Fintype X] [Fintype Θ] (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) :
  marginal_x (assemble pX pΘ_givenX) = pX := by
  exact marginal_x_assemble pX pΘ_givenX

-- Test: `cond_theta_given_x` uses the expected pointwise division formula
example {X Θ : Type} [Fintype X] [Fintype Θ] (p : FinProb (X × Θ)) (x : X)
    (hx : 0 < (marginal_x p).toFun x) (θ : Θ) :
  (cond_theta_given_x p x hx).toFun θ = p.toFun (x, θ) / (marginal_x p).toFun x :=
by
  exact cond_theta_given_x_toFun p x hx θ

-- KL chain-rule holds (proved by `kl_chain_rule`)
example {X Θ : Type} [Fintype X] [Fintype Θ] [DecidableEq X]
    (p q : FinProb (X × Θ))
    (hp : ∀ x, 0 < (marginal_x p).toFun x)
    (hq : ∀ x, 0 < (marginal_x q).toFun x) :
    KL p q =
      KL (marginal_x p) (marginal_x q) +
      ∑ x : X, (marginal_x p).toFun x *
        KL (cond_theta_given_x p x (hp x)) (cond_theta_given_x q x (hq x)) :=
  kl_chain_rule p q hq hp

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
example {α : Type} [Fintype α] (p : FinProb α) (f : α → ℝ) :
  InfoGeometry.expectation (p : InfoGeometry.ProbabilityDist α) f = ∑ x, p.toFun x * f x := by simp

end InfoGeometry.KL.EntropicInferenceTest
