import InfoGeometry.EntropicInference
set_option linter.unusedSectionVars false

namespace InfoGeometry.KL.EntropicInferenceTest

open InfoGeometry.EntropicInference
open scoped BigOperators

inductive State
  | zero
  | one
deriving Repr, DecidableEq, Fintype, Nonempty

abbrev X_test := State
abbrev Θ_test := State

-- Test: marginal_x and marginal_theta sum to 1 and are nonnegative
example {X Θ : Type} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]
    (p : FinProb (X × Θ)) :
  (∀ x, 0 ≤ marginal_x p x) ∧ (∀ θ, 0 ≤ marginal_theta p θ) ∧
    (∑ x, marginal_x p x = 1) ∧ (∑ θ, marginal_theta p θ = 1) :=
by
  constructor
  · intro x; exact bot_le
  constructor
  · intro θ; exact bot_le
  constructor
  · classical
    simpa [tsum_fintype] using (marginal_x p).tsum_coe
  · classical
    simpa [tsum_fintype] using (marginal_theta p).tsum_coe

-- Test: assemble produces a valid joint
example {X Θ : Type} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]
    (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) :
  (∀ xt, 0 ≤ assemble pX pΘ_givenX xt) ∧ (∑ xt, assemble pX pΘ_givenX xt = 1) :=
by
  constructor
  · intro xt; exact bot_le
  · classical
    simpa [tsum_fintype] using (assemble pX pΘ_givenX).tsum_coe

-- Test: marginal of an assembled joint is the original marginal
example {X Θ : Type} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]
    (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) :
  marginal_x (assemble pX pΘ_givenX) = pX := by
  exact marginal_x_assemble pX pΘ_givenX

-- Test: conditional is a valid probability law
example {X Θ : Type} [Fintype X] [Fintype Θ] [MeasurableSpace X] [MeasurableSpace Θ]
    (p : FinProb (X × Θ)) (x : X) (hx : x ∈ (marginal_x p).support) :
    (∑ θ, cond_theta_given_x p x hx θ = 1) := by
  classical
  simpa [tsum_fintype] using (cond_theta_given_x p x hx).tsum_coe

-- Test: `ProbabilityDist` is a definitional alias of `FinProb`
example {α : Type} [Fintype α] (p : FinProb α) :
  (p : InfoGeometry.ProbabilityDist α) = p := rfl

-- Test: expectation compatibility for coercions
example {α : Type} [Fintype α] (p : FinProb α) (f : α → ℝ) :
  InfoGeometry.expectation (p : InfoGeometry.ProbabilityDist α) f = ∑ x, (p x).toReal * f x := by
  rfl

-- Constructive finite chain-rule in `toReal` form (strict-positivity variant).
example {X Θ : Type} [Fintype X] [Fintype Θ] [DecidableEq X] [DecidableEq Θ]
    [MeasurableSpace X] [MeasurableSpace Θ]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Θ]
    [Nonempty Θ]
    (p q : FinProb (X × Θ))
    (hposp : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal)
    (hposq : ∀ x : X, ∀ θ : Θ, 0 < (q (x, θ)).toReal) :
    (KL p q).toReal =
      (InfoGeometry.kl_div (α := X)
        (marginal_x (X := X) (Θ := Θ) p).toMeasure
        (marginal_x (X := X) (Θ := Θ) q).toMeasure).toReal
      +
      (∑ x : X, (marginal_x (X := X) (Θ := Θ) p x).toReal *
        (InfoGeometry.kl_div (α := Θ)
          (cond_theta_given_x (X := X) (Θ := Θ) p x
            (InfoGeometry.EntropicInference.marginal_x_full_support_of_joint_toReal_pos p hposp x)).toMeasure
          (cond_theta_given_x (X := X) (Θ := Θ) q x
            (InfoGeometry.EntropicInference.marginal_x_full_support_of_joint_toReal_pos q hposq x)).toMeasure).toReal) := by
  simpa using InfoGeometry.EntropicInference.kl_chain_rule_toReal_strict p q hposp hposq

-- Constructive Jeffrey KL-Pythagorean decomposition in `toReal` form (no `KlChainRule` hypothesis).
example {X Θ : Type} [Fintype X] [Fintype Θ] [DecidableEq X] [DecidableEq Θ]
    [MeasurableSpace X] [MeasurableSpace Θ]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Θ]
    [Nonempty Θ]
    (p q : FinProb (X × Θ))
    (hposp : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal)
    (hposq : ∀ x : X, ∀ θ : Θ, 0 < (q (x, θ)).toReal) :
    (KL p q).toReal =
      (KL p (jeffrey_joint q (marginal_x p)
        (InfoGeometry.EntropicInference.marginal_x_full_support_of_joint_toReal_pos q hposq))).toReal
      +
      (InfoGeometry.kl_div (α := X)
        (marginal_x p).toMeasure
        (marginal_x q).toMeasure).toReal := by
  simpa using InfoGeometry.EntropicInference.kl_pythagorean_jeffrey_toReal_strict
    (p := p) (q := q) (p_x := marginal_x p) hposp hposq rfl

-- Constructive Jeffrey KL-Pythagorean decomposition in `ℝ≥0∞` form (no `KlChainRule` hypothesis).
example {X Θ : Type} [Fintype X] [Fintype Θ] [DecidableEq X] [DecidableEq Θ]
    [MeasurableSpace X] [MeasurableSpace Θ]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Θ]
    [Nonempty Θ]
    (p q : FinProb (X × Θ))
    (hposp : ∀ x : X, ∀ θ : Θ, 0 < (p (x, θ)).toReal)
    (hposq : ∀ x : X, ∀ θ : Θ, 0 < (q (x, θ)).toReal) :
    KL p q =
      KL p (jeffrey_joint q (marginal_x p)
        (InfoGeometry.EntropicInference.marginal_x_full_support_of_joint_toReal_pos q hposq))
      +
      InfoGeometry.kl_div (α := X)
        (marginal_x p).toMeasure
        (marginal_x q).toMeasure := by
  simpa using InfoGeometry.EntropicInference.kl_pythagorean_jeffrey_strict
    (p := p) (q := q) (p_x := marginal_x p) hposp hposq rfl

section StrictPositiveStateTests

variable [MeasurableSpace X_test] [MeasurableSpace Θ_test]
  [MeasurableSingletonClass X_test] [MeasurableSingletonClass Θ_test]

variable (p q : Joint X_test Θ_test)
variable (p_x : FinProb X_test)
variable (hposp : ∀ x : X_test, ∀ θ : Θ_test, 0 < (p (x, θ)).toReal)
variable (hposq : ∀ x : X_test, ∀ θ : Θ_test, 0 < (q (x, θ)).toReal)
variable (hmarg : marginal_x p = p_x)

lemma hq_support_of_strict_pos
    (hposq : ∀ x : X_test, ∀ θ : Θ_test, 0 < (q (x, θ)).toReal)
    (x : X_test) : x ∈ (marginal_x q).support := by
  exact (marginal_x_full_support_of_joint_toReal_pos q hposq) x

noncomputable example : Joint X_test Θ_test :=
  jeffrey_joint q p_x (fun x => hq_support_of_strict_pos (q := q) hposq x)

example :
    kl p q =
      kl p (jeffrey_joint q p_x
        (fun x => hq_support_of_strict_pos (q := q) hposq x))
      + InfoGeometry.kl_div (α := X_test) p_x.toMeasure (marginal_x q).toMeasure := by
  simpa using
    kl_pythagorean_jeffrey_strict
      (p := p) (q := q) (p_x := p_x) hposp hposq hmarg

example :
    (kl p q).toReal =
      (kl p (jeffrey_joint q p_x
        (fun x => hq_support_of_strict_pos (q := q) hposq x))).toReal
      + (InfoGeometry.kl_div (α := X_test) p_x.toMeasure (marginal_x q).toMeasure).toReal := by
  simpa using
    kl_pythagorean_jeffrey_toReal_strict
      (p := p) (q := q) (p_x := p_x) hposp hposq hmarg

end StrictPositiveStateTests

end InfoGeometry.KL.EntropicInferenceTest
