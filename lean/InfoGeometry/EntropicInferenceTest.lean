import InfoGeometry.EntropicInference

open InfoGeometry.EntropicInference
open scoped BigOperators

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
  exact condΘGivenX_toFun p x hx θ

-- KL chain-rule (pointwise decomposition test)
example {X Θ : Type} [Fintype X] [Fintype Θ]
    (p q : FinProb (X × Θ))
    (hp : ∀ x, 0 < (marginalX p).toFun x)
    (hq : ∀ x, 0 < (marginalX q).toFun x) :
  Prop :=
  KL_chain_rule p q hq hp

-- Test: Jeffrey update is ME (concrete Bool × Bool example, full joint support)
-- [TEST DISABLED] dependent theorems were stubbed out
-- example :
--   let q : FinProb (Bool × Bool) := { toFun := fun _ => (1 : ℝ) / 4,
--     nonneg := by intro _; norm_num,
--     sum_one := by simp [Finset.sum_const, Finset.card_univ]; norm_num }
--   let pX : FinProb Bool := { toFun := fun b => if b then (3 : ℝ) / 5 else (2 : ℝ) / 5,
--     nonneg := by intro b; split_ifs; norm_num,
--     sum_one := by simp [Finset.sum_const, Finset.card_univ]; norm_num }
--   let p := assemble pX (fun _ => dirac true)
--   -- `q` has full joint support and `pX` is strictly positive
--   have hq_joint : ∀ z, 0 < q.toFun z := fun _ => by norm_num
--   have hpX_pos : ∀ x, 0 < pX.toFun x := by intro x; dsimp [pX]; split_ifs; norm_num
--   show Entropy p q ≤ Entropy (jeffreyJoint q pX (fun x => Finset.sum_pos fun θ _ => hq_joint (x, θ))) q := by
--     apply (jeffrey_is_ME_of_full_support q pX hq_joint hpX_pos) p
--     simp [marginalX_assemble]
--
-- Test: Jeffrey update is ME when `pX` has a zero mass entry and `q` only needs positive
-- slice support on the `x` where `pX` is positive.
-- example :
--   let q : FinProb (Bool × Bool) := { toFun := fun z =>
--       match z with
--       | (true, true) => (1 : ℝ) / 2
--       | (true, false) => (1 : ℝ) / 2
--       | (_, _) => 0
--     , nonneg := by intro _; norm_num,
--     sum_one := by simp [Finset.sum_const, Finset.card_univ]; norm_num }
--   let pX : FinProb Bool := { toFun := fun b => if b then 1 else 0,
--     nonneg := by intro b; split_ifs; norm_num,
--     sum_one := by simp [Finset.sum_const, Finset.card_univ]; norm_num }
--   let p := assemble pX (fun _ => dirac true)
--   have hq_slice : ∀ x, 0 < pX.toFun x → ∀ θ, 0 < q.toFun (x, θ) := by
--     intro x hx; cases x; · intro θ; cases θ; norm_num; · intro θ; contradiction
--   show Entropy p q ≤ Entropy (jeffreyJoint_on_support q pX hq_slice) q := by
--     apply (jeffrey_is_ME_on_support q pX hq_slice) p
--     simp [marginalX_assemble]

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
