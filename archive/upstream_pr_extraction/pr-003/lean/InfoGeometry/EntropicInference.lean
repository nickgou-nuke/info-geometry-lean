import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

import InfoGeometry.Basic
import InfoGeometry.KL.Finite

open scoped BigOperators

namespace InfoGeometry.EntropicInference

/-!
Finite entropic inference core:
- `FinProb α`: finite probability vectors with values in `ℝ`
- `KL (p ‖ q)` with a safe `0 * log (0 / _) = 0` convention
- Bayes/Jeffrey constructions on finite joint spaces
-/


section FiniteProb

variable {α : Type} [Fintype α]

/-- Use the canonical `FinProb` from `InfoGeometry.Basic`. -/
abbrev FinProb (α : Type*) [Fintype α] := InfoGeometry.FinProb α

/-- Delegate to the canonical `InfoGeometry.normalize` in `Basic.lean`. -/
noncomputable def normalize
    {α : Type} [Fintype α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hZ : 0 < (∑ a, w a)) : FinProb α :=
  InfoGeometry.normalize (w := w) (hw := hw) (hZ := hZ)

/-- Delegate to the canonical `InfoGeometry.dirac` in `Basic.lean`. -/
noncomputable def dirac
    {α : Type} [Fintype α] [DecidableEq α]
    (a0 : α) : FinProb α :=
  InfoGeometry.dirac (a0 := a0)

/-- KL term with `0 * log(0 / _) = 0` convention. -/
noncomputable def klTerm (p q : ℝ) : ℝ :=
  if p = 0 then 0 else p * Real.log (p / q)

/-- Kullback–Leibler divergence `KL(p ‖ q)` on finite probability vectors. -/
noncomputable def KL {α : Type} [Fintype α] (p q : FinProb α) : ℝ :=
  ∑ a, klTerm (p.toFun a) (q.toFun a)

/-- Negative KL as entropy-like update objective. -/
noncomputable def Entropy {α : Type} [Fintype α] (p q : FinProb α) : ℝ :=
  -KL p q

/-- Forwarding wrapper to the canonical converter in `Basic.lean`. -/
def toProbabilityDist {α : Type} [Fintype α] (p : FinProb α) : InfoGeometry.ProbabilityDist α :=
  FinProb.toProbabilityDist p

/-- Bridge to the core KL definition when the reference distribution has full support. -/
lemma KL_eq_klDiv
    {α : Type} [Fintype α]
    (p q : FinProb α) (hq : ∀ a, 0 < q.toFun a) :
    KL p q = InfoGeometry.klDiv (toProbabilityDist p) (toProbabilityDist q) := by
  classical
  unfold KL InfoGeometry.klDiv InfoGeometry.expectation InfoGeometry.logDensity
  refine Finset.sum_congr rfl ?_
  intro a _ha
  by_cases hp : p.toFun a = 0
  · simp [klTerm, hp, toProbabilityDist, FinProb.toProbabilityDist_prob]
  · rw [klTerm, if_neg hp]
    have hq_ne : q.toFun a ≠ 0 := (hq a).ne'
    -- By definition, (toProbabilityDist q).prob a = q.toFun a
    simp only [toProbabilityDist, FinProb.toProbabilityDist_prob]
    rw [Real.log_div hp hq_ne]

/-- Gibbs inequality in finite dimension under strict positivity of the reference law. -/
theorem KL_nonneg
    {α : Type} [Fintype α]
    (p q : FinProb α) (hq : ∀ a, 0 < q.toFun a) : 0 ≤ KL p q := by
  rw [KL_eq_klDiv (p := p) (q := q) hq]
  exact InfoGeometry.KL.klDiv_nonneg_of_fullSupport
    (P := toProbabilityDist p)
    (Q := toProbabilityDist q)
    (h_support := hq)

variable {α : Type} [Fintype α]


/-- Self-divergence vanishes. -/
lemma KL_self {α : Type} [Fintype α] (p : FinProb α) : KL p p = 0 := by
  classical
  unfold KL
  -- switch to an explicit `Finset.sum` to use `Finset.sum_eq_zero`
  apply Finset.sum_eq_zero
  intros a _ha
  by_cases hp : p.toFun a = 0
  · simp [klTerm, hp]
  · have : p.toFun a / p.toFun a = (1 : ℝ) := div_self hp
    simp [klTerm, hp]

lemma Entropy_le_Entropy_of_eq
    {α : Type} [Fintype α]
    (p q : FinProb α) (hq : ∀ a, 0 < q.toFun a) :
    Entropy p q ≤ Entropy q q := by
  have hpq : Entropy p q ≤ 0 := neg_nonpos.mpr (KL_nonneg p q hq)
  have hqq : Entropy q q = 0 := by simp [Entropy, KL_self]
  exact le_trans hpq (by simp [hqq])

end FiniteProb


section BayesJeffreyFinite

variable {X Θ : Type} [Fintype X] [Fintype Θ]

/-- Joint distributions on `X × Θ`. -/
abbrev Joint := FinProb (X × Θ)

/-- Marginal on `X`. -/
noncomputable def marginalX (p : FinProb (X × Θ)) : FinProb X := by
  classical
  refine {
    toFun := fun x => Finset.sum Finset.univ (fun θ => p.toFun (x, θ)),
    nonneg := by
      intro x
      apply Finset.sum_nonneg
      intro θ _
      exact p.nonneg (x, θ),
    sum_one := by
      calc
        (∑ x : X, ∑ θ : Θ, p.toFun (x, θ)) = ∑ z : X × Θ, p.toFun z := by rw [← Fintype.sum_prod_type']
        _ = 1 := p.sum_one
  }

/-- Marginal on `Θ`. -/
noncomputable def marginalΘ (p : FinProb (X × Θ)) : FinProb Θ := by
  classical
  refine {
    toFun := fun θ => Finset.sum Finset.univ (fun x => p.toFun (x, θ)),
    nonneg := by
      intro θ
      apply Finset.sum_nonneg
      intro x _
      exact p.nonneg (x, θ),
    sum_one := by
      calc
        (∑ θ : Θ, ∑ x : X, p.toFun (x, θ)) = ∑ x, ∑ θ, p.toFun (x, θ) := by rw [Finset.sum_comm]
        _ = ∑ z : X × Θ, p.toFun z := by rw [← Fintype.sum_prod_type']
        _ = 1 := p.sum_one
  }

/-- Conditional `p(θ | x)` by normalizing `θ ↦ p(x, θ)`; requires positive `x`-marginal. -/
noncomputable def condΘGivenX
    (p : FinProb (X × Θ)) (x : X)
    (hx : 0 < (marginalX p).toFun x) : FinProb Θ := by
  classical
  let w : Θ → ℝ := fun θ => p.toFun (x, θ)
  have hw : ∀ θ, 0 ≤ w θ := by intro θ; exact p.nonneg (x, θ)
  have hZ : 0 < (∑ θ : Θ, w θ) := by
    simp only [w]
    convert hx using 1
  exact normalize w hw hZ

/-- `condΘGivenX` projection (pointwise formula). -/
@[simp] lemma condΘGivenX_toFun (p : FinProb (X × Θ)) (x : X) (hx : 0 < (marginalX p).toFun x)
    (θ : Θ) : (condΘGivenX p x hx).toFun θ = p.toFun (x, θ) / (marginalX p).toFun x :=
  by
    dsimp [condΘGivenX, normalize]
    -- `normalize` definition gives `toFun := fun a => w a / Z` with `w := fun θ => p.toFun (x, θ)`
    rfl

/-- Assemble a joint distribution from a marginal on `X` and conditionals on `Θ | X`. -/
noncomputable def assemble (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) : FinProb (X × Θ) := by
  classical
  refine {
    toFun := fun xt => pX.toFun xt.1 * (pΘ_givenX xt.1).toFun xt.2,
    nonneg := by
      intro xt
      exact mul_nonneg (pX.nonneg xt.1) ((pΘ_givenX xt.1).nonneg xt.2),
    sum_one := by
      calc
        (∑ z : X × Θ, pX.toFun z.1 * (pΘ_givenX z.1).toFun z.2)
          = ∑ x : X, ∑ θ : Θ, pX.toFun x * (pΘ_givenX x).toFun θ := by rw [← Fintype.sum_prod_type']
        _ = ∑ x : X, pX.toFun x * (∑ θ : Θ, (pΘ_givenX x).toFun θ) := by
              congr 1
              funext x
              rw [Finset.mul_sum]
        _ = ∑ x : X, pX.toFun x * 1 := by simp
        _ = ∑ x : X, pX.toFun x := by simp
        _ = 1 := pX.sum_one
  }

/-- `assemble` projection (pointwise formula). -/
@[simp] lemma assemble_toFun (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) (x : X) (θ : Θ) :
    (assemble pX pΘ_givenX).toFun (x, θ) = pX.toFun x * (pΘ_givenX x).toFun θ := rfl

/-- Marginalizing an assembled joint recovers the original marginal `pX`. -/
theorem marginalX_assemble (pX : FinProb X) (pΘ_givenX : X → FinProb Θ) :
    marginalX (assemble pX pΘ_givenX) = pX := by
  apply FinProb.ext
  intro x
  -- unfold `marginalX`/`assemble` first, then do the algebra explicitly
  dsimp [marginalX, assemble]
  rw [← Finset.mul_sum, sum_eq_one, mul_one]

/-- Bayes posterior from factorized prior `q(θ) q(x | θ)` after observing `x0`. -/
noncomputable def bayesPosterior
    (qΘ : FinProb Θ) (qX_givenΘ : Θ → FinProb X) (x0 : X)
    (hZ : 0 < (∑ θ : Θ, qΘ.toFun θ * (qX_givenΘ θ).toFun x0)) : FinProb Θ := by
  classical
  let w : Θ → ℝ := fun θ => qΘ.toFun θ * (qX_givenΘ θ).toFun x0
  have hw : ∀ θ, 0 ≤ w θ := by
    intro θ
    exact mul_nonneg (qΘ.nonneg θ) ((qX_givenΘ θ).nonneg x0)
  exact normalize w hw hZ

variable [DecidableEq X]

/-- Bayes joint posterior: `p(x, θ) = δ_{x0}(x) * p(θ)`. -/
noncomputable def bayesJoint
    (qΘ : FinProb Θ) (qX_givenΘ : Θ → FinProb X) (x0 : X)
    (hZ : 0 < (∑ θ : Θ, qΘ.toFun θ * (qX_givenΘ θ).toFun x0)) : FinProb (X × Θ) :=
  assemble (dirac x0) (fun _x => bayesPosterior qΘ qX_givenΘ x0 hZ)

/-- Jeffrey joint update: replace `x`-marginal by `pX`, preserve `q(θ | x)`. -/
noncomputable def jeffreyJoint
    (q : FinProb (X × Θ)) (pX : FinProb X)
    (hx : ∀ x, 0 < (marginalX q).toFun x) : FinProb (X × Θ) :=
  assemble pX (fun x => condΘGivenX q x (hx x))

/-- Factorized prior joint `q(θ) q(x | θ)`. -/
noncomputable def factorizedJoint
    (qΘ : FinProb Θ) (qX_givenΘ : Θ → FinProb X) : FinProb (X × Θ) := by
  classical
  refine {
    toFun := fun xt => qΘ.toFun xt.2 * (qX_givenΘ xt.2).toFun xt.1,
    nonneg := by
      intro xt
      exact mul_nonneg (qΘ.nonneg xt.2) ((qX_givenΘ xt.2).nonneg xt.1),
    sum_one := by
      calc
        (∑ z : X × Θ, qΘ.toFun z.2 * (qX_givenΘ z.2).toFun z.1)
          = ∑ x : X, ∑ θ : Θ, qΘ.toFun θ * (qX_givenΘ θ).toFun x := by
            rw [← Fintype.sum_prod_type']
        _ = ∑ θ : Θ, ∑ x : X, qΘ.toFun θ * (qX_givenΘ θ).toFun x := by rw [Finset.sum_comm]
        _ = ∑ θ : Θ, qΘ.toFun θ * (∑ x : X, (qX_givenΘ θ).toFun x) := by
            congr 1
            funext θ
            rw [Finset.mul_sum]
        _ = ∑ θ : Θ, qΘ.toFun θ * 1 := by simp
        _ = ∑ θ : Θ, qΘ.toFun θ := by simp
        _ = 1 := qΘ.sum_one
  }

/-! ME characterization interfaces (finite case). -/

/-- KL chain-rule decomposition on finite products. -/
def KL_chain_rule
    (p q : FinProb (X × Θ))
    (hq : ∀ x : X, 0 < (marginalX q).toFun x)
    (hp : ∀ x : X, 0 < (marginalX p).toFun x) : Prop :=
  KL p q
    =
    KL (marginalX p) (marginalX q)
      +
    (∑ x : X, (marginalX p).toFun x *
      KL (condΘGivenX p x (hp x)) (condΘGivenX q x (hq x)))

/-- Jeffrey update is ME under fixed `x`-marginal constraint. -/
def jeffrey_is_ME
    (q : FinProb (X × Θ)) (pX : FinProb X)
    (hq : ∀ x : X, 0 < (marginalX q).toFun x) : Prop :=
  ∀ p : Joint, marginalX p = pX →
    Entropy p q ≤ Entropy (jeffreyJoint q pX hq) q

/-- Bayes update is ME under hard-data marginal constraint `p(x)=δ_{x0}`. -/
def bayes_is_ME
    (qΘ : FinProb Θ) (qX_givenΘ : Θ → FinProb X) (x0 : X)
    (hZ : 0 < (∑ θ : Θ, qΘ.toFun θ * (qX_givenΘ θ).toFun x0)) : Prop :=
  ∀ p : Joint, marginalX p = dirac x0 →
    Entropy p (factorizedJoint qΘ qX_givenΘ)
      ≤ Entropy (bayesJoint qΘ qX_givenΘ x0 hZ) (factorizedJoint qΘ qX_givenΘ)

end BayesJeffreyFinite

end InfoGeometry.EntropicInference
