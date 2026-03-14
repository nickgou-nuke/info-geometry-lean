import InfoGeometry.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# InfoGeometry.Canonical.IBCore

Canonical core for the Information Bottleneck finite scaffold.
Rebased entirely onto the `PMF` (FinProb) foundation, using monadic
operations and `PMF.normalize` for mathematically rigorous marginalizations.
-/

open scoped BigOperators ENNReal NNReal

namespace InfoGeometry.Canonical.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]

/-- Draft IB problem package. -/
structure IBProblem where
  pXY : FinProb (X × Y)
  beta : ℝ
  beta_pos : 0 < beta

/-- `Y` is inhabited whenever an `IBProblem` exists. -/
private theorem nonemptyY (prob : IBProblem (X := X) (Y := Y)) : Nonempty Y := by
  have h_supp := prob.pXY.support_nonempty
  rcases h_supp with ⟨xy, _⟩
  exact ⟨xy.2⟩

/-! ### Monadic Probability Manipulations -/

/-- Marginal p(x). -/
noncomputable def marginal_x (prob : IBProblem (X := X) (Y := Y)) : FinProb X :=
  prob.pXY.map Prod.fst

/-- Induced joint distribution p(y,t) = ∑_x p(x,y) p(t|x). -/
noncomputable def jointYT (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : FinProb (Y × T) :=
  prob.pXY.bind (fun (x, y) => (pT_givenX x).map (fun t => (y, t)))

/-- Induced marginal q(t). -/
noncomputable def inducedMarginalT (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : FinProb T :=
  (jointYT prob pT_givenX).map Prod.snd

/-- Joint distribution p(x,t) = p(x) p(t|x). -/
noncomputable def jointXT (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : FinProb (X × T) :=
  (marginal_x prob).bind (fun x => (pT_givenX x).map (fun t => (x, t)))

/-- Independent coupling p(A)p(B). -/
noncomputable def independentCoupling {A B : Type*} (pA : FinProb A) (pB : FinProb B) :
    FinProb (A × B) :=
  pA.bind (fun a => pB.map (fun b => (a, b)))

/-! ### Finiteness Helpers for PMF Normalization -/

/-- Summing finitely many finite values in ℝ≥0∞ yields a finite value. -/
private lemma tsum_ne_top_of_fintype
    {A : Type*} [Fintype A] (f : A → ℝ≥0∞) (hf : ∀ a, f a ≠ ⊤) :
    (∑' a, f a) ≠ ⊤ := by
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr (fun a _ => hf a)

/-- Any single probability mass is strictly less than infinity. -/
private lemma pmf_val_ne_top {A : Type*} (p : FinProb A) (a : A) : p a ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one p a) ENNReal.one_lt_top)

/-- The unnormalized conditional slice has finite total mass. -/
private lemma cond_slice_ne_top
    (prob : IBProblem (X := X) (Y := Y)) (x : X) :
    (∑' y, prob.pXY (x, y)) ≠ ⊤ := by
  apply tsum_ne_top_of_fintype
  intro y
  exact pmf_val_ne_top prob.pXY (x, y)

/-- The unnormalized induced posterior slice has finite total mass. -/
private lemma jointYT_slice_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (t : T) :
    (∑' y, jointYT prob pT_givenX (y, t)) ≠ ⊤ := by
  apply tsum_ne_top_of_fintype
  intro y
  exact pmf_val_ne_top (jointYT prob pT_givenX) (y, t)

/-! ### Conditionals and Projections via Normalization -/

/-- Conditional $p(y|x)$. -/
noncomputable def condYGivenX (prob : IBProblem (X := X) (Y := Y)) (x : X) : FinProb Y := by
  classical
  let f : Y → ℝ≥0∞ := fun y => prob.pXY (x, y)
  by_cases h0 : (∑' y, f y) = 0
  · let _ : Nonempty Y := nonemptyY prob
    exact PMF.pure (Classical.arbitrary Y)
  · exact PMF.normalize f h0 (cond_slice_ne_top prob x)

/-- Induced Bayesian projection $m(y|t) = p(y,t) / q(t)$. -/
noncomputable def inducedMProjection (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : T → FinProb Y := by
  classical
  intro t
  let pYT := jointYT prob pT_givenX
  let f : Y → ℝ≥0∞ := fun y => pYT (y, t)
  by_cases h0 : (∑' y, f y) = 0
  · let _ : Nonempty Y := nonemptyY prob
    exact PMF.pure (Classical.arbitrary Y)
  · exact PMF.normalize f h0 (jointYT_slice_ne_top prob pT_givenX t)

/-! ### Information Bottleneck Functionals -/

section InformationTheory

variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

/-- Generic Mutual Information defined strictly via canonical KL divergence. -/
noncomputable def mutualInformation {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (pAB : FinProb (A × B)) : ℝ :=
  let pA := pAB.map Prod.fst
  let pB := pAB.map Prod.snd
  (InfoGeometry.fin_kl_div pAB (independentCoupling pA pB)).toReal

/-- Local definition of Shannon Entropy for the Lagrangian Constant. -/
noncomputable def entropy {A : Type*} [Fintype A] (p : FinProb A) : ℝ :=
  - ∑ a : A, (p a).toReal * Real.log (p a).toReal

/-- The IB Lagrangian: $L(p, β) = I(X;T) - β I(Y;T)$. -/
noncomputable def ibLagrangian (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : ℝ :=
  mutualInformation (jointXT prob pT_givenX) -
  prob.beta * mutualInformation (jointYT prob pT_givenX)

/-- The IB variational functional:
$F(p, m, β) = I(X;T) + β \sum_x p(x) KL(p(y|x) || \sum_t p(t|x) m(y|t))$. -/
noncomputable def ibVariationalFunctional (prob : IBProblem (X := X) (Y := Y))
  (pT_givenX : X → FinProb T) (mY_givenT : T → FinProb Y) : ℝ :=
  let pX := marginal_x prob
  let pXT := jointXT prob pT_givenX
  mutualInformation pXT +
    prob.beta * (∑ x : X, (pX x).toReal *
      (InfoGeometry.fin_kl_div (condYGivenX prob x) ((pT_givenX x).bind mY_givenT)).toReal)

/-- IB Lagrangian constant: $H(Y|X)$. -/
noncomputable def ibLagrangianConstant (prob : IBProblem (X := X) (Y := Y)) : ℝ :=
  let pX := marginal_x prob
  ∑ x : X, (pX x).toReal * entropy (condYGivenX prob x)

/-! ### Blahut-Arimoto Dynamics (Finite Canonical Step) -/

/--
Unnormalized Blahut-Arimoto score
`q(t) * exp(-β * KL(p(y|x) || m(y|t)))` in `ℝ≥0∞`.
-/
noncomputable def baScore
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) : T → ℝ≥0∞ := fun t =>
  let qT := inducedMarginalT prob pT_givenX
  let mY_givenT := inducedMProjection prob pT_givenX
  qT t * ENNReal.ofReal
    (Real.exp
      (-prob.beta *
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal))

private lemma baScore_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) (t : T) :
    baScore prob pT_givenX x t ≠ ⊤ := by
  dsimp [baScore]
  refine ENNReal.mul_ne_top ?_ ?_
  · exact pmf_val_ne_top (inducedMarginalT prob pT_givenX) t
  · simp

private lemma baScore_slice_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    (∑' t, baScore prob pT_givenX x t) ≠ ⊤ := by
  apply tsum_ne_top_of_fintype
  intro t
  exact baScore_ne_top prob pT_givenX x t

/--
One canonical finite Blahut-Arimoto update step for `p(t|x)`, implemented via
normalization of the BA score.
-/
noncomputable def ibBlahutArimotoStep
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : X → FinProb T := by
  classical
  intro x
  let f : T → ℝ≥0∞ := baScore prob pT_givenX x
  by_cases h0 : (∑' t, f t) = 0
  · have hSupp : (pT_givenX x).support.Nonempty := (pT_givenX x).support_nonempty
    exact PMF.pure (Classical.choose hSupp)
  · exact PMF.normalize f h0 (baScore_slice_ne_top prob pT_givenX x)

/-- Fixed-point predicate for the canonical finite Blahut-Arimoto update. -/
def ibBlahutArimotoFixedPoint
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : Prop :=
  ibBlahutArimotoStep prob pT_givenX = pT_givenX

/--
Canonical IB iterate trajectory generated by recursive Blahut-Arimoto updates
from an initial encoder `p0`.
-/
noncomputable def ibTrajectory
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T) : Nat → X → FinProb T
  | 0 => p0
  | k + 1 => ibBlahutArimotoStep prob (ibTrajectory prob p0 k)

@[simp] theorem ibTrajectory_zero
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T) :
    ibTrajectory prob p0 0 = p0 := rfl

@[simp] theorem ibTrajectory_succ
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T) (k : Nat) :
    ibTrajectory prob p0 (k + 1) = ibBlahutArimotoStep prob (ibTrajectory prob p0 k) := rfl

/--
The recursive IB trajectory is exactly the iterate sequence of the one-step
Blahut-Arimoto map.
-/
@[simp] theorem ibTrajectory_eq_iterate
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T) (k : Nat) :
    ibTrajectory prob p0 k = (ibBlahutArimotoStep prob)^[k] p0 := by
  induction k with
  | zero =>
      simp [ibTrajectory]
  | succ k hk =>
      simp [ibTrajectory, Function.iterate_succ_apply', hk]

/--
Existence of an explicit total IB trajectory satisfying the BA recursion.
-/
theorem exists_ibTrajectory
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T) :
    ∃ pTrajectory : Nat → X → FinProb T,
      pTrajectory 0 = p0 ∧
      (∀ k : Nat, pTrajectory (k + 1) = ibBlahutArimotoStep prob (pTrajectory k)) := by
  refine ⟨ibTrajectory prob p0, rfl, ?_⟩
  intro k
  rfl

/--
Contraction-driven convergence of the IB trajectory.

This is the Banach fixed-point closure for the canonical BA recursion:
once `ibBlahutArimotoStep` is shown contracting on the encoder space,
the generated IB trajectory converges to a unique fixed point.
-/
theorem pTrajectory_eq_iterate_of_step
    (prob : IBProblem (X := X) (Y := Y))
    (pTrajectory : Nat → X → FinProb T)
    (hStep :
      ∀ k : Nat,
        pTrajectory (k + 1)
          = ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob (pTrajectory k)) :
    ∀ n : Nat,
      pTrajectory n
        = (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)^[n] (pTrajectory 0) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [hStep, ih]
      simp [Function.iterate_succ_apply']

/--
Constructive contraction packaging:
`K < 1` plus a Lipschitz witness for the BA step map yields `ContractingWith K`.
-/
theorem ibBlahutArimotoStep_contracting_of_lipschitz
    [EMetricSpace (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : NNReal}
    (hK : Kc < 1)
    (hLip : LipschitzWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)) :
    ContractingWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob) := by
  exact ⟨hK, hLip⟩

/--
Banach fixed-point convergence for arbitrary BA-recursive trajectories.

Given a strict contraction witness for `ibBlahutArimotoStep prob` on a complete
encoder metric space, every trajectory satisfying the BA recursion converges to
the unique fixed point.
-/
theorem tendsto_ibTrajectory_fixedPoint
    [MetricSpace (X → FinProb T)]
    [CompleteSpace (X → FinProb T)]
    [Nonempty (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    (pTrajectory : Nat → X → FinProb T)
    (hStep :
      ∀ k : Nat,
        pTrajectory (k + 1)
          = ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob (pTrajectory k))
    {Kc : NNReal}
    (hContr :
      ContractingWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)) :
    ∃ p_star : X → FinProb T,
      Filter.Tendsto pTrajectory Filter.atTop (nhds p_star) ∧
      ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p_star = p_star := by
  let p_star :=
    ContractingWith.fixedPoint (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob) hContr
  have hiter :
      ∀ n : Nat,
        pTrajectory n
          = (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)^[n] (pTrajectory 0) :=
    pTrajectory_eq_iterate_of_step (prob := prob) (pTrajectory := pTrajectory) hStep
  have htend :
      Filter.Tendsto
        (fun n => (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)^[n] (pTrajectory 0))
        Filter.atTop (nhds p_star) := by
    simpa [p_star] using
      (ContractingWith.tendsto_iterate_fixedPoint
        (f := ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)
        (hf := hContr) (pTrajectory 0))
  have hEq :
      pTrajectory =
        (fun n => (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)^[n] (pTrajectory 0)) := by
    funext n
    exact hiter n
  refine ⟨p_star, ?_, ?_⟩
  · exact hEq ▸ htend
  · simpa [p_star] using
      (ContractingWith.fixedPoint_isFixedPt
        (f := ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob) (hf := hContr))

/--
Contraction-driven convergence of the canonical recursively defined IB trajectory.
-/
theorem tendsto_ibTrajectory_fixedPoint_of_contracting
    [MetricSpace (X → FinProb T)]
    [CompleteSpace (X → FinProb T)]
    [Nonempty (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T)
    (F : (X → FinProb T) → (X → FinProb T))
    (hF : F = ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)
    {Kc : NNReal}
    (hContr : ContractingWith Kc F) :
    ∃ p_star : X → FinProb T,
      Filter.Tendsto (ibTrajectory prob p0) Filter.atTop (nhds p_star) ∧
      ibBlahutArimotoStep prob p_star = p_star := by
  subst hF
  simpa using
    (tendsto_ibTrajectory_fixedPoint
      (prob := prob)
      (pTrajectory := ibTrajectory prob p0)
      (hStep := ibTrajectory_succ (prob := prob) (p0 := p0))
      (hContr := hContr))

/--
Lipschitz-driven convergence route:
if one proves the BA step map is `K`-Lipschitz with `K < 1`, Banach closure
follows immediately for the canonical IB trajectory.
-/
theorem tendsto_ibTrajectory_fixedPoint_of_lipschitz
    [MetricSpace (X → FinProb T)]
    [CompleteSpace (X → FinProb T)]
    [Nonempty (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T)
    {Kc : NNReal}
    (hK : Kc < 1)
    (hLip : LipschitzWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)) :
    ∃ p_star : X → FinProb T,
      Filter.Tendsto (ibTrajectory prob p0) Filter.atTop (nhds p_star) ∧
      ibBlahutArimotoStep prob p_star = p_star := by
  exact tendsto_ibTrajectory_fixedPoint_of_contracting
    (prob := prob) (p0 := p0)
    (F := ibBlahutArimotoStep prob) (hF := rfl)
    (hContr := ibBlahutArimotoStep_contracting_of_lipschitz
      (prob := prob) hK hLip)

/--
KL Lyapunov functional with a frozen BA target:
`p ↦ ∑ₓ KL(p(·|x) || BA[p_anchor](·|x))`.
-/
noncomputable def baFrozenTargetGap
    (prob : IBProblem (X := X) (Y := Y))
    (pAnchor p : X → FinProb T) : ℝ :=
  ∑ x : X, (InfoGeometry.fin_kl_div (p x) ((ibBlahutArimotoStep prob pAnchor) x)).toReal

/-- Nonnegativity of the frozen-target KL Lyapunov functional. -/
lemma baFrozenTargetGap_nonneg
    (prob : IBProblem (X := X) (Y := Y))
    (pAnchor p : X → FinProb T) :
    0 ≤ baFrozenTargetGap prob pAnchor p := by
  unfold baFrozenTargetGap
  refine Finset.sum_nonneg ?_
  intro x hx
  exact ENNReal.toReal_nonneg

/--
Frozen-target gap vanishes when evaluated at the BA updated policy.
-/
theorem baFrozenTargetGap_step_eq_zero
    (prob : IBProblem (X := X) (Y := Y))
    (pOld : X → FinProb T) :
    baFrozenTargetGap prob pOld (ibBlahutArimotoStep prob pOld) = 0 := by
  unfold baFrozenTargetGap
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hkl :
      InfoGeometry.fin_kl_div
        ((ibBlahutArimotoStep prob pOld) x)
        ((ibBlahutArimotoStep prob pOld) x) = 0 := by
    unfold InfoGeometry.fin_kl_div InfoGeometry.kl_div
    simpa using
      (InformationTheory.klDiv_self
        (μ := (((ibBlahutArimotoStep prob pOld) x).toMeasure)))
  simpa [hkl]

/--
Constructive one-step BA descent (frozen-target form):
after one BA update, the frozen-target KL gap is minimized to `0`, hence
it is no larger than its pre-update value.
-/
theorem ibBlahutArimotoStep_descent_frozenTarget
    (prob : IBProblem (X := X) (Y := Y))
    (pOld : X → FinProb T) :
    baFrozenTargetGap prob pOld (ibBlahutArimotoStep prob pOld)
      ≤ baFrozenTargetGap prob pOld pOld := by
  have hzero :
      baFrozenTargetGap prob pOld (ibBlahutArimotoStep prob pOld) = 0 :=
    baFrozenTargetGap_step_eq_zero (prob := prob) (pOld := pOld)
  rw [hzero]
  exact baFrozenTargetGap_nonneg (prob := prob) (pAnchor := pOld) (p := pOld)

end InformationTheory

end InfoGeometry.Canonical.IB
