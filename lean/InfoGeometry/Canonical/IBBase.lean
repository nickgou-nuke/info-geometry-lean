import InfoGeometry.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.KL.Finite
import InfoGeometry.MaxEnt.IProjection
import InfoGeometry.Measure.Normalized

/-!
# InfoGeometry.Canonical.IBBase

Foundational finite Information Bottleneck data:
- joint and conditional laws
- induced marginals and projections
- mutual-information and variational objectives
- frozen BA score and its finiteness properties
-/

open scoped BigOperators ENNReal NNReal

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

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
lemma pmf_val_ne_top {A : Type*} (p : FinProb A) (a : A) : p a ≠ ⊤ := by
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

/-! ### Blahut-Arimoto Dynamics (Frozen Target Score) -/

/--
Frozen-target BA score with explicit target `(qT, mY_givenT)`.
-/
noncomputable def baScoreFrozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) : T → ℝ≥0∞ := fun t =>
  qT t * ENNReal.ofReal
    (Real.exp
      (-prob.beta *
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal))

lemma baScoreFrozen_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) (t : T) :
    baScoreFrozen prob qT mY_givenT x t ≠ ⊤ := by
  dsimp [baScoreFrozen]
  refine ENNReal.mul_ne_top ?_ ?_
  · exact pmf_val_ne_top qT t
  · simp

lemma baScoreFrozen_slice_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    (∑' t, baScoreFrozen prob qT mY_givenT x t) ≠ ⊤ := by
  apply tsum_ne_top_of_fintype
  intro t
  exact baScoreFrozen_ne_top prob qT mY_givenT x t

lemma baScoreFrozen_slice_ne_zero
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    (∑' t, baScoreFrozen prob qT mY_givenT x t) ≠ 0 := by
  classical
  rcases qT.support_nonempty with ⟨t0, ht0⟩
  have hq_nonzero : qT t0 ≠ 0 := by
    exact (qT.mem_support_iff t0).1 ht0
  have hscore_pos : 0 < baScoreFrozen prob qT mY_givenT x t0 := by
    dsimp [baScoreFrozen]
    refine ENNReal.mul_pos ?_ ?_
    · exact hq_nonzero
    · exact ENNReal.ofReal_ne_zero_iff.2 (Real.exp_pos _)
  have hle :
      baScoreFrozen prob qT mY_givenT x t0 ≤ ∑' t, baScoreFrozen prob qT mY_givenT x t := by
    rw [tsum_fintype]
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ t0)
  exact ne_of_gt (lt_of_lt_of_le hscore_pos hle)

/--
Local frozen finiteness regime for a fixed slice `x`.
This prevents `ENNReal.toReal` collapse (`toReal ⊤ = 0`) in Gibbs identities.
-/
def FrozenFiniteRegime
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) : Prop :=
  InfoGeometry.fin_kl_div (pT_givenX x) qT ≠ ⊤ ∧
  ∀ t : T, (pT_givenX x) t ≠ 0 →
    InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t) ≠ ⊤

lemma FrozenFiniteRegime.fin_kl_div_encoder_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (hFin : FrozenFiniteRegime prob pT_givenX qT mY_givenT x) :
    InfoGeometry.fin_kl_div (pT_givenX x) qT ≠ ⊤ :=
  hFin.1

lemma FrozenFiniteRegime.fin_kl_div_cond_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (hFin : FrozenFiniteRegime prob pT_givenX qT mY_givenT x)
    (t : T)
    (ht : (pT_givenX x) t ≠ 0) :
    InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t) ≠ ⊤ :=
  hFin.2 t ht

lemma FrozenFiniteRegime.ofReal_toReal_fin_kl_div_encoder
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (hFin : FrozenFiniteRegime prob pT_givenX qT mY_givenT x) :
    ENNReal.ofReal ((InfoGeometry.fin_kl_div (pT_givenX x) qT).toReal)
      = InfoGeometry.fin_kl_div (pT_givenX x) qT := by
  exact ENNReal.ofReal_toReal (hFin.fin_kl_div_encoder_ne_top
    (prob := prob) (pT_givenX := pT_givenX) (qT := qT) (mY_givenT := mY_givenT) (x := x))

lemma FrozenFiniteRegime.ofReal_toReal_fin_kl_div_cond
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (hFin : FrozenFiniteRegime prob pT_givenX qT mY_givenT x)
    (t : T)
    (ht : (pT_givenX x) t ≠ 0) :
    ENNReal.ofReal ((InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)
      = InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t) := by
  exact ENNReal.ofReal_toReal (hFin.fin_kl_div_cond_ne_top
    (prob := prob) (pT_givenX := pT_givenX) (qT := qT) (mY_givenT := mY_givenT)
    (x := x) (t := t) ht)

/--
Log-partition function for the frozen BA score.
-/
noncomputable def logPartitionFrozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) : ℝ :=
  Real.log ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal)

lemma baScoreFrozen_slice_toReal_pos
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    0 < ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal) := by
  exact ENNReal.toReal_pos
    (baScoreFrozen_slice_ne_zero prob qT mY_givenT x)
    (baScoreFrozen_slice_ne_top prob qT mY_givenT x)

end InformationTheory

end InfoGeometry.Canonical.IB
