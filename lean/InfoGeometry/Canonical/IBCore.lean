import InfoGeometry.Basic
import InfoGeometry.MaxEnt.IProjection
import InfoGeometry.Measure.Normalized
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

private lemma baScoreFrozen_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) (t : T) :
    baScoreFrozen prob qT mY_givenT x t ≠ ⊤ := by
  dsimp [baScoreFrozen]
  refine ENNReal.mul_ne_top ?_ ?_
  · exact pmf_val_ne_top qT t
  · simp

private lemma baScoreFrozen_slice_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    (∑' t, baScoreFrozen prob qT mY_givenT x t) ≠ ⊤ := by
  apply tsum_ne_top_of_fintype
  intro t
  exact baScoreFrozen_ne_top prob qT mY_givenT x t

private lemma baScoreFrozen_slice_ne_zero
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

section FrozenJaynes

variable [DecidableEq T]

/--
Finite Jaynes slice induced by the frozen IB target at fixed `x`.
-/
noncomputable def frozenSliceJaynes
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) : InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem T Unit := by
  classical
  exact
    { prior := qT
      index := {()}
      feature := fun _ t =>
        -prob.beta * (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
      target := fun _ => 0 }

lemma frozenSliceJaynes_fullSupportPrior
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    (frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x).FullSupportPrior := by
  intro t
  simpa [frozenSliceJaynes] using hq t

lemma frozenSliceJaynes_partition_one_ne_zero
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    (frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x).partition
      (fun _ : Unit => (1 : ℝ)) ≠ 0 := by
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  have hprior : J.FullSupportPrior := by
    intro t
    simpa [J, frozenSliceJaynes] using hq t
  haveI : Nonempty T := by
    rcases qT.support_nonempty with ⟨t0, ht0⟩
    exact ⟨t0⟩
  exact J.partition_ne_zero_of_fullSupport hprior (fun _ : Unit => (1 : ℝ))

lemma frozenSlice_partition_eq_baScoreFrozen_tsum_toReal
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    J.partition lam = ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal) := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  calc
    J.partition lam
        = ∑ t : T, (qT t).toReal *
            Real.exp
              (-prob.beta *
                (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal) := by
            simp [J, lam, frozenSliceJaynes,
              InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.partition,
              InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.energy]
    _ = ∑ t : T, (baScoreFrozen prob qT mY_givenT x t).toReal := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          unfold baScoreFrozen
          rw [ENNReal.toReal_mul]
          rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
    _ = ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal) := by
          rw [tsum_fintype, ENNReal.toReal_sum]
          intro t ht
          exact baScoreFrozen_ne_top prob qT mY_givenT x t

lemma frozenSlice_logPartition_eq_logPartitionFrozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X) :
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    J.logPartition lam = logPartitionFrozen prob qT mY_givenT x := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  have hpart : J.partition lam = ((∑' t, baScoreFrozen prob qT mY_givenT x t).toReal) := by
    simpa [J, lam] using
      (frozenSlice_partition_eq_baScoreFrozen_tsum_toReal
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x)
  simpa [J, lam, hpart, InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.logPartition, logPartitionFrozen]

/--
Local frozen free-energy identity in Jaynes variational form (single slice `x`).
-/
lemma frozenSlice_local_free_energy_identity_sum
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (p_x : FinProb T)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    let hZ : J.partition lam ≠ 0 :=
      frozenSliceJaynes_partition_one_ne_zero
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
    (InfoGeometry.fin_kl_div p_x qT).toReal +
      prob.beta * ∑ t : T, (p_x t).toReal *
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
    =
      (∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t))
        - J.logPartition lam := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  let hZ : J.partition lam ≠ 0 :=
    frozenSliceJaynes_partition_one_ne_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hprior : J.FullSupportPrior := by
    intro t
    simpa [J, frozenSliceJaynes] using hq t
  have hvar := J.kl_gibbs_variational_identity hprior lam hZ p_x
  have hKLq :
      (InfoGeometry.fin_kl_div p_x qT).toReal
        = ∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / (J.prior t).toReal) := by
    simpa [J, frozenSliceJaynes] using
      (InfoGeometry.MaxEnt.IProjection.toReal_klDiv_eq_sum_log_ratio
        (P := p_x) (Q := qT) hq)
  have hMoment :
      (∑ i ∈ J.index, lam i * J.moment p_x (J.feature i))
        =
      -prob.beta * ∑ t : T, (p_x t).toReal *
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal := by
    calc
      (∑ i ∈ J.index, lam i * J.moment p_x (J.feature i))
          = ∑ i ∈ ({()} : Finset Unit), lam i * J.moment p_x (J.feature i) := by
              simp [J, frozenSliceJaynes]
      _ = J.moment p_x (J.feature ()) := by
              simp [lam]
      _ =
          -prob.beta * ∑ t : T, (p_x t).toReal *
            (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal := by
              unfold InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.moment
              calc
                (∑ t : T, (p_x t).toReal * J.feature () t)
                    = ∑ t : T, (p_x t).toReal *
                        (-prob.beta *
                          (InfoGeometry.fin_kl_div (condYGivenX prob x)
                            (mY_givenT t)).toReal) := by
                          simp [J, frozenSliceJaynes]
                _ = ∑ t : T, -prob.beta * ((p_x t).toReal *
                      (InfoGeometry.fin_kl_div (condYGivenX prob x)
                        (mY_givenT t)).toReal) := by
                      refine Finset.sum_congr rfl ?_
                      intro t ht
                      ring
                _ =
                    -prob.beta * ∑ t : T, (p_x t).toReal *
                      (InfoGeometry.fin_kl_div (condYGivenX prob x)
                        (mY_givenT t)).toReal := by
                      simpa using (Finset.mul_sum (s := (Finset.univ : Finset T))
                        (f := fun t : T => (p_x t).toReal *
                          (InfoGeometry.fin_kl_div (condYGivenX prob x)
                            (mY_givenT t)).toReal)
                        (a := -prob.beta)).symm
  rw [← hKLq, hMoment] at hvar
  linarith

/--
Local frozen free-energy identity as KL-to-Gibbs minus log-partition.
-/
lemma local_free_energy_identity
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (p_x : FinProb T)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    let hZ : J.partition lam ≠ 0 :=
      frozenSliceJaynes_partition_one_ne_zero
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
    (InfoGeometry.fin_kl_div p_x qT).toReal +
      prob.beta * ∑ t : T, (p_x t).toReal *
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
    =
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
        - J.logPartition lam := by
  classical
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  let hZ : J.partition lam ≠ 0 :=
    frozenSliceJaynes_partition_one_ne_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hsum :
      (InfoGeometry.fin_kl_div p_x qT).toReal +
        prob.beta * ∑ t : T, (p_x t).toReal *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
      =
        (∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t))
          - J.logPartition lam := by
    simpa [J, lam, hZ] using
      (frozenSlice_local_free_energy_identity_sum
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x p_x hq)
  have hGibbsFull : ∀ t : T, 0 < ((J.gibbsDist lam hZ t).toReal) := by
    intro t
    rw [J.gibbsDist_pointwise]
    unfold InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsProb
    unfold InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsWeight
    have hZnonneg : 0 ≤ J.partition lam := J.partition_nonneg lam
    have hZpos : 0 < J.partition lam := lt_of_le_of_ne hZnonneg (Ne.symm hZ)
    exact div_pos (mul_pos (hq t) (Real.exp_pos _)) hZpos
  have hKLg :
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
        = ∑ t : T, (p_x t).toReal *
            Real.log ((p_x t).toReal / ((J.gibbsDist lam hZ) t).toReal) := by
    simpa using
      (InfoGeometry.MaxEnt.IProjection.toReal_klDiv_eq_sum_log_ratio
        (P := p_x) (Q := J.gibbsDist lam hZ) hGibbsFull)
  have hKLg' :
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
        = ∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t) := by
    calc
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
          = ∑ t : T, (p_x t).toReal *
              Real.log ((p_x t).toReal / ((J.gibbsDist lam hZ) t).toReal) := hKLg
      _ = ∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            simp [J.gibbsDist_pointwise]
  calc
    (InfoGeometry.fin_kl_div p_x qT).toReal +
        prob.beta * ∑ t : T, (p_x t).toReal *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
        =
      (∑ t : T, (p_x t).toReal * Real.log ((p_x t).toReal / J.gibbsProb lam hZ t))
        - J.logPartition lam := hsum
    _ =
      (InfoGeometry.fin_kl_div p_x (J.gibbsDist lam hZ)).toReal
        - J.logPartition lam := by
          rw [hKLg']

end FrozenJaynes

/--
`PMF.normalize` is invariant under positive finite global rescaling of the score.

This is the local projective-ray/Weyl-gauge invariance statement for finite PMFs.
-/
lemma pmf_normalize_eq_of_scale
    (f : T → ℝ≥0∞)
    (hf0 : (∑' t, f t) ≠ 0)
    (hfTop : (∑' t, f t) ≠ ⊤)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcTop : c ≠ ⊤) :
    PMF.normalize
      (fun t => c * f t)
      (by
        simpa [ENNReal.tsum_mul_left] using
          (mul_ne_zero hc0 hf0))
      (by
        rw [ENNReal.tsum_mul_left]
        exact ENNReal.mul_ne_top hcTop hfTop)
      = PMF.normalize f hf0 hfTop := by
  ext t
  rw [PMF.normalize_apply, PMF.normalize_apply]
  calc
    c * f t * (∑' x, c * f x)⁻¹
        = (c * f t) / (∑' x, c * f x) := by
            rw [div_eq_mul_inv]
    _ = (c * f t) / (c * ∑' x, f x) := by
          rw [ENNReal.tsum_mul_left]
    _ = f t / (∑' x, f x) := by
          simpa using ENNReal.mul_div_mul_left
            (a := f t) (b := (∑' x, f x)) (c := c) hc0 hcTop
    _ = f t * (∑' x, f x)⁻¹ := by
          rw [div_eq_mul_inv]

/--
`toReal` pointwise formula for `PMF.normalize`.
-/
lemma pmf_normalize_apply_toReal
    (f : T → ℝ≥0∞)
    (hf0 : (∑' t, f t) ≠ 0)
    (hfTop : (∑' t, f t) ≠ ⊤)
    (t : T) :
    ((PMF.normalize f hf0 hfTop t).toReal)
      = (f t).toReal * ((∑' x, f x).toReal)⁻¹ := by
  rw [PMF.normalize_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]

/--
Two score functions lie on the same positive projective ray.
-/
def SameScoreRay (f g : T → ℝ≥0∞) : Prop :=
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ g = fun t => c * f t

lemma SameScoreRay.refl (f : T → ℝ≥0∞) :
    SameScoreRay (T := T) f f := by
  refine ⟨1, one_ne_zero, ENNReal.one_ne_top, ?_⟩
  funext t
  simp

lemma SameScoreRay.symm {f g : T → ℝ≥0∞}
    (h : SameScoreRay (T := T) f g) :
    SameScoreRay (T := T) g f := by
  rcases h with ⟨c, hc0, hcTop, rfl⟩
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hcTop, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  funext t
  have hmul : c⁻¹ * (c * f t) = f t := by
    calc
      c⁻¹ * (c * f t) = (c⁻¹ * c) * f t := by ac_rfl
      _ = 1 * f t := by rw [ENNReal.inv_mul_cancel hc0 hcTop]
      _ = f t := by simp
  simpa [mul_assoc] using hmul.symm

lemma SameScoreRay.trans {f g h : T → ℝ≥0∞}
    (hfg : SameScoreRay (T := T) f g)
    (hgh : SameScoreRay (T := T) g h) :
    SameScoreRay (T := T) f h := by
  rcases hfg with ⟨c₁, hc₁0, hc₁Top, hg⟩
  rcases hgh with ⟨c₂, hc₂0, hc₂Top, hh⟩
  refine ⟨c₂ * c₁, mul_ne_zero hc₂0 hc₁0, ENNReal.mul_ne_top hc₂Top hc₁Top, ?_⟩
  funext t
  rw [hh, hg]
  simp [mul_assoc, mul_comm, mul_left_comm]

instance sameScoreRaySetoid : Setoid (T → ℝ≥0∞) where
  r := SameScoreRay (T := T)
  iseqv := by
    refine ⟨SameScoreRay.refl (T := T), ?_, ?_⟩
    · intro f g hfg
      exact SameScoreRay.symm (T := T) hfg
    · intro f g h hfg hgh
      exact SameScoreRay.trans (T := T) hfg hgh

/--
Radial (volume-changing) degree of an unnormalized score: total slice mass.
-/
noncomputable def scoreRayDegree (f : T → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t, f t

/--
Projective (volume-preserving) gauge section of an unnormalized score.
-/
noncomputable def scoreProjectiveGauge
    (f : T → ℝ≥0∞)
    (hf0 : scoreRayDegree (T := T) f ≠ 0)
    (hfTop : scoreRayDegree (T := T) f ≠ ⊤) : FinProb T :=
  PMF.normalize f hf0 hfTop

/--
Normalization depends only on the projective ray of the score.
-/
lemma pmf_normalize_eq_of_sameScoreRay
    {f g : T → ℝ≥0∞}
    (hRay : SameScoreRay (T := T) f g)
    (hf0 : (∑' t, f t) ≠ 0)
    (hfTop : (∑' t, f t) ≠ ⊤)
    (hg0 : (∑' t, g t) ≠ 0)
    (hgTop : (∑' t, g t) ≠ ⊤) :
    PMF.normalize g hg0 hgTop = PMF.normalize f hf0 hfTop := by
  rcases hRay with ⟨c, hc0, hcTop, rfl⟩
  have h0eq :
      hg0 =
        (by
          simpa [ENNReal.tsum_mul_left] using
            (mul_ne_zero hc0 hf0)) := by
    exact Subsingleton.elim _ _
  have hTopeq :
      hgTop =
        (by
          rw [ENNReal.tsum_mul_left]
          exact ENNReal.mul_ne_top hcTop hfTop) := by
    exact Subsingleton.elim _ _
  cases h0eq
  cases hTopeq
  exact pmf_normalize_eq_of_scale
    (T := T) f hf0 hfTop c hc0 hcTop

/-- Dilation rescales score-ray degree multiplicatively. -/
lemma scoreRayDegree_scale
    (f : T → ℝ≥0∞)
    (c : ℝ≥0∞) :
    scoreRayDegree (T := T) (fun t => c * f t)
      = c * scoreRayDegree (T := T) f := by
  unfold scoreRayDegree
  rw [ENNReal.tsum_mul_left]

/--
Projective gauge is invariant on score rays.
-/
lemma scoreProjectiveGauge_eq_of_sameScoreRay
    {f g : T → ℝ≥0∞}
    (hRay : SameScoreRay (T := T) f g)
    (hf0 : scoreRayDegree (T := T) f ≠ 0)
    (hfTop : scoreRayDegree (T := T) f ≠ ⊤)
    (hg0 : scoreRayDegree (T := T) g ≠ 0)
    (hgTop : scoreRayDegree (T := T) g ≠ ⊤) :
    scoreProjectiveGauge (T := T) g hg0 hgTop
      = scoreProjectiveGauge (T := T) f hf0 hfTop := by
  exact pmf_normalize_eq_of_sameScoreRay
    (T := T) hRay hf0 hfTop hg0 hgTop

/--
Finite nonzero score slice: a concrete representative of a projective score ray.
-/
structure ScoreSlice where
  f : T → ℝ≥0∞
  nonzero : scoreRayDegree (T := T) f ≠ 0
  finite : scoreRayDegree (T := T) f ≠ ⊤

instance scoreSliceSetoid : Setoid (ScoreSlice (T := T)) where
  r s₁ s₂ := SameScoreRay (T := T) s₁.f s₂.f
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      exact SameScoreRay.refl (T := T) s.f
    · intro s₁ s₂ h
      exact SameScoreRay.symm (T := T) h
    · intro s₁ s₂ s₃ h₁₂ h₂₃
      exact SameScoreRay.trans (T := T) h₁₂ h₂₃

/-- Projective score-ray state space (unnormalized cone modulo positive scaling). -/
abbrev ScoreRay : Type := Quotient (scoreSliceSetoid (T := T))

namespace ScoreSlice

/-- Canonical PMF gauge section attached to a concrete nonzero finite score slice. -/
noncomputable def gaugeSection (s : ScoreSlice (T := T)) : FinProb T :=
  scoreProjectiveGauge (T := T) s.f s.nonzero s.finite

end ScoreSlice

namespace ScoreRay

/-- Canonical PMF gauge section attached to a projective score ray class. -/
noncomputable def gaugeSection : ScoreRay (T := T) → FinProb T :=
  Quotient.lift
    (fun s : ScoreSlice (T := T) => s.gaugeSection)
    (by
      intro s₁ s₂ hs
      exact scoreProjectiveGauge_eq_of_sameScoreRay
        (T := T)
        hs
        s₁.nonzero s₁.finite
        s₂.nonzero s₂.finite |> Eq.symm)

@[simp] theorem gaugeSection_mk (s : ScoreSlice (T := T)) :
    gaugeSection (T := T) (Quotient.mk (scoreSliceSetoid (T := T)) s) = s.gaugeSection := rfl

end ScoreRay

/--
Radial/projective factorization for any finite nonzero score slice.
-/
lemma score_radial_projective_factorization
    (f : T → ℝ≥0∞)
    (hf0 : scoreRayDegree (T := T) f ≠ 0)
    (hfTop : scoreRayDegree (T := T) f ≠ ⊤)
    (t : T) :
    scoreRayDegree (T := T) f
      * (scoreProjectiveGauge (T := T) f hf0 hfTop t)
      = f t := by
  unfold scoreRayDegree scoreProjectiveGauge
  rw [PMF.normalize_apply]
  have hcancel : (∑' x, f x) * (∑' x, f x)⁻¹ = 1 := by
    simpa [scoreRayDegree] using (ENNReal.mul_inv_cancel hf0 hfTop)
  calc
    (∑' x, f x) * (f t * (∑' x, f x)⁻¹)
        = f t * ((∑' x, f x) * (∑' x, f x)⁻¹) := by ac_rfl
    _ = f t * 1 := by rw [hcancel]
    _ = f t := by simp

/--
Normalization of an already normalized finite law is proof-irrelevant and
returns the same PMF.
-/
lemma pmf_normalize_eq_self
    (p : FinProb T) :
    PMF.normalize
      (fun t => p t)
      (by
        classical
        rcases p.support_nonempty with ⟨t0, ht0⟩
        have hp0 : p t0 ≠ 0 := by
          exact (p.mem_support_iff t0).1 ht0
        have hpPos : 0 < p t0 := by
          exact bot_lt_iff_ne_bot.mpr hp0
        have hle : p t0 ≤ ∑' t, p t := by
          rw [tsum_fintype]
          exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ t0)
        exact ne_of_gt (lt_of_lt_of_le hpPos hle))
      p.tsum_coe_ne_top = p := by
  ext t
  have hsum : (∑ t, p t) = (1 : ℝ≥0∞) := by
    simpa [tsum_fintype] using p.tsum_coe
  simp [PMF.normalize_apply, hsum]

/--
Frozen-target normalized BA step.
-/
noncomputable def ibBlahutArimotoStepFrozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y) : X → FinProb T := by
  classical
  intro x
  exact PMF.normalize
    (baScoreFrozen prob qT mY_givenT x)
    (baScoreFrozen_slice_ne_zero prob qT mY_givenT x)
    (baScoreFrozen_slice_ne_top prob qT mY_givenT x)

/--
If the frozen distortion term is uniform in `t` at a fixed slice `x`, the BA
update collapses to the frozen prior `qT`.

Interpretation: along this symmetry-flat slice there is no nontrivial
optimization direction after projective normalization.
-/
theorem ibBlahutArimotoStepFrozen_eq_prior_of_uniformDistortion
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (d : ℝ)
    (hUniform :
      ∀ t : T,
        (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal = d) :
    ibBlahutArimotoStepFrozen prob qT mY_givenT x = qT := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-prob.beta * d))
  have hc0 : c ≠ 0 := by
    have hcpos : 0 < c := by
      exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
    exact ne_of_gt hcpos
  have hcTop : c ≠ ⊤ := by
    simp [c]
  have hscore :
      ∀ t : T, baScoreFrozen prob qT mY_givenT x t = qT t * c := by
    intro t
    unfold baScoreFrozen
    simpa [c, hUniform t, mul_assoc, mul_left_comm, mul_comm]
  have hsum :
      (∑' t, baScoreFrozen prob qT mY_givenT x t) = c := by
    calc
      (∑' t, baScoreFrozen prob qT mY_givenT x t)
          = ∑' t, qT t * c := by
              refine tsum_congr ?_
              intro t
              exact hscore t
      _ = (∑' t, qT t) * c := by
            simpa using (ENNReal.tsum_mul_right (f := fun t => qT t) (a := c))
      _ = c := by
            rw [qT.tsum_coe, one_mul]
  ext t
  unfold ibBlahutArimotoStepFrozen
  rw [PMF.normalize_apply]
  calc
    baScoreFrozen prob qT mY_givenT x t
        * (∑' t', baScoreFrozen prob qT mY_givenT x t')⁻¹
      = (qT t * c) * c⁻¹ := by
          rw [hscore t, hsum]
    _ = qT t * (c * c⁻¹) := by
          ac_rfl
    _ = qT t * 1 := by
          rw [ENNReal.mul_inv_cancel hc0 hcTop]
    _ = qT t := by simp

/--
Slice-wise projective/Weyl invariance of the frozen BA update:
rescaling the frozen score by a positive finite factor does not change the
normalized update.
-/
lemma ibBlahutArimotoStepFrozen_slice_eq_of_score_scale
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (x : X)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcTop : c ≠ ⊤) :
    PMF.normalize
      (fun t => c * baScoreFrozen prob qT mY_givenT x t)
      (by
        simpa [ENNReal.tsum_mul_left] using
          (mul_ne_zero hc0 (baScoreFrozen_slice_ne_zero prob qT mY_givenT x)))
      (by
        rw [ENNReal.tsum_mul_left]
        exact ENNReal.mul_ne_top hcTop (baScoreFrozen_slice_ne_top prob qT mY_givenT x))
      =
    ibBlahutArimotoStepFrozen prob qT mY_givenT x := by
  simpa [ibBlahutArimotoStepFrozen] using
    (pmf_normalize_eq_of_scale
      (T := T)
      (f := baScoreFrozen prob qT mY_givenT x)
      (hf0 := baScoreFrozen_slice_ne_zero prob qT mY_givenT x)
      (hfTop := baScoreFrozen_slice_ne_top prob qT mY_givenT x)
      (c := c) hc0 hcTop)

/--
Full frozen-step projective/Weyl invariance:
for any positive finite per-slice scaling `κ(x)`, the normalized BA update is unchanged.
-/
theorem ibBlahutArimotoStepFrozen_eq_of_score_ray_scale
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (κ : X → ℝ≥0∞)
    (hκ0 : ∀ x : X, κ x ≠ 0)
    (hκTop : ∀ x : X, κ x ≠ ⊤) :
    (fun x =>
      PMF.normalize
        (fun t => κ x * baScoreFrozen prob qT mY_givenT x t)
        (by
          simpa [ENNReal.tsum_mul_left] using
            (mul_ne_zero (hκ0 x) (baScoreFrozen_slice_ne_zero prob qT mY_givenT x)))
        (by
          rw [ENNReal.tsum_mul_left]
          exact ENNReal.mul_ne_top (hκTop x) (baScoreFrozen_slice_ne_top prob qT mY_givenT x)))
      =
    ibBlahutArimotoStepFrozen prob qT mY_givenT := by
  funext x
  exact ibBlahutArimotoStepFrozen_slice_eq_of_score_scale
    (X := X) (Y := Y) (T := T) prob qT mY_givenT x (κ x) (hκ0 x) (hκTop x)

/--
The standard unnormalized Blahut-Arimoto score, recovered by passing the
induced self-consistent marginal and projection into the frozen formulation.
-/
noncomputable def baScore
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : X → T → ℝ≥0∞ :=
  baScoreFrozen prob
    (inducedMarginalT prob pT_givenX)
    (inducedMProjection prob pT_givenX)

private lemma baScore_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) (t : T) :
    baScore prob pT_givenX x t ≠ ⊤ := by
  simpa [baScore] using
    baScoreFrozen_ne_top
      (prob := prob)
      (qT := inducedMarginalT prob pT_givenX)
      (mY_givenT := inducedMProjection prob pT_givenX)
      (x := x) (t := t)

private lemma baScore_slice_ne_top
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    (∑' t, baScore prob pT_givenX x t) ≠ ⊤ := by
  simpa [baScore] using
    baScoreFrozen_slice_ne_top
      (prob := prob)
      (qT := inducedMarginalT prob pT_givenX)
      (mY_givenT := inducedMProjection prob pT_givenX)
      (x := x)

/--
The BA score mass is strictly positive (hence nonzero): one can pick a support
point of `qT = inducedMarginalT prob pT_givenX`, and the exponential factor in
`baScore` is always strictly positive.
-/
private lemma baScore_slice_ne_zero
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    (∑' t, baScore prob pT_givenX x t) ≠ 0 := by
  simpa [baScore] using
    baScoreFrozen_slice_ne_zero
      (prob := prob)
      (qT := inducedMarginalT prob pT_givenX)
      (mY_givenT := inducedMProjection prob pT_givenX)
      (x := x)

/--
The standard canonical BA update, recovered as a pure specialization of the
frozen step.
-/
noncomputable def ibBlahutArimotoStep
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : X → FinProb T :=
  ibBlahutArimotoStepFrozen prob
    (inducedMarginalT prob pT_givenX)
    (inducedMProjection prob pT_givenX)

/--
Primary BA object: the unnormalized score field (projective ray representative).
-/
noncomputable def ibBlahutArimotoStepUnnormalized
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : X → T → ℝ≥0∞ :=
  baScore prob pT_givenX

/--
Canonical BA score slice as a finite nonzero representative in the unnormalized cone.
-/
noncomputable def ibBlahutArimotoScoreSlice
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) : ScoreSlice (T := T) where
  f := ibBlahutArimotoStepUnnormalized prob pT_givenX x
  nonzero := baScore_slice_ne_zero prob pT_givenX x
  finite := baScore_slice_ne_top prob pT_givenX x

/--
Canonical BA score ray (projective unnormalized state) at each slice `x`.
-/
noncomputable def ibBlahutArimotoScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) : X → ScoreRay (T := T) :=
  fun x => Quotient.mk (scoreSliceSetoid (T := T))
    (ibBlahutArimotoScoreSlice prob pT_givenX x)

/--
If BA unnormalized scores are slice-wise on the same projective ray, BA score rays coincide.
-/
theorem ibBlahutArimotoScoreRay_eq_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay : ∀ x : X, SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q := by
  funext x
  apply Quotient.sound
  simpa [ibBlahutArimotoScoreSlice, ibBlahutArimotoStepUnnormalized] using hRay x

/--
Radial degree (volume-changing part) of the BA unnormalized score at a slice.
-/
noncomputable def ibBlahutArimotoStepDegree
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) : ℝ≥0∞ :=
  scoreRayDegree (T := T) (ibBlahutArimotoStepUnnormalized prob pT_givenX x)

/--
When the BA score mass is nonzero, the BA step is exactly the normalization
of the BA score.
-/
lemma ibBlahutArimotoStep_apply_eq_normalize
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X)
    (h0 : (∑' t, baScore prob pT_givenX x t) ≠ 0) :
    ibBlahutArimotoStep prob pT_givenX x
      = PMF.normalize (baScore prob pT_givenX x) h0
          (baScoreFrozen_slice_ne_top prob _ _ x) := by
  have hproof :
      h0 = baScoreFrozen_slice_ne_zero prob
        (inducedMarginalT prob pT_givenX)
        (inducedMProjection prob pT_givenX) x := by
    exact Subsingleton.elim _ _
  cases hproof
  rfl

/--
The normalized BA update is exactly the projective gauge-fixing of the
unnormalized BA score.
-/
lemma ibBlahutArimotoStep_eq_scoreProjectiveGauge
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) (x : X) :
    ibBlahutArimotoStep prob pT_givenX x
      =
    scoreProjectiveGauge (T := T)
      (ibBlahutArimotoStepUnnormalized prob pT_givenX x)
      (baScore_slice_ne_zero prob pT_givenX x)
      (baScore_slice_ne_top prob pT_givenX x) := by
  simpa [scoreProjectiveGauge, ibBlahutArimotoStepUnnormalized] using
    (ibBlahutArimotoStep_apply_eq_normalize
      (X := X) (Y := Y) (T := T) prob pT_givenX x
      (baScore_slice_ne_zero prob pT_givenX x))

/--
BA normalization is exactly the gauge section of the BA score ray.
-/
lemma ibBlahutArimotoStep_eq_scoreRayGaugeSection
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    ibBlahutArimotoStep prob pT_givenX x
      = ScoreRay.gaugeSection (T := T) (ibBlahutArimotoScoreRay prob pT_givenX x) := by
  simp [ibBlahutArimotoScoreRay, ibBlahutArimotoScoreSlice,
    ScoreSlice.gaugeSection, ibBlahutArimotoStep_eq_scoreProjectiveGauge]

/--
Normalized BA updates are derived from score rays: equality of BA score-ray maps
implies equality of BA normalized updates.
-/
theorem ibBlahutArimotoStep_eq_of_scoreRay_eq
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q) :
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q := by
  funext x
  have hx :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p x
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q x := by
    simpa using congrArg (fun F => F x) hRay
  calc
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p x
        = ScoreRay.gaugeSection (T := T)
            (ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p x) :=
          ibBlahutArimotoStep_eq_scoreRayGaugeSection
            (X := X) (Y := Y) (T := T) prob p x
    _ = ScoreRay.gaugeSection (T := T)
          (ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q x) := by
          simpa [hx]
    _ = ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q x := by
          symm
          exact ibBlahutArimotoStep_eq_scoreRayGaugeSection
            (X := X) (Y := Y) (T := T) prob q x

/--
Global BA update equality from slice-wise score-ray equivalence.
This is the canonical corollary: PMF-level equality is derived from ray-level equality.
-/
theorem ibBlahutArimotoStep_eq_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay : ∀ x : X, SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q := by
  exact ibBlahutArimotoStep_eq_of_scoreRay_eq
    (X := X) (Y := Y) (T := T) prob p q
    (ibBlahutArimotoScoreRay_eq_of_sameScoreRay
      (X := X) (Y := Y) (T := T) prob p q hRay)

/--
Slice-wise radial/projective decomposition of BA:
unnormalized score = degree × normalized projective representative.
-/
theorem ibBlahutArimotoStep_radial_projective_split
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) (t : T) :
    ibBlahutArimotoStepDegree prob pT_givenX x
      * (ibBlahutArimotoStep prob pT_givenX x t)
      =
    ibBlahutArimotoStepUnnormalized prob pT_givenX x t := by
  unfold ibBlahutArimotoStepDegree
  rw [ibBlahutArimotoStep_eq_scoreProjectiveGauge (X := X) (Y := Y) (T := T) prob pT_givenX x]
  exact score_radial_projective_factorization
    (T := T)
    (f := ibBlahutArimotoStepUnnormalized prob pT_givenX x)
    (hf0 := baScore_slice_ne_zero prob pT_givenX x)
    (hfTop := baScore_slice_ne_top prob pT_givenX x)
    t

/--
Intrinsic BA projective invariance under positive finite per-slice dilations of
the unnormalized score.
-/
theorem ibBlahutArimotoStep_eq_of_score_ray_scale
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (κ : X → ℝ≥0∞)
    (hκ0 : ∀ x : X, κ x ≠ 0)
    (hκTop : ∀ x : X, κ x ≠ ⊤) :
    (fun x =>
      PMF.normalize
        (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
        (by
          simpa [ibBlahutArimotoStepUnnormalized, ENNReal.tsum_mul_left] using
            (mul_ne_zero (hκ0 x) (baScore_slice_ne_zero prob pT_givenX x)))
        (by
          rw [ENNReal.tsum_mul_left]
          simpa [ibBlahutArimotoStepUnnormalized] using
            (ENNReal.mul_ne_top (hκTop x) (baScore_slice_ne_top prob pT_givenX x))))
      = ibBlahutArimotoStep prob pT_givenX := by
  funext x
  rw [ibBlahutArimotoStep_eq_scoreProjectiveGauge (X := X) (Y := Y) (T := T) prob pT_givenX x]
  exact pmf_normalize_eq_of_scale
    (T := T)
    (f := ibBlahutArimotoStepUnnormalized prob pT_givenX x)
    (hf0 := baScore_slice_ne_zero prob pT_givenX x)
    (hfTop := baScore_slice_ne_top prob pT_givenX x)
    (c := κ x) (hκ0 x) (hκTop x)

/--
Cartan-style split under BA-score dilations:
radial degree scales multiplicatively, projective BA update is invariant.
-/
theorem ibBlahutArimotoStep_dilation_split
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (κ : X → ℝ≥0∞)
    (hκ0 : ∀ x : X, κ x ≠ 0)
    (hκTop : ∀ x : X, κ x ≠ ⊤) :
    (∀ x : X,
      scoreRayDegree (T := T)
        (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
          = κ x * ibBlahutArimotoStepDegree prob pT_givenX x)
    ∧
    ((fun x =>
      PMF.normalize
        (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
        (by
          simpa [ibBlahutArimotoStepUnnormalized, ENNReal.tsum_mul_left] using
            (mul_ne_zero (hκ0 x) (baScore_slice_ne_zero prob pT_givenX x)))
        (by
          rw [ENNReal.tsum_mul_left]
          simpa [ibBlahutArimotoStepUnnormalized] using
            (ENNReal.mul_ne_top (hκTop x) (baScore_slice_ne_top prob pT_givenX x))))
      = ibBlahutArimotoStep prob pT_givenX) := by
  refine ⟨?_, ?_⟩
  · intro x
    unfold ibBlahutArimotoStepDegree
    simpa [ibBlahutArimotoStepUnnormalized] using
      scoreRayDegree_scale
        (T := T)
        (f := ibBlahutArimotoStepUnnormalized prob pT_givenX x)
        (c := κ x)
  · exact ibBlahutArimotoStep_eq_of_score_ray_scale
      (X := X) (Y := Y) (T := T) prob pT_givenX κ hκ0 hκTop

section MeasureProjectiveBridge

variable [Nonempty T]

/--
Canonical BA slice as a measure-projective ray class.
This keeps the ontology at ray level, with normalization only as section choice.
-/
noncomputable def ibBlahutArimotoProjectiveState
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) :
    X → InfoGeometry.MeasureProjective.ProjectiveState T :=
  fun x =>
    InfoGeometry.MeasureProjective.Normalized.pmfToProjectiveState
      (ibBlahutArimotoStep prob pT_givenX x)

/--
Slice equality of BA updates under score-ray equivalence.
-/
lemma ibBlahutArimotoStep_slice_eq_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (x : X)
    (hRay : SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ibBlahutArimotoStep prob p x = ibBlahutArimotoStep prob q x := by
  have hp :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = PMF.normalize
            (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (ibBlahutArimotoStep_apply_eq_normalize
        (X := X) (Y := Y) (T := T) prob p x
        (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x))
  have hq :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x
        = PMF.normalize
            (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x) := by
    simpa using
      (ibBlahutArimotoStep_apply_eq_normalize
        (X := X) (Y := Y) (T := T) prob q x
        (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x))
  have hnorm :
      PMF.normalize
          (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)
        =
      PMF.normalize
          (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (pmf_normalize_eq_of_sameScoreRay
        (T := T)
        (hRay := hRay)
        (hf0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
        (hfTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x)
        (hg0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
        (hgTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
  rw [hp, hq]
  exact hnorm.symm

/--
Global BA projective-state invariance under slice-wise score-ray equivalence.
-/
theorem ibBlahutArimotoProjectiveState_eq_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay : ∀ x : X, SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob q := by
  funext x
  have hstep :
      ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p x
        = ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q x :=
    ibBlahutArimotoStep_slice_eq_of_sameScoreRay
      (X := X) (Y := Y) (T := T) prob p q x (hRay x)
  simpa [ibBlahutArimotoProjectiveState, hstep]

/--
Projective BA state equality derived directly from equality of BA score-ray maps.
-/
theorem ibBlahutArimotoProjectiveState_eq_of_scoreRay_eq
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q) :
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob p
      =
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob q := by
  have hstep :
      ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p
        =
      ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q :=
    ibBlahutArimotoStep_eq_of_scoreRay_eq
      (X := X) (Y := Y) (T := T) prob p q hRay
  funext x
  simpa [ibBlahutArimotoProjectiveState] using
    congrArg InfoGeometry.MeasureProjective.Normalized.pmfToProjectiveState
      (congrArg (fun F => F x) hstep)

/--
BA projective-state invariance under positive finite score dilations.
-/
theorem ibBlahutArimotoProjectiveState_eq_of_score_ray_scale
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (κ : X → ℝ≥0∞)
    (hκ0 : ∀ x : X, κ x ≠ 0)
    (hκTop : ∀ x : X, κ x ≠ ⊤) :
    (fun x =>
      InfoGeometry.MeasureProjective.Normalized.pmfToProjectiveState
        (PMF.normalize
          (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
          (by
            simpa [ibBlahutArimotoStepUnnormalized, ENNReal.tsum_mul_left] using
              (mul_ne_zero (hκ0 x) (baScore_slice_ne_zero prob pT_givenX x)))
          (by
            rw [ENNReal.tsum_mul_left]
            simpa [ibBlahutArimotoStepUnnormalized] using
              (ENNReal.mul_ne_top (hκTop x) (baScore_slice_ne_top prob pT_givenX x)))))
      =
    ibBlahutArimotoProjectiveState (X := X) (Y := Y) (T := T) prob pT_givenX := by
  funext x
  have hscale :=
    ibBlahutArimotoStep_eq_of_score_ray_scale
      (X := X) (Y := Y) (T := T) prob pT_givenX κ hκ0 hκTop
  have hx :
      PMF.normalize
          (fun t => κ x * ibBlahutArimotoStepUnnormalized prob pT_givenX x t)
          (by
            simpa [ibBlahutArimotoStepUnnormalized, ENNReal.tsum_mul_left] using
              (mul_ne_zero (hκ0 x) (baScore_slice_ne_zero prob pT_givenX x)))
          (by
            rw [ENNReal.tsum_mul_left]
            simpa [ibBlahutArimotoStepUnnormalized] using
              (ENNReal.mul_ne_top (hκTop x) (baScore_slice_ne_top prob pT_givenX x)))
        = ibBlahutArimotoStep prob pT_givenX x := by
    simpa using congrArg (fun f => f x) hscale
  simpa [ibBlahutArimotoProjectiveState] using
    congrArg InfoGeometry.MeasureProjective.Normalized.pmfToProjectiveState hx

end MeasureProjectiveBridge

/--
The intrinsic BA score is the frozen score specialized to induced target data.
-/
@[simp] lemma baScore_eq_baScoreFrozen_induced
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T)
    (x : X) :
    baScore prob pT_givenX x
      = baScoreFrozen prob (inducedMarginalT prob pT_givenX) (inducedMProjection prob pT_givenX) x := rfl

/--
The intrinsic BA step is the frozen-target normalized step specialized to
induced target data.
-/
lemma ibBlahutArimotoStep_eq_frozen_induced
    (prob : IBProblem (X := X) (Y := Y))
    (pT_givenX : X → FinProb T) :
    ibBlahutArimotoStep prob pT_givenX
      = ibBlahutArimotoStepFrozen prob (inducedMarginalT prob pT_givenX) (inducedMProjection prob pT_givenX) := rfl

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

/-! ### Concrete Sup-Metric Contraction Reductions -/

/--
Concrete finite sup metric on `FinProb T`, using pointwise masses in `ℝ≥0∞`.
-/
noncomputable def finProbMassNndist
    (p q : FinProb T) : ℝ≥0 :=
  Finset.sup Finset.univ (fun t => nndist (p t).toReal (q t).toReal)

/--
Pointwise mass-distance is bounded by the finite sup metric on `FinProb T`.
-/
lemma nndist_eval_le_finProbMassNndist
    (p q : FinProb T) (t : T) :
    nndist (p t).toReal (q t).toReal ≤ finProbMassNndist (T := T) p q := by
  unfold finProbMassNndist
  exact Finset.le_sup
    (s := Finset.univ)
    (f := fun t : T => nndist (p t).toReal (q t).toReal)
    (Finset.mem_univ t)

/--
Concrete encoder sup metric obtained by taking finite sup over `x` of
`finProbMassNndist` on each conditional law `p(·|x)`.
-/
noncomputable def encoderMassNndist
    (p q : X → FinProb T) : ℝ≥0 :=
  Finset.sup Finset.univ (fun x => finProbMassNndist (T := T) (p x) (q x))

/--
Pointwise encoder slice distance is bounded by encoder sup metric.
-/
lemma finProbMassNndist_eval_le_encoderMassNndist
    (p q : X → FinProb T) (x : X) :
    finProbMassNndist (T := T) (p x) (q x) ≤ encoderMassNndist (X := X) (T := T) p q := by
  unfold encoderMassNndist
  exact Finset.le_sup
    (s := Finset.univ)
    (f := fun x : X => finProbMassNndist (T := T) (p x) (q x))
    (Finset.mem_univ x)

/--
Intrinsic normalize stability under projective score-ray equivalence:
if two BA scores at slice `x` lie on the same positive ray, their normalized
updates coincide, hence the mass-sup distance vanishes (`K = 0`).
-/
theorem ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay : ∀ x : X, SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ (0 : ℝ≥0) * finProbMassNndist (T := T) (p x) (q x) := by
  intro x
  have hp :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = PMF.normalize
            (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (ibBlahutArimotoStep_apply_eq_normalize
        (X := X) (Y := Y) (T := T) prob p x
        (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x))
  have hq :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x
        = PMF.normalize
            (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x) := by
    simpa using
      (ibBlahutArimotoStep_apply_eq_normalize
        (X := X) (Y := Y) (T := T) prob q x
        (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x))
  have hnorm :
      PMF.normalize
          (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)
        =
      PMF.normalize
          (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (pmf_normalize_eq_of_sameScoreRay
        (T := T)
        (hRay := hRay x)
        (hf0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
        (hfTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x)
        (hg0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
        (hgTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
  have hstep :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x := by
    rw [hp, hq]
    exact hnorm.symm
  have hdist :
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        = 0 := by
    simpa [hstep, finProbMassNndist]
  simpa [hdist]

/--
Concrete contraction lift in the explicit mass sup metric:
pointwise contraction on each `x` implies global contraction on encoders.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_of_pointwise
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hPointwise :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
          ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderMassNndist (X := X) (T := T) p q := by
  intro p q
  unfold encoderMassNndist
  refine Finset.sup_le ?_
  intro x hx
  calc
    finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ Kc * finProbMassNndist (T := T) (p x) (q x) := hPointwise p q x
    _ ≤ Kc * Finset.sup Finset.univ
          (fun x => finProbMassNndist (T := T) (p x) (q x)) := by
      have hsup :
          finProbMassNndist (T := T) (p x) (q x) ≤
            Finset.sup Finset.univ (fun x => finProbMassNndist (T := T) (p x) (q x)) := by
        exact Finset.le_sup
          (s := Finset.univ)
          (f := fun x : X => finProbMassNndist (T := T) (p x) (q x))
          (Finset.mem_univ x)
      exact mul_le_mul_of_nonneg_left hsup Kc.2

/--
Global encoder contraction under slice-wise score-ray equivalence (`K = 0`).
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_zero_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (hRay :
      ∀ p q : X → FinProb T, ∀ x : X,
        SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ (0 : ℝ≥0) * encoderMassNndist (X := X) (T := T) p q := by
  exact ibBlahutArimotoStep_encoderMassNndist_le_of_pointwise
    (X := X) (Y := Y) (T := T) (prob := prob) (Kc := 0)
    (hPointwise := by
      intro p q x
      exact ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_sameScoreRay
        (X := X) (Y := Y) (T := T) prob p q (fun x' => hRay p q x') x)

/--
Pointwise zero-contraction corollary driven directly by BA score-ray map equality.
-/
theorem ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_scoreRay_eq
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q) :
    ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ (0 : ℝ≥0) * finProbMassNndist (T := T) (p x) (q x) := by
  intro x
  have hstep :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x := by
    simpa using congrArg (fun F => F x)
      (ibBlahutArimotoStep_eq_of_scoreRay_eq
        (X := X) (Y := Y) (T := T) prob p q hRay)
  have hdist :
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        = 0 := by
    simpa [hstep, finProbMassNndist]
  simpa [hdist]

/--
Global zero-contraction corollary driven directly by BA score-ray map equality.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_zero_of_scoreRay_eq
    (prob : IBProblem (X := X) (Y := Y))
    (p q : X → FinProb T)
    (hRay :
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob p
        =
      ibBlahutArimotoScoreRay (X := X) (Y := Y) (T := T) prob q) :
    encoderMassNndist (X := X) (T := T)
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
      ≤ (0 : ℝ≥0) * encoderMassNndist (X := X) (T := T) p q := by
  unfold encoderMassNndist
  refine Finset.sup_le ?_
  intro x hx
  calc
    finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ (0 : ℝ≥0) * finProbMassNndist (T := T) (p x) (q x) :=
      ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_scoreRay_eq
        (X := X) (Y := Y) (T := T) prob p q hRay x
    _ = 0 := by simp
    _ = (0 : ℝ≥0) * encoderMassNndist (X := X) (T := T) p q := by simp

/--
Pointwise BA contraction reduction:
it is enough to prove the contraction estimate after rewriting BA updates as
normalizations of BA scores (under nonzero score mass).
-/
theorem ibBlahutArimotoStep_pointwise_massNndist_le_of_normalize
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hNonzero :
      ∀ p : X → FinProb T, ∀ x : X,
        (∑' t, baScore prob p x t) ≠ 0)
    (hNormalize :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x) (hNonzero p x) (baScore_slice_ne_top prob p x))
          (PMF.normalize (baScore prob q x) (hNonzero q x) (baScore_slice_ne_top prob q x))
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x) := by
  intro p q x
  have hp :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x
        = PMF.normalize (baScore prob p x) (hNonzero p x) (baScore_slice_ne_top prob p x) := by
    simpa using ibBlahutArimotoStep_apply_eq_normalize (X := X) (Y := Y) (T := T) prob p x (hNonzero p x)
  have hq :
      (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x
        = PMF.normalize (baScore prob q x) (hNonzero q x) (baScore_slice_ne_top prob q x) := by
    simpa using ibBlahutArimotoStep_apply_eq_normalize (X := X) (Y := Y) (T := T) prob q x (hNonzero q x)
  simpa [hp, hq] using hNormalize p q x

/--
Global BA contraction reduction in the explicit mass sup metric:
combine the normalize-form pointwise estimate with finite-sup lifting.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_of_normalize
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hNonzero :
      ∀ p : X → FinProb T, ∀ x : X,
        (∑' t, baScore prob p x t) ≠ 0)
    (hNormalize :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x) (hNonzero p x) (baScore_slice_ne_top prob p x))
          (PMF.normalize (baScore prob q x) (hNonzero q x) (baScore_slice_ne_top prob q x))
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderMassNndist (X := X) (T := T) p q := by
  exact ibBlahutArimotoStep_encoderMassNndist_le_of_pointwise
    (X := X) (Y := Y) (T := T) prob
    (hPointwise :=
      ibBlahutArimotoStep_pointwise_massNndist_le_of_normalize
        (X := X) (Y := Y) (T := T) prob hNonzero hNormalize)

/--
Pointwise BA contraction reduction with intrinsic nonzero-score discharge:
only the normalize-form estimate remains as an external analytic obligation.
-/
theorem ibBlahutArimotoStep_pointwise_massNndist_le_of_normalize_intrinsicNonzero
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hNormalize :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x))
          (PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x))
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x) := by
  intro p q x
  simpa [ibBlahutArimotoStep] using hNormalize p q x

/--
Internal normalize-form zero-contraction witness:
slice-wise score-ray equivalence implies the normalize inequality with `K = 0`.
-/
theorem baNormalize_pointwise_massNndist_le_zero_of_sameScoreRay
    (prob : IBProblem (X := X) (Y := Y))
    (hRay :
      ∀ p q : X → FinProb T, ∀ x : X,
        SameScoreRay (T := T) (baScore prob p x) (baScore prob q x)) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        (PMF.normalize (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x))
        (PMF.normalize (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
        ≤ (0 : ℝ≥0) * finProbMassNndist (T := T) (p x) (q x) := by
  intro p q x
  have hnorm :
      PMF.normalize (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)
        =
      PMF.normalize (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x) := by
    simpa using
      (pmf_normalize_eq_of_sameScoreRay
        (T := T)
        (hRay := hRay p q x)
        (hf0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
        (hfTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x)
        (hg0 := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
        (hgTop := baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
  have hdist :
      finProbMassNndist (T := T)
        (PMF.normalize (baScore prob p x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x))
        (PMF.normalize (baScore prob q x)
          (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
          (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
        = 0 := by
    have hnorm' :
        PMF.normalize (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x)
          =
        PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x) := hnorm.symm
    have hrewrite :
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x))
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
          =
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)) := by
      exact congrArg
        (fun r =>
          finProbMassNndist (T := T) r
            (PMF.normalize (baScore prob q x)
              (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
              (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)))
        hnorm'
    calc
      finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob p x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob p x))
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
          =
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x))
          (PMF.normalize (baScore prob q x)
            (baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob q x)
            (baScore_slice_ne_top (X := X) (Y := Y) (T := T) prob q x)) := by
              exact hrewrite
      _ = 0 := by simp [finProbMassNndist]
  simpa [hdist]

/--
General normalize-Lipschitz estimate (nonzero `Kc`) under explicit lower-mass
control on score slices.

The bound is driven by:
- slice mass lower bound (`m`)
- pointwise score Lipschitz (`Kscore`)
- reciprocal-mass Lipschitz (`Kinv`)
- pointwise score upper bound (`ub`)
-/
theorem baNormalize_pointwise_massNndist_le_of_massRecipLipschitz
    (prob : IBProblem (X := X) (Y := Y))
    {m Kscore Kinv ub : ℝ}
    (Kc : ℝ≥0)
    (hm : 0 < m)
    (hKscore_nonneg : 0 ≤ Kscore)
    (hKinv_nonneg : 0 ≤ Kinv)
    (hKc : (Kc : ℝ) = Kscore / m + ub * Kinv)
    (hMassLower :
      ∀ p : X → FinProb T, ∀ x : X,
        m ≤ ((∑' t, baScore prob p x t).toReal))
    (hScoreUpper :
      ∀ p : X → FinProb T, ∀ x : X, ∀ t : T,
        (baScore prob p x t).toReal ≤ ub)
    (hScoreLip :
      ∀ p q : X → FinProb T, ∀ x : X, ∀ t : T,
        |(baScore prob p x t).toReal - (baScore prob q x t).toReal|
          ≤ Kscore * ((finProbMassNndist (T := T) (p x) (q x) : ℝ)))
    (hMassInvLip :
      ∀ p q : X → FinProb T, ∀ x : X,
        |((∑' t, baScore prob p x t).toReal)⁻¹
            - ((∑' t, baScore prob q x t).toReal)⁻¹|
          ≤ Kinv * ((finProbMassNndist (T := T) (p x) (q x) : ℝ))) :
    ∀ p q : X → FinProb T, ∀ x : X,
      finProbMassNndist (T := T)
        (PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x))
        (PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x))
        ≤ Kc * (finProbMassNndist (T := T) (p x) (q x)) := by
  intro p q x
  let d : ℝ := (finProbMassNndist (T := T) (p x) (q x) : ℝ)
  have hd_nonneg : 0 ≤ d := by
    exact (show 0 ≤ (finProbMassNndist (T := T) (p x) (q x) : ℝ≥0) from (finProbMassNndist (T := T) (p x) (q x)).2)
  unfold finProbMassNndist
  refine Finset.sup_le ?_
  intro t ht
  have hdist_nndist_real :
      ((nndist
        ((PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x) t).toReal)
        ((PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x) t).toReal) : ℝ))
        ≤ (Kc : ℝ) * d := by
    let Sp : ℝ := ((∑' τ, baScore prob p x τ).toReal)
    let Sq : ℝ := ((∑' τ, baScore prob q x τ).toReal)
    let a : ℝ := (baScore prob p x t).toReal
    let b : ℝ := (baScore prob q x t).toReal
    have hSp_ge : m ≤ Sp := by simpa [Sp] using hMassLower p x
    have hSq_ge : m ≤ Sq := by simpa [Sq] using hMassLower q x
    have hSp_pos : 0 < Sp := lt_of_lt_of_le hm hSp_ge
    have hSq_pos : 0 < Sq := lt_of_lt_of_le hm hSq_ge
    have hSpInv_le : Sp⁻¹ ≤ m⁻¹ := (inv_le_inv₀ hSp_pos hm).2 hSp_ge
    have hSpInv_nonneg : 0 ≤ Sp⁻¹ := by positivity
    have hb_nonneg : 0 ≤ b := by
      simpa [b] using (ENNReal.toReal_nonneg : 0 ≤ (baScore prob q x t).toReal)
    have hNum : |a - b| ≤ Kscore * d := by
      simpa [a, b, d] using hScoreLip p q x t
    have hInv : |Sp⁻¹ - Sq⁻¹| ≤ Kinv * d := by
      simpa [Sp, Sq, d] using hMassInvLip p q x
    have hb_le_ub : b ≤ ub := by
      simpa [b] using hScoreUpper q x t
    have htri :
        |a * Sp⁻¹ - b * Sq⁻¹|
          ≤ |a * Sp⁻¹ - b * Sp⁻¹| + |b * Sp⁻¹ - b * Sq⁻¹| := by
      exact abs_sub_le _ _ _
    have hfirst :
        |a * Sp⁻¹ - b * Sp⁻¹| = |a - b| * Sp⁻¹ := by
      have hsplit : a * Sp⁻¹ - b * Sp⁻¹ = (a - b) * Sp⁻¹ := by ring
      rw [hsplit, abs_mul, abs_of_nonneg hSpInv_nonneg]
    have hsecond :
        |b * Sp⁻¹ - b * Sq⁻¹| = b * |Sp⁻¹ - Sq⁻¹| := by
      have hsplit : b * Sp⁻¹ - b * Sq⁻¹ = b * (Sp⁻¹ - Sq⁻¹) := by ring
      rw [hsplit, abs_mul, abs_of_nonneg hb_nonneg]
    have hfirst_le :
        |a * Sp⁻¹ - b * Sp⁻¹| ≤ (Kscore * d) * m⁻¹ := by
      rw [hfirst]
      have hKd_nonneg : 0 ≤ Kscore * d := mul_nonneg hKscore_nonneg hd_nonneg
      have h1 : |a - b| * Sp⁻¹ ≤ (Kscore * d) * Sp⁻¹ :=
        mul_le_mul_of_nonneg_right hNum hSpInv_nonneg
      have h2 : (Kscore * d) * Sp⁻¹ ≤ (Kscore * d) * m⁻¹ :=
        mul_le_mul_of_nonneg_left hSpInv_le hKd_nonneg
      exact le_trans h1 h2
    have hsecond_le :
        |b * Sp⁻¹ - b * Sq⁻¹| ≤ ub * (Kinv * d) := by
      rw [hsecond]
      have hKd_nonneg : 0 ≤ Kinv * d := mul_nonneg hKinv_nonneg hd_nonneg
      have h1 : b * |Sp⁻¹ - Sq⁻¹| ≤ b * (Kinv * d) :=
        mul_le_mul_of_nonneg_left hInv hb_nonneg
      have h2 : b * (Kinv * d) ≤ ub * (Kinv * d) :=
        mul_le_mul_of_nonneg_right hb_le_ub hKd_nonneg
      exact le_trans h1 h2
    have htotal :
        |a * Sp⁻¹ - b * Sq⁻¹| ≤ (Kscore * d) * m⁻¹ + ub * (Kinv * d) := by
      exact le_trans htri (add_le_add hfirst_le hsecond_le)
    have hrhs :
        (Kscore * d) * m⁻¹ + ub * (Kinv * d)
          = (Kscore / m + ub * Kinv) * d := by
      calc
        (Kscore * d) * m⁻¹ + ub * (Kinv * d)
            = (Kscore * m⁻¹ + ub * Kinv) * d := by ring
        _ = (Kscore / m + ub * Kinv) * d := by
              rw [div_eq_mul_inv]
    have hnorm_p :
        ((PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x) t).toReal)
          = a * Sp⁻¹ := by
      simpa [a, Sp] using
        (pmf_normalize_apply_toReal
          (T := T)
          (f := baScore prob p x)
          (hf0 := baScore_slice_ne_zero prob p x)
          (hfTop := baScore_slice_ne_top prob p x)
          (t := t))
    have hnorm_q :
        ((PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x) t).toReal)
          = b * Sq⁻¹ := by
      simpa [b, Sq] using
        (pmf_normalize_apply_toReal
          (T := T)
          (f := baScore prob q x)
          (hf0 := baScore_slice_ne_zero prob q x)
          (hfTop := baScore_slice_ne_top prob q x)
          (t := t))
    have hdist_real :
        |((PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x) t).toReal)
          - ((PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x) t).toReal)|
          ≤ (Kc : ℝ) * d := by
      calc
        |((PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x) t).toReal)
          - ((PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x) t).toReal)|
            = |a * Sp⁻¹ - b * Sq⁻¹| := by
                rw [hnorm_p, hnorm_q]
        _ ≤ (Kscore * d) * m⁻¹ + ub * (Kinv * d) := htotal
        _ = (Kscore / m + ub * Kinv) * d := hrhs
        _ = (Kc : ℝ) * d := by rw [hKc]
    simpa [Real.nndist_eq] using hdist_real
  exact_mod_cast hdist_nndist_real

/--
Global BA contraction in `encoderMassNndist` obtained from the explicit
normalize-Lipschitz estimate with lower-mass control.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_of_massRecipLipschitz
    (prob : IBProblem (X := X) (Y := Y))
    {m Kscore Kinv ub : ℝ}
    (Kc : ℝ≥0)
    (hm : 0 < m)
    (hKscore_nonneg : 0 ≤ Kscore)
    (hKinv_nonneg : 0 ≤ Kinv)
    (hKc : (Kc : ℝ) = Kscore / m + ub * Kinv)
    (hMassLower :
      ∀ p : X → FinProb T, ∀ x : X,
        m ≤ ((∑' t, baScore prob p x t).toReal))
    (hScoreUpper :
      ∀ p : X → FinProb T, ∀ x : X, ∀ t : T,
        (baScore prob p x t).toReal ≤ ub)
    (hScoreLip :
      ∀ p q : X → FinProb T, ∀ x : X, ∀ t : T,
        |(baScore prob p x t).toReal - (baScore prob q x t).toReal|
          ≤ Kscore * ((finProbMassNndist (T := T) (p x) (q x) : ℝ)))
    (hMassInvLip :
      ∀ p q : X → FinProb T, ∀ x : X,
        |((∑' t, baScore prob p x t).toReal)⁻¹
            - ((∑' t, baScore prob q x t).toReal)⁻¹|
          ≤ Kinv * ((finProbMassNndist (T := T) (p x) (q x) : ℝ))) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderMassNndist (X := X) (T := T) p q := by
  exact ibBlahutArimotoStep_encoderMassNndist_le_of_pointwise
    (X := X) (Y := Y) (T := T) (prob := prob)
    (hPointwise :=
      baNormalize_pointwise_massNndist_le_of_massRecipLipschitz
        (X := X) (Y := Y) (T := T)
        (prob := prob) (Kc := Kc)
        (hm := hm)
        (hKscore_nonneg := hKscore_nonneg)
        (hKinv_nonneg := hKinv_nonneg)
        (hKc := hKc)
        (hMassLower := hMassLower)
        (hScoreUpper := hScoreUpper)
        (hScoreLip := hScoreLip)
        (hMassInvLip := hMassInvLip))

/--
Global BA contraction reduction with intrinsic nonzero-score discharge:
it now depends only on the normalize-form pointwise estimate.
-/
theorem ibBlahutArimotoStep_encoderMassNndist_le_of_normalize_intrinsicNonzero
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hNormalize :
      ∀ p q : X → FinProb T, ∀ x : X,
        finProbMassNndist (T := T)
          (PMF.normalize (baScore prob p x) (baScore_slice_ne_zero prob p x) (baScore_slice_ne_top prob p x))
          (PMF.normalize (baScore prob q x) (baScore_slice_ne_zero prob q x) (baScore_slice_ne_top prob q x))
          ≤ Kc * finProbMassNndist (T := T) (p x) (q x)) :
    ∀ p q : X → FinProb T,
      encoderMassNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderMassNndist (X := X) (T := T) p q := by
  exact ibBlahutArimotoStep_encoderMassNndist_le_of_normalize
    (X := X) (Y := Y) (T := T) prob
    (hNonzero := baScore_slice_ne_zero (X := X) (Y := Y) (T := T) prob)
    (hNormalize := hNormalize)

/--
Concrete encoder sup-metric (as `ℝ≥0`) induced by pointwise `nndist`.
-/
noncomputable def encoderNndist
    [PseudoMetricSpace (FinProb T)]
    (p q : X → FinProb T) : ℝ≥0 :=
  Finset.sup Finset.univ (fun x => nndist (p x) (q x))

/--
Pointwise `nndist` is bounded by the encoder sup-metric.
-/
lemma nndist_eval_le_encoderNndist
    [PseudoMetricSpace (FinProb T)]
    (p q : X → FinProb T) (x : X) :
    nndist (p x) (q x) ≤ encoderNndist (X := X) (T := T) p q := by
  unfold encoderNndist
  exact Finset.le_sup
    (s := Finset.univ)
    (f := fun x : X => nndist (p x) (q x))
    (Finset.mem_univ x)

/--
Concrete contraction lift in encoder sup-metric:
pointwise `nndist` contraction implies global encoder sup-metric contraction.
-/
theorem ibBlahutArimotoStep_encoderNndist_le_of_pointwise
    [PseudoMetricSpace (FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hPointwise :
      ∀ p q : X → FinProb T, ∀ x : X,
        nndist ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
          ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
          ≤ Kc * nndist (p x) (q x)) :
    ∀ p q : X → FinProb T,
      encoderNndist (X := X) (T := T)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p)
        (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q)
        ≤ Kc * encoderNndist (X := X) (T := T) p q := by
  intro p q
  unfold encoderNndist
  refine Finset.sup_le ?_
  intro x hx
  calc
    nndist ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p) x)
        ((ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob q) x)
        ≤ Kc * nndist (p x) (q x) := hPointwise p q x
    _ ≤ Kc * Finset.sup Finset.univ (fun x => nndist (p x) (q x)) := by
      have hsup :
          nndist (p x) (q x) ≤ Finset.sup Finset.univ (fun x => nndist (p x) (q x)) := by
        exact Finset.le_sup
          (s := Finset.univ)
          (f := fun x : X => nndist (p x) (q x))
          (Finset.mem_univ x)
      exact mul_le_mul_of_nonneg_left
        hsup Kc.2

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

/--
Frozen-target KL Lyapunov functional with explicit target `(qT, mY_givenT)`.
-/
noncomputable def baFrozenTargetGapWith
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (p : X → FinProb T) : ℝ :=
  ∑ x : X, (InfoGeometry.fin_kl_div (p x) ((ibBlahutArimotoStepFrozen prob qT mY_givenT) x)).toReal

theorem baFrozenTargetGap_eq_baFrozenTargetGapWith_induced
    (prob : IBProblem (X := X) (Y := Y))
    (pAnchor p : X → FinProb T) :
    baFrozenTargetGap prob pAnchor p
      = baFrozenTargetGapWith prob
          (inducedMarginalT prob pAnchor)
          (inducedMProjection prob pAnchor)
          p := by
  unfold baFrozenTargetGap baFrozenTargetGapWith
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp [ibBlahutArimotoStep_eq_frozen_induced]

/-! ### Fully Internal Frozen Free-Energy Descent (Jaynes Slice) -/

/--
Frozen free-energy functional in Jaynes form (fixed `qT`, fixed `mY_givenT`):
`∑ₓ p(x) [ KL(p(t|x)||qT) + β E_{t~p(t|x)} KL(p(y|x)||m(y|t)) ]`.
-/
noncomputable def ibFrozenFreeEnergy
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (p : X → FinProb T) : ℝ :=
  let pX := marginal_x prob
  ∑ x : X, (pX x).toReal *
    ((InfoGeometry.fin_kl_div (p x) qT).toReal
      + prob.beta * ∑ t : T, (p x t).toReal *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)

/--
Frozen log-partition offset:
`∑ₓ p(x) log Z_x`.
-/
noncomputable def frozenLogPartitionOffset
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y) : ℝ :=
  let pX := marginal_x prob
  ∑ x : X, (pX x).toReal * logPartitionFrozen prob qT mY_givenT x

section FrozenInternalDescent

variable [DecidableEq T]

/--
Jaynes-slice frozen Gibbs update (definitionally the Gibbs posterior
from `frozenSliceJaynes` at each `x`).
-/
noncomputable def ibBlahutArimotoStepFrozenGibbs
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    X → FinProb T := by
  classical
  intro x
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  let hZ : J.partition lam ≠ 0 :=
    frozenSliceJaynes_partition_one_ne_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  exact J.gibbsDist lam hZ

/--
The frozen BA step is exactly the Jaynes-slice Gibbs posterior step.
-/
theorem ibBlahutArimotoStepFrozen_eq_frozenGibbs
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT
      =
    ibBlahutArimotoStepFrozenGibbs (X := X) (Y := Y) (T := T) prob qT mY_givenT hq := by
  funext x
  ext t
  let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
  let lam : Unit → ℝ := fun _ => 1
  let hZ : J.partition lam ≠ 0 :=
    frozenSliceJaynes_partition_one_ne_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
  have hpart : J.partition lam = ((∑' t', baScoreFrozen prob qT mY_givenT x t').toReal) := by
    simpa [J, lam] using
      (frozenSlice_partition_eq_baScoreFrozen_tsum_toReal
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x)
  have hleft_toReal :
      ((ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal
        =
      (qT t).toReal *
        Real.exp
          (-prob.beta *
            (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)
        / J.partition lam := by
    calc
      ((ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal
          = ((baScoreFrozen prob qT mY_givenT x t).toReal) /
              ((∑' t', baScoreFrozen prob qT mY_givenT x t').toReal) := by
                simp [ibBlahutArimotoStepFrozen, PMF.normalize_apply, div_eq_mul_inv]
      _ =
        (qT t).toReal *
          Real.exp
            (-prob.beta *
              (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)
          / J.partition lam := by
            rw [← hpart]
            unfold baScoreFrozen
            rw [ENNReal.toReal_mul]
            rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
  have hright_toReal :
      ((ibBlahutArimotoStepFrozenGibbs (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x) t).toReal
        =
      (qT t).toReal *
        Real.exp
          (-prob.beta *
            (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)
        / J.partition lam := by
    simp [ibBlahutArimotoStepFrozenGibbs, J, lam, frozenSliceJaynes,
      InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsDist_pointwise,
      InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsProb,
      InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsWeight,
      InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.energy]
  have hleft_ne_top :
      ((ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one _ t) ENNReal.one_lt_top)
  have hright_ne_top :
      ((ibBlahutArimotoStepFrozenGibbs (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x) t) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one _ t) ENNReal.one_lt_top)
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).1
    (hleft_toReal.trans hright_toReal.symm)

/--
Weighted frozen KL gap to the Jaynes-slice Gibbs update.
-/
noncomputable def baFrozenTargetGapWithGibbs
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (p : X → FinProb T) : ℝ :=
  let pX := marginal_x prob
  ∑ x : X, (pX x).toReal *
    (InfoGeometry.fin_kl_div (p x)
      ((ibBlahutArimotoStepFrozenGibbs
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) x)).toReal

/--
Decomposition of frozen free energy into weighted Gibbs KL gap minus the
weighted log-partition offset, derived slice-wise from `local_free_energy_identity`.
-/
theorem ibFrozenFreeEnergy_eq_gap_minus_logPartition
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (p : X → FinProb T) :
    ibFrozenFreeEnergy prob qT mY_givenT p
      =
    baFrozenTargetGapWithGibbs
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p
      - frozenLogPartitionOffset prob qT mY_givenT := by
  classical
  let pX := marginal_x prob
  have hslice :
      ∀ x : X,
        (InfoGeometry.fin_kl_div (p x) qT).toReal +
            prob.beta * ∑ t : T, (p x t).toReal *
              (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
          =
        (InfoGeometry.fin_kl_div (p x)
          ((ibBlahutArimotoStepFrozenGibbs
            (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) x)).toReal
          - logPartitionFrozen prob qT mY_givenT x := by
    intro x
    let J := frozenSliceJaynes (X := X) (Y := Y) (T := T) prob qT mY_givenT x
    let lam : Unit → ℝ := fun _ => 1
    let hZ : J.partition lam ≠ 0 :=
      frozenSliceJaynes_partition_one_ne_zero
        (X := X) (Y := Y) (T := T) prob qT mY_givenT x hq
    have hloc :
        (InfoGeometry.fin_kl_div (p x) qT).toReal +
            prob.beta * ∑ t : T, (p x t).toReal *
              (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
          =
        (InfoGeometry.fin_kl_div (p x) (J.gibbsDist lam hZ)).toReal
          - J.logPartition lam := by
      simpa [J, lam, hZ] using
        (local_free_energy_identity
          (X := X) (Y := Y) (T := T)
          prob qT mY_givenT x (p x) hq)
    have hlog : J.logPartition lam = logPartitionFrozen prob qT mY_givenT x := by
      simpa [J, lam] using
        (frozenSlice_logPartition_eq_logPartitionFrozen
          (X := X) (Y := Y) (T := T) prob qT mY_givenT x)
    calc
      (InfoGeometry.fin_kl_div (p x) qT).toReal +
          prob.beta * ∑ t : T, (p x t).toReal *
            (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
        =
      (InfoGeometry.fin_kl_div (p x) (J.gibbsDist lam hZ)).toReal
        - J.logPartition lam := hloc
      _ =
      (InfoGeometry.fin_kl_div (p x)
        ((ibBlahutArimotoStepFrozenGibbs
          (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) x)).toReal
        - logPartitionFrozen prob qT mY_givenT x := by
          rw [hlog]
          rfl
  unfold ibFrozenFreeEnergy baFrozenTargetGapWithGibbs frozenLogPartitionOffset
  dsimp [pX]
  calc
    ∑ x : X, (pX x).toReal *
        ((InfoGeometry.fin_kl_div (p x) qT).toReal +
          prob.beta * ∑ t : T, (p x t).toReal *
            (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)
      =
    ∑ x : X, (pX x).toReal *
      ((InfoGeometry.fin_kl_div (p x)
        ((ibBlahutArimotoStepFrozenGibbs
          (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) x)).toReal
        - logPartitionFrozen prob qT mY_givenT x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact congrArg (fun z => (pX x).toReal * z) (hslice x)
    _ =
    ∑ x : X,
      ((pX x).toReal *
        (InfoGeometry.fin_kl_div (p x)
          ((ibBlahutArimotoStepFrozenGibbs
            (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) x)).toReal
        -
        (pX x).toReal * logPartitionFrozen prob qT mY_givenT x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ =
      (∑ x : X, (pX x).toReal *
        (InfoGeometry.fin_kl_div (p x)
          ((ibBlahutArimotoStepFrozenGibbs
            (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) x)).toReal)
      -
      (∑ x : X, (pX x).toReal * logPartitionFrozen prob qT mY_givenT x) := by
          rw [Finset.sum_sub_distrib]

/--
Derived decomposition hypothesis for the Gibbs-slice frozen step.
-/
lemma ibFrozenFreeEnergy_hStepDecomp
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    let C := -frozenLogPartitionOffset prob qT mY_givenT
    ibFrozenFreeEnergy prob qT mY_givenT
      (ibBlahutArimotoStepFrozenGibbs
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq)
      = C + baFrozenTargetGapWithGibbs
          (X := X) (Y := Y) (T := T) prob qT mY_givenT hq
          (ibBlahutArimotoStepFrozenGibbs
            (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) := by
  intro C
  unfold C
  have h :=
    ibFrozenFreeEnergy_eq_gap_minus_logPartition
      (X := X) (Y := Y) (T := T)
      prob qT mY_givenT hq
      (ibBlahutArimotoStepFrozenGibbs
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/--
Derived decomposition hypothesis for an arbitrary encoder policy `p`.
-/
lemma ibFrozenFreeEnergy_hPDecomp
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (p : X → FinProb T) :
    let C := -frozenLogPartitionOffset prob qT mY_givenT
    ibFrozenFreeEnergy prob qT mY_givenT p
      = C + baFrozenTargetGapWithGibbs
          (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p := by
  intro C
  unfold C
  have h :=
    ibFrozenFreeEnergy_eq_gap_minus_logPartition
      (X := X) (Y := Y) (T := T)
      prob qT mY_givenT hq p
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-- Nonnegativity of the weighted frozen Gibbs KL gap. -/
lemma baFrozenTargetGapWithGibbs_nonneg
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (p : X → FinProb T) :
    0 ≤ baFrozenTargetGapWithGibbs
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p := by
  unfold baFrozenTargetGapWithGibbs
  refine Finset.sum_nonneg ?_
  intro x hx
  exact mul_nonneg (ENNReal.toReal_nonneg) ENNReal.toReal_nonneg

/--
The weighted frozen Gibbs KL gap vanishes at the Gibbs-slice frozen step.
-/
theorem baFrozenTargetGapWithGibbs_step_eq_zero
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal) :
    baFrozenTargetGapWithGibbs
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq
      (ibBlahutArimotoStepFrozenGibbs
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) = 0 := by
  unfold baFrozenTargetGapWithGibbs
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hkl :
      InfoGeometry.fin_kl_div
        ((ibBlahutArimotoStepFrozenGibbs
          (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) x)
        ((ibBlahutArimotoStepFrozenGibbs
          (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) x) = 0 := by
    unfold InfoGeometry.fin_kl_div InfoGeometry.kl_div
    simpa using
      (InformationTheory.klDiv_self
        (μ := (((ibBlahutArimotoStepFrozenGibbs
          (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) x).toMeasure)))
  simp [hkl]

/--
Fully internal frozen descent:
`ibFrozenFreeEnergy` decreases along the Gibbs-slice frozen step.
-/
theorem ibFrozenFreeEnergy_frozen_descent_internal
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (p : X → FinProb T) :
    ibFrozenFreeEnergy prob qT mY_givenT
      (ibBlahutArimotoStepFrozenGibbs
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq)
    ≤
    ibFrozenFreeEnergy prob qT mY_givenT p := by
  let C := -frozenLogPartitionOffset prob qT mY_givenT
  have hStepDecomp :
      ibFrozenFreeEnergy prob qT mY_givenT
        (ibBlahutArimotoStepFrozenGibbs
          (X := X) (Y := Y) (T := T) prob qT mY_givenT hq)
        = C + baFrozenTargetGapWithGibbs
            (X := X) (Y := Y) (T := T) prob qT mY_givenT hq
            (ibBlahutArimotoStepFrozenGibbs
              (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) := by
    simpa [C] using
      (ibFrozenFreeEnergy_hStepDecomp
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq)
  have hPDecomp :
      ibFrozenFreeEnergy prob qT mY_givenT p
        = C + baFrozenTargetGapWithGibbs
            (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p := by
    simpa [C] using
      (ibFrozenFreeEnergy_hPDecomp
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p)
  rw [hStepDecomp, hPDecomp]
  have hzero :
      baFrozenTargetGapWithGibbs
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq
        (ibBlahutArimotoStepFrozenGibbs
          (X := X) (Y := Y) (T := T) prob qT mY_givenT hq) = 0 :=
    baFrozenTargetGapWithGibbs_step_eq_zero
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq
  rw [hzero, add_zero]
  have hnonneg :
      0 ≤ baFrozenTargetGapWithGibbs
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p :=
    baFrozenTargetGapWithGibbs_nonneg
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p
  simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hnonneg C

/--
Internal frozen descent rewritten on the canonical frozen BA step symbol.
-/
theorem ibFrozenFreeEnergy_frozen_descent
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (p : X → FinProb T) :
    ibFrozenFreeEnergy prob qT mY_givenT
      (ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT)
    ≤
    ibFrozenFreeEnergy prob qT mY_givenT p := by
  have hEq :
      ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT
        =
      ibBlahutArimotoStepFrozenGibbs (X := X) (Y := Y) (T := T) prob qT mY_givenT hq :=
    ibBlahutArimotoStepFrozen_eq_frozenGibbs
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq
  simpa [hEq] using
    (ibFrozenFreeEnergy_frozen_descent_internal
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p)

end FrozenInternalDescent

/--
Canonical frozen variational functional in Jaynes form.

This is the frozen-target objective whose decomposition is derived internally
from `local_free_energy_identity`.
-/
noncomputable def ibVariationalFunctionalFrozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (p : X → FinProb T) : ℝ :=
  ibFrozenFreeEnergy prob qT mY_givenT p

/--
Fully internal frozen descent theorem in canonical variational form.

No external decomposition hypotheses are required: the decomposition is derived
from the local free-energy identity via the frozen Jaynes layer.
-/
theorem ibVariationalFunctional_frozen_descent
    [DecidableEq T]
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (p : X → FinProb T) :
    ibVariationalFunctionalFrozen prob qT mY_givenT
      (ibBlahutArimotoStepFrozen (X := X) (Y := Y) (T := T) prob qT mY_givenT)
    ≤ ibVariationalFunctionalFrozen prob qT mY_givenT p := by
  simpa [ibVariationalFunctionalFrozen] using
    (ibFrozenFreeEnergy_frozen_descent
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq p)

/--
The 'loose' IB variational functional (thermodynamic upper bound):
$F_{loose}(p, m, q) = \sum_x p(x) [ KL(p(t|x) || q(t)) + \beta \sum_t p(t|x) KL(p(y|x) || m(y|t)) ]$.

This functional admits an exact slice-wise Jaynes/Gibbs decomposition.
-/
noncomputable def ibVariationalFunctionalLoose
    (prob : IBProblem (X := X) (Y := Y))
    (p : X → FinProb T)
    (mY_givenT : T → FinProb Y)
    (qT : FinProb T) : ℝ :=
  ibFrozenFreeEnergy prob qT mY_givenT p

/--
Theorem: Loose functional identity.
The loose variational functional is exactly the sum of local free energies.
-/
theorem ibVariationalFunctionalLoose_eq_sum_local
    (prob : IBProblem (X := X) (Y := Y))
    (p : X → FinProb T)
    (mY_givenT : T → FinProb Y)
    (qT : FinProb T) :
    ibVariationalFunctionalLoose prob p mY_givenT qT =
    let pX := marginal_x prob
    ∑ x : X, (pX x).toReal *
      ((InfoGeometry.fin_kl_div (p x) qT).toReal
        + prob.beta * ∑ t : T, (p x t).toReal *
            (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal) := rfl

/--
The 'strict' variational functional is bounded above by the 'loose' functional.
This is a direct consequence of the convexity of the KL divergence (Jensen's inequality).
-/
theorem ibVariationalFunctional_le_loose
    (prob : IBProblem (X := X) (Y := Y))
    (p : X → FinProb T)
    (mY_givenT : T → FinProb Y)
    (qT : FinProb T)
    (hMI :
      mutualInformation (jointXT (prob := prob) p)
        = ∑ x : X, ((marginal_x (prob := prob) x).toReal *
            (InfoGeometry.fin_kl_div (p x) qT).toReal))
    (hJensen :
      ∀ x : X,
        (InfoGeometry.fin_kl_div (condYGivenX prob x) ((p x).bind mY_givenT)).toReal
          ≤
        ∑ t : T, (p x t).toReal *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal) :
    ibVariationalFunctional prob p mY_givenT ≤
    ibVariationalFunctionalLoose prob p mY_givenT qT := by
  let pX := marginal_x (prob := prob)
  unfold ibVariationalFunctional ibVariationalFunctionalLoose ibFrozenFreeEnergy
  let A : ℝ :=
    ∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (p x) qT).toReal
  let B : ℝ :=
    ∑ x : X,
      (pX x).toReal *
        (InfoGeometry.fin_kl_div (condYGivenX prob x) ((p x).bind mY_givenT)).toReal
  let C : ℝ :=
    ∑ x : X,
      (pX x).toReal *
        (∑ t : T, (p x t).toReal *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)
  have hLeft :
      (have pX := marginal_x (prob := prob)
       have pXT := jointXT (prob := prob) p
       mutualInformation pXT +
         prob.beta *
           ∑ x : X,
             (pX x).toReal *
               (InfoGeometry.fin_kl_div (condYGivenX prob x) ((p x).bind mY_givenT)).toReal)
        =
      A + prob.beta * B := by
    simp [A, B, pX, hMI]
  rw [hLeft]
  have hWeighted :
      B ≤ C := by
    unfold B C
    refine Finset.sum_le_sum ?_
    intro x _hx
    exact mul_le_mul_of_nonneg_left (hJensen x) ((pX x).toReal_nonneg)
  have hβnn : 0 ≤ prob.beta := le_of_lt prob.beta_pos
  have hBetaWeighted :
      prob.beta * B ≤ prob.beta * C := by
    exact mul_le_mul_of_nonneg_left hWeighted hβnn
  have hMain :
      A + prob.beta * B ≤ A + prob.beta * C := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hBetaWeighted A
  have hRight :
      (have pX := marginal_x (prob := prob)
       ∑ x : X,
         (pX x).toReal *
           ((InfoGeometry.fin_kl_div (p x) qT).toReal
             + prob.beta * ∑ t : T, (p x t).toReal *
                 (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal))
        =
      (∑ x : X,
          (pX x).toReal *
            ((InfoGeometry.fin_kl_div (p x) qT).toReal
              + prob.beta * ∑ t : T, (p x t).toReal *
                  (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)) := by
    simp [pX]
  have hRhs :
      (∑ x : X,
          (pX x).toReal *
            ((InfoGeometry.fin_kl_div (p x) qT).toReal
              + prob.beta * ∑ t : T, (p x t).toReal *
                  (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal))
        = A + prob.beta * C := by
    calc
      (∑ x : X,
          (pX x).toReal *
            ((InfoGeometry.fin_kl_div (p x) qT).toReal
              + prob.beta * ∑ t : T, (p x t).toReal *
                  (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal))
          =
        ∑ x : X,
          ((pX x).toReal * (InfoGeometry.fin_kl_div (p x) qT).toReal
            +
            (pX x).toReal *
              (prob.beta * ∑ t : T, (p x t).toReal *
                (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ =
        (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (p x) qT).toReal)
          +
        (∑ x : X,
            (pX x).toReal *
              (prob.beta * ∑ t : T, (p x t).toReal *
                (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)) := by
              rw [Finset.sum_add_distrib]
      _ =
        (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (p x) qT).toReal)
          +
        (∑ x : X,
            prob.beta *
              ((pX x).toReal *
                (∑ t : T, (p x t).toReal *
                  (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal))) := by
              refine congrArg (fun z => (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (p x) qT).toReal) + z) ?_
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ =
        (∑ x : X, (pX x).toReal * (InfoGeometry.fin_kl_div (p x) qT).toReal)
          +
        prob.beta *
          (∑ x : X,
              (pX x).toReal *
                (∑ t : T, (p x t).toReal *
                  (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal)) := by
              rw [Finset.mul_sum]
      _ = A + prob.beta * C := by simp [A, C]
  rw [hRight]
  exact (by simpa [A, B, C] using hMain.trans_eq hRhs.symm)

/-- Nonnegativity of the explicit frozen-target KL Lyapunov functional. -/
lemma baFrozenTargetGapWith_nonneg
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (p : X → FinProb T) :
    0 ≤ baFrozenTargetGapWith prob qT mY_givenT p := by
  unfold baFrozenTargetGapWith
  refine Finset.sum_nonneg ?_
  intro x hx
  exact ENNReal.toReal_nonneg

/--
Frozen-target gap with explicit target vanishes at the frozen BA update.
-/
theorem baFrozenTargetGapWith_step_eq_zero
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y) :
    baFrozenTargetGapWith prob qT mY_givenT
      (ibBlahutArimotoStepFrozen prob qT mY_givenT) = 0 := by
  unfold baFrozenTargetGapWith
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hkl :
      InfoGeometry.fin_kl_div
        ((ibBlahutArimotoStepFrozen prob qT mY_givenT) x)
        ((ibBlahutArimotoStepFrozen prob qT mY_givenT) x) = 0 := by
    unfold InfoGeometry.fin_kl_div InfoGeometry.kl_div
    simpa using
      (InformationTheory.klDiv_self
        (μ := (((ibBlahutArimotoStepFrozen prob qT mY_givenT) x).toMeasure)))
  simpa [hkl]

/--
Constructive one-step frozen-target descent for the explicit KL Lyapunov gap.
-/
theorem ibBlahutArimotoStepFrozen_descent_frozenTargetGap
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (p : X → FinProb T) :
    baFrozenTargetGapWith prob qT mY_givenT
      (ibBlahutArimotoStepFrozen prob qT mY_givenT)
      ≤ baFrozenTargetGapWith prob qT mY_givenT p := by
  have hzero :
      baFrozenTargetGapWith prob qT mY_givenT
        (ibBlahutArimotoStepFrozen prob qT mY_givenT) = 0 :=
    baFrozenTargetGapWith_step_eq_zero (prob := prob) (qT := qT) (mY_givenT := mY_givenT)
  rw [hzero]
  exact baFrozenTargetGapWith_nonneg (prob := prob) (qT := qT) (mY_givenT := mY_givenT) (p := p)

/--
Bridge theorem: frozen variational descent follows from a decomposition of the
variational functional into a constant offset plus the fully internal frozen free energy.

This bridges the external gap decomposition to the internal canonical descent.
-/
theorem ibVariationalFunctional_frozen_descent_of_gap_decomposition
    [DecidableEq T]
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (p : X → FinProb T)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (C : ℝ)
    (hStepDecomp :
      ibVariationalFunctional prob
        (ibBlahutArimotoStepFrozen prob qT mY_givenT) mY_givenT
        = C + ibVariationalFunctionalFrozen prob qT mY_givenT
            (ibBlahutArimotoStepFrozen prob qT mY_givenT))
    (hPDecomp :
      ibVariationalFunctional prob p mY_givenT
        = C + ibVariationalFunctionalFrozen prob qT mY_givenT p) :
    ibVariationalFunctional prob
      (ibBlahutArimotoStepFrozen prob qT mY_givenT) mY_givenT
    ≤ ibVariationalFunctional prob p mY_givenT := by
  rw [hStepDecomp, hPDecomp]
  have h_descent := ibVariationalFunctional_frozen_descent prob qT mY_givenT hq p
  linarith

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
