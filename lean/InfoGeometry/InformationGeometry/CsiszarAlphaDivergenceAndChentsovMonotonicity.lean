/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Epistemology.ChentsovMetricInvariance
import InfoGeometry.InformationGeometry.ArakiDonaldVariational
import InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# General Chentsov Markov Fisher Monotonicity, Csiszár f-Divergences, and Amari α-Divergences

This module upgrades congruent-fiber metric invariance (`ChentsovMetricInvariance`) and
total-variation contraction (`VariationalRG`) to general non-degenerate Markov kernels
and convex divergence functionals:

1. **Interior Markov Pushforward & Bayesian Posterior Kernel (`posteriorKernel`)**:
   - Proves that column-non-degenerate Markov kernels preserve the simplex interior
     (`pushInterior`) and induce normalized conditional posterior kernels
     `posteriorKernel T P hcol b a = P(a) T(a, b) / (T_* P)(b)`, matching the
     Bayesian Petz recovery operator (`UnifiedInfoGeometryPetzFockBridge.petzRecoveryVec`).
2. **Exact Chentsov–Petz Fisher Deficit & General Markov Monotonicity**:
   - Proves the exact variance-deficit identity
     `chentsov_fisher_deficit_eq_posterior_variance`:
     `g_P(u, u) - g_{T_* P}(T_* u, T_* u) = ∑_b (T_* P)_b Var_{P(·|b)}(u / P - (T_* u) / (T_* P))`.
   - Deduces unconditional Markov contraction `chentsov_markov_fisher_contraction` and
     the exact sufficiency / Petz-recovery saturation characterizations
     `chentsov_markov_fisher_eq_iff` and `chentsov_markov_fisher_eq_iff_petzRecovery`.
3. **Csiszár `f`-Divergences & General Data Processing Inequality**:
   - Defines `csiszarFDivergence f p q` and proves `csiszarFDivergence_ge_apply_one`,
     `csiszarFDivergence_nonneg`, conjugate duality `csiszarFDivergence_conjugate`, and the
     general Markov Data Processing Inequality `csiszarFDivergence_markov_contraction` for
     every convex generator on `[0, ∞)`.
   - Specializes directly to KL relative entropy (`ArakiDonald.relativeEntropy`) and
     Pearson `χ²` divergence (`UnifiedInfoGeometryPetzFockBridge.chiSquaredInner`).
4. **Amari `α`-Divergences**:
   - Defines `amariAlphaDivergence α p q`, proves `α ↔ -α` duality
     (`amariAlphaDivergence_dual`), `α = 0` Hellinger representation and faithfulness
     (`amariAlphaDivergence_zero_eq_two_hellingerSq`, `amariAlphaDivergence_zero_eq_zero_iff`),
     exact Csiszár generator representation `csiszarFDivergence_amariAlphaGenerator_eq`,
     non-negativity `amariAlphaDivergence_nonneg`, and full-parameter Markov Data Processing
     Inequality `amariAlphaDivergence_markov_contraction`.
-/

noncomputable section

namespace InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity

open Finset
open scoped BigOperators
open InfoGeometry.Epistemology.VariationalRG
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.InformationGeometry.ArakiDonald
open InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge

/-! ### 1. Interior Pushforward and Bayesian Posterior Kernel -/

/-- A Markov kernel `T : α → β → ℝ` is column-non-degenerate when every output state `b`
is reachable with positive probability from at least one input state `a`. -/
def ColNondegenerate {α β : Type*} [Fintype α] [Fintype β] (T : MarkovKernel α β) : Prop :=
  ∀ b : β, ∃ a : α, 0 < T.T a b

/-- Pushforward of a simplex-interior distribution under a column-non-degenerate Markov
kernel remains strictly in the simplex interior. -/
def pushInterior {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T) :
    ProbInterior β where
  p := (pushforward T (toProbDist P)).p
  pos b := by
    dsimp [pushforward, toProbDist]
    rcases hcol b with ⟨a₀, ha₀⟩
    exact Finset.sum_pos'
      (fun a _ => mul_nonneg (P.pos a).le (T.nonneg a b))
      ⟨a₀, Finset.mem_univ a₀, mul_pos (P.pos a₀) ha₀⟩
  sum_one := (pushforward T (toProbDist P)).sum_one

@[simp]
lemma pushInterior_p {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T) (b : β) :
    (pushInterior T P hcol).p b = ∑ a, P.p a * T.T a b := rfl

/-- Bayesian posterior transition kernel `P(a | b) = P(a) T(a, b) / (T_* P)(b)` associated
with an interior prior `P` and column-non-degenerate forward Markov kernel `T`. -/
def posteriorKernel {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T)
    (b : β) (a : α) : ℝ :=
  (P.p a * T.T a b) / (pushInterior T P hcol).p b

theorem posteriorKernel_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T)
    (b : β) (a : α) :
    0 ≤ posteriorKernel T P hcol b a :=
  div_nonneg (mul_nonneg (P.pos a).le (T.nonneg a b)) ((pushInterior T P hcol).pos b).le

theorem posteriorKernel_sum_one {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T) (b : β) :
    ∑ a, posteriorKernel T P hcol b a = 1 := by
  unfold posteriorKernel
  rw [← Finset.sum_div, ← pushInterior_p T P hcol b,
    div_self (ne_of_gt ((pushInterior T P hcol).pos b))]

/-- Package `posteriorKernel` as a reverse `MarkovKernel β α` (Bayesian inversion). -/
def posteriorMarkovKernel {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T) :
    MarkovKernel β α where
  T := posteriorKernel T P hcol
  nonneg := posteriorKernel_nonneg T P hcol
  sum_one := posteriorKernel_sum_one T P hcol

/-- The Bayesian posterior expectation equals the classical Petz transpose recovery map
`UnifiedInfoGeometryPetzFockBridge.petzRecoveryVec` on the density ratio `y / (T_* P)`. -/
theorem posteriorKernel_expectation_eq_petzRecoveryVec {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T) (y : β → ℝ) (a : α) :
    ∑ b, posteriorKernel T P hcol b a * y b =
      petzRecoveryVec P.p (fun b a' => T.T a' b) (pushInterior T P hcol).p y a := by
  unfold posteriorKernel petzRecoveryVec
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b _
  ring

/-! ### 2. Chentsov–Petz Posterior-Variance Deficit & Markov Fisher Monotonicity -/

/-- Exact Bayesian posterior-variance deficit identity for Fisher information under an
arbitrary column-non-degenerate Markov transition `T`. -/
theorem chentsov_fisher_deficit_eq_posterior_variance {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T) (u : α → ℝ) :
    fisherMetric P u u -
        fisherMetric (pushInterior T P hcol) (pushforwardTangentVec T u)
          (pushforwardTangentVec T u) =
      ∑ b, (pushInterior T P hcol).p b *
        ∑ a, posteriorKernel T P hcol b a *
          (u a / P.p a - pushforwardTangentVec T u b / (pushInterior T P hcol).p b) ^ 2 := by
  let Q := pushInterior T P hcol
  let v := pushforwardTangentVec T u
  have hQpos : ∀ b, 0 < Q.p b := Q.pos
  have hPpos : ∀ a, 0 < P.p a := P.pos
  have h_b (b : β) :
      Q.p b * ∑ a, posteriorKernel T P hcol b a * (u a / P.p a - v b / Q.p b) ^ 2 =
        (∑ a, T.T a b * ((u a * u a) / P.p a)) - (v b * v b) / Q.p b := by
    have hQne : Q.p b ≠ 0 := ne_of_gt (hQpos b)
    have hprod :
        Q.p b * ∑ a, posteriorKernel T P hcol b a * (u a / P.p a - v b / Q.p b) ^ 2 =
          ∑ a, (T.T a b * ((u a * u a) / P.p a) -
            2 * (v b / Q.p b) * (u a * T.T a b) +
            (v b / Q.p b) ^ 2 * (P.p a * T.T a b)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      have hPne : P.p a ≠ 0 := ne_of_gt (hPpos a)
      unfold posteriorKernel
      have hQne' : (pushInterior T P hcol).p b ≠ 0 := ne_of_gt (hQpos b)
      field_simp [hQne', hPne]
      ring
    rw [hprod, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hv : ∑ a, u a * T.T a b = v b := rfl
    have hq : ∑ a, P.p a * T.T a b = Q.p b := rfl
    rw [hv, hq]
    field_simp [hQne]
    ring
  calc
    fisherMetric P u u - fisherMetric Q v v
        = (∑ a, (u a * u a) / P.p a) - ∑ b, (v b * v b) / Q.p b := rfl
    _ = (∑ a, ((u a * u a) / P.p a) * ∑ b, T.T a b) - ∑ b, (v b * v b) / Q.p b := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [T.sum_one a, mul_one]
    _ = (∑ a, ∑ b, T.T a b * ((u a * u a) / P.p a)) - ∑ b, (v b * v b) / Q.p b := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ = (∑ b, ∑ a, T.T a b * ((u a * u a) / P.p a)) - ∑ b, (v b * v b) / Q.p b := by
          rw [Finset.sum_comm]
    _ = ∑ b, ((∑ a, T.T a b * ((u a * u a) / P.p a)) - (v b * v b) / Q.p b) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ b, Q.p b * ∑ a, posteriorKernel T P hcol b a * (u a / P.p a - v b / Q.p b) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro b _
          exact (h_b b).symm

/-- **General Chentsov Markov Fisher Contraction**: every column-non-degenerate Markov
kernel contracts (or preserves) the Fisher information metric everywhere on the simplex
interior. -/
theorem chentsov_markov_fisher_contraction {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T) (u : α → ℝ) :
    fisherMetric (pushInterior T P hcol) (pushforwardTangentVec T u)
        (pushforwardTangentVec T u) ≤
      fisherMetric P u u := by
  have hdef := chentsov_fisher_deficit_eq_posterior_variance T P hcol u
  have hnonneg :
      0 ≤ ∑ b, (pushInterior T P hcol).p b *
        ∑ a, posteriorKernel T P hcol b a *
          (u a / P.p a - pushforwardTangentVec T u b / (pushInterior T P hcol).p b) ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro b _
    refine mul_nonneg ((pushInterior T P hcol).pos b).le ?_
    refine Finset.sum_nonneg ?_
    intro a _
    exact mul_nonneg (posteriorKernel_nonneg T P hcol b a) (sq_nonneg _)
  linarith

/-- **Exact Sufficiency Saturation Iff for Fisher Contraction**: equality holds iff the
score `u / P` is constant along every positive transition fiber of `T`. -/
theorem chentsov_markov_fisher_eq_iff {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T) (u : α → ℝ) :
    fisherMetric (pushInterior T P hcol) (pushforwardTangentVec T u)
          (pushforwardTangentVec T u) =
        fisherMetric P u u ↔
      ∀ a b, T.T a b ≠ 0 →
        u a / P.p a = pushforwardTangentVec T u b / (pushInterior T P hcol).p b := by
  let Q := pushInterior T P hcol
  let v := pushforwardTangentVec T u
  have hdef := chentsov_fisher_deficit_eq_posterior_variance T P hcol u
  have hb_nonneg :
      ∀ b ∈ (Finset.univ : Finset β),
        0 ≤ Q.p b * ∑ a, posteriorKernel T P hcol b a * (u a / P.p a - v b / Q.p b) ^ 2 := by
    intro b _
    refine mul_nonneg (Q.pos b).le ?_
    refine Finset.sum_nonneg ?_
    intro a _
    exact mul_nonneg (posteriorKernel_nonneg T P hcol b a) (sq_nonneg _)
  have ha_nonneg (b : β) :
      ∀ a ∈ (Finset.univ : Finset α),
        0 ≤ posteriorKernel T P hcol b a * (u a / P.p a - v b / Q.p b) ^ 2 :=
    fun a _ => mul_nonneg (posteriorKernel_nonneg T P hcol b a) (sq_nonneg _)
  constructor
  · intro heq a b hT
    have hsum0 :
        ∑ b', Q.p b' * ∑ a', posteriorKernel T P hcol b' a' *
            (u a' / P.p a' - v b' / Q.p b') ^ 2 = 0 := by
      linarith
    have hb0 := (Finset.sum_eq_zero_iff_of_nonneg hb_nonneg).mp hsum0 b (Finset.mem_univ b)
    have hinner0 :
        ∑ a', posteriorKernel T P hcol b a' * (u a' / P.p a' - v b / Q.p b) ^ 2 = 0 :=
      (mul_eq_zero.mp hb0).resolve_left (ne_of_gt (Q.pos b))
    have ha0 := (Finset.sum_eq_zero_iff_of_nonneg (ha_nonneg b)).mp hinner0 a (Finset.mem_univ a)
    have hpk_pos : posteriorKernel T P hcol b a ≠ 0 := by
      unfold posteriorKernel
      exact div_ne_zero (mul_ne_zero (ne_of_gt (P.pos a)) hT) (ne_of_gt (Q.pos b))
    have hsq0 : (u a / P.p a - v b / Q.p b) ^ 2 = 0 :=
      (mul_eq_zero.mp ha0).resolve_left hpk_pos
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
  · intro hsuff
    have hsum0 :
        ∑ b, Q.p b * ∑ a, posteriorKernel T P hcol b a * (u a / P.p a - v b / Q.p b) ^ 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b _
      refine mul_eq_zero_of_right (Q.p b) (Finset.sum_eq_zero ?_)
      intro a _
      by_cases hT : T.T a b = 0
      · simp [posteriorKernel, hT]
      · rw [hsuff a b hT, sub_self, sq, mul_zero, mul_zero]
    linarith

/-- **Petz Recovery Saturation Characterization**: Fisher information is preserved by a
Markov kernel `T` iff the Bayesian Petz transpose recovery map reconstructs the tangent
vector `u` identically from `T_* u`. -/
theorem chentsov_markov_fisher_eq_iff_petzRecovery {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (P : ProbInterior α) (hcol : ColNondegenerate T) (u : α → ℝ) :
    fisherMetric (pushInterior T P hcol) (pushforwardTangentVec T u)
          (pushforwardTangentVec T u) =
        fisherMetric P u u ↔
      petzRecoveryVec P.p (fun b a => T.T a b) (pushInterior T P hcol).p
          (pushforwardTangentVec T u) = u := by
  let Q := pushInterior T P hcol
  let v := pushforwardTangentVec T u
  constructor
  · intro heq
    have hsuff := (chentsov_markov_fisher_eq_iff T P hcol u).mp heq
    funext a
    unfold petzRecoveryVec
    calc
      P.p a * ∑ b, T.T a b * (v b / Q.p b)
          = ∑ b, T.T a b * (P.p a * (v b / Q.p b)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro b _
              ring
      _ = ∑ b, T.T a b * u a := by
            refine Finset.sum_congr rfl ?_
            intro b _
            by_cases hT : T.T a b = 0
            · simp [hT]
            · have hrat := (hsuff a b hT).symm
              rw [hrat]
              have hPne : P.p a ≠ 0 := ne_of_gt (P.pos a)
              rw [mul_div_cancel₀ (u a) hPne]
      _ = (∑ b, T.T a b) * u a := by
            rw [← Finset.sum_mul]
      _ = u a := by rw [T.sum_one a, one_mul]
  · intro hpetz
    have hadj := petzRecoveryVec_chiSquared_adjoint P.p (fun a => ne_of_gt (P.pos a))
      (fun b a => T.T a b) Q.p u v
    have hcoarse : markovCoarseGrain (fun b a => T.T a b) u = v := by
      funext b
      simp [markovCoarseGrain, v, pushforwardTangentVec, mul_comm]
    rw [hcoarse, hpetz] at hadj
    change chiSquaredInner Q.p v v = chiSquaredInner P.p u u
    exact hadj.symm

/-! ### 3. Csiszár f-Divergences and General Data Processing Inequality -/

/-- Csiszár `f`-divergence `D_f(p ∥ q) = ∑_a q(a) f(p(a) / q(a))`. -/
def csiszarFDivergence {α : Type*} [Fintype α] (f : ℝ → ℝ) (p q : α → ℝ) : ℝ :=
  ∑ a, q a * f (p a / q a)

/-- Jensen lower bound for Csiszár `f`-divergence on simplex-interior distributions:
`f(1) ≤ D_f(P ∥ Q)` for any convex generator `f` on `[0, ∞)`. -/
theorem csiszarFDivergence_ge_apply_one {α : Type*} [Fintype α]
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici (0 : ℝ)) f) (P Q : ProbInterior α) :
    f 1 ≤ csiszarFDivergence f P.p Q.p := by
  have hmem : ∀ a ∈ (Finset.univ : Finset α), P.p a / Q.p a ∈ Set.Ici (0 : ℝ) :=
    fun a _ => div_nonneg (P.pos a).le (Q.pos a).le
  have hj := hf.map_sum_le (t := (Finset.univ : Finset α))
    (w := Q.p) (p := fun a => P.p a / Q.p a)
    (fun a _ => (Q.pos a).le) Q.sum_one hmem
  have havg : ∑ a, Q.p a • (P.p a / Q.p a) = 1 := by
    calc
      ∑ a, Q.p a * (P.p a / Q.p a) = ∑ a, P.p a := by
        refine Finset.sum_congr rfl ?_
        intro a _
        exact mul_div_cancel₀ (P.p a) (ne_of_gt (Q.pos a))
      _ = 1 := P.sum_one
  rw [havg] at hj
  simpa [csiszarFDivergence, smul_eq_mul] using hj

/-- Gibbs-type non-negativity of `D_f(P ∥ Q)` whenever `f` is convex on `[0, ∞)` with `f(1) = 0`. -/
theorem csiszarFDivergence_nonneg {α : Type*} [Fintype α]
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici (0 : ℝ)) f) (hf1 : f 1 = 0)
    (P Q : ProbInterior α) :
    0 ≤ csiszarFDivergence f P.p Q.p := by
  rw [← hf1]
  exact csiszarFDivergence_ge_apply_one f hf P Q

/-- **General Csiszár `f`-Divergence Data Processing Inequality**:
for every convex generator `f` on `[0, ∞)` and every column-non-degenerate Markov kernel `T`,
`D_f(T_* P ∥ T_* Q) ≤ D_f(P ∥ Q)`. -/
theorem csiszarFDivergence_markov_contraction {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (hcol : ColNondegenerate T)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici (0 : ℝ)) f)
    (P Q : ProbInterior α) :
    csiszarFDivergence f (pushInterior T P hcol).p (pushInterior T Q hcol).p ≤
      csiszarFDivergence f P.p Q.p := by
  let P' := pushInterior T P hcol
  let Q' := pushInterior T Q hcol
  have h_pt (b : β) :
      Q'.p b * f (P'.p b / Q'.p b) ≤ ∑ a, (Q.p a * T.T a b) * f (P.p a / Q.p a) := by
    have hj := hf.map_sum_le (t := (Finset.univ : Finset α))
      (w := posteriorKernel T Q hcol b) (p := fun a => P.p a / Q.p a)
      (fun a _ => posteriorKernel_nonneg T Q hcol b a)
      (posteriorKernel_sum_one T Q hcol b)
      (fun a _ => div_nonneg (P.pos a).le (Q.pos a).le)
    have havg : ∑ a, posteriorKernel T Q hcol b a • (P.p a / Q.p a) = P'.p b / Q'.p b := by
      have hQ'ne : Q'.p b ≠ 0 := ne_of_gt (Q'.pos b)
      calc
        ∑ a, ((Q.p a * T.T a b) / Q'.p b) * (P.p a / Q.p a)
            = ∑ a, (P.p a * T.T a b) / Q'.p b := by
                refine Finset.sum_congr rfl ?_
                intro a _
                have hQne : Q.p a ≠ 0 := ne_of_gt (Q.pos a)
                field_simp [hQ'ne, hQne]
        _ = (∑ a, P.p a * T.T a b) / Q'.p b := by rw [← Finset.sum_div]
        _ = P'.p b / Q'.p b := rfl
    rw [havg] at hj
    have hmul := mul_le_mul_of_nonneg_left hj (Q'.pos b).le
    have hrhs :
        Q'.p b * ∑ a, posteriorKernel T Q hcol b a • f (P.p a / Q.p a) =
          ∑ a, (Q.p a * T.T a b) * f (P.p a / Q.p a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      have hQ'ne : Q'.p b ≠ 0 := ne_of_gt (Q'.pos b)
      unfold posteriorKernel
      simp only [smul_eq_mul]
      have hQ'ne' : (pushInterior T Q hcol).p b ≠ 0 := ne_of_gt (Q'.pos b)
      field_simp [hQ'ne']
      ring
    exact hmul.trans_eq hrhs
  calc
    csiszarFDivergence f P'.p Q'.p
        ≤ ∑ b, ∑ a, (Q.p a * T.T a b) * f (P.p a / Q.p a) :=
          Finset.sum_le_sum (fun b _ => h_pt b)
    _ = ∑ a, ∑ b, (Q.p a * f (P.p a / Q.p a)) * T.T a b := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ = ∑ a, (Q.p a * f (P.p a / Q.p a)) * ∑ b, T.T a b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← Finset.mul_sum]
    _ = ∑ a, Q.p a * f (P.p a / Q.p a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [T.sum_one a, mul_one]
    _ = csiszarFDivergence f P.p Q.p := rfl

/-- Csiszár conjugate generator `f*(t) = t * f(1 / t)`. -/
def csiszarConjugate (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * f (1 / t)

/-- Reverse-argument symmetry under Csiszár conjugation:
`D_{f*}(P ∥ Q) = D_f(Q ∥ P)`. -/
theorem csiszarFDivergence_conjugate {α : Type*} [Fintype α]
    (f : ℝ → ℝ) (P Q : ProbInterior α) :
    csiszarFDivergence (csiszarConjugate f) P.p Q.p = csiszarFDivergence f Q.p P.p := by
  unfold csiszarFDivergence csiszarConjugate
  refine Finset.sum_congr rfl ?_
  intro a _
  have hQne : Q.p a ≠ 0 := ne_of_gt (Q.pos a)
  rw [one_div_div, ← mul_assoc, mul_div_cancel₀ (P.p a) hQne]

/-- KL divergence equals the Csiszár divergence generated by `t ↦ t * log t`. -/
theorem csiszarFDivergence_kl_eq_relativeEntropy {α : Type*} [Fintype α]
    (P Q : ProbInterior α) :
    csiszarFDivergence (fun t => t * Real.log t) P.p Q.p =
      relativeEntropy P.p Q.p := by
  unfold csiszarFDivergence relativeEntropy
  refine Finset.sum_congr rfl ?_
  intro a _
  have hQne : Q.p a ≠ 0 := ne_of_gt (Q.pos a)
  rw [← mul_assoc, mul_div_cancel₀ (P.p a) hQne]

/-- **KL Data Processing Inequality** for general column-non-degenerate Markov kernels. -/
theorem relativeEntropy_markov_contraction {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (hcol : ColNondegenerate T) (P Q : ProbInterior α) :
    relativeEntropy (pushInterior T P hcol).p (pushInterior T Q hcol).p ≤
      relativeEntropy P.p Q.p := by
  rw [← csiszarFDivergence_kl_eq_relativeEntropy (pushInterior T P hcol) (pushInterior T Q hcol),
    ← csiszarFDivergence_kl_eq_relativeEntropy P Q]
  exact csiszarFDivergence_markov_contraction T hcol (fun t => t * Real.log t)
    Real.convexOn_mul_log P Q

/-- Pearson `χ²` Csiszár divergence equals `UnifiedInfoGeometryPetzFockBridge.chiSquaredInner`
of the difference vector `P - Q`. -/
theorem csiszarFDivergence_chiSq_eq_chiSquaredInner {α : Type*} [Fintype α]
    (P Q : ProbInterior α) :
    csiszarFDivergence (fun t => (t - 1) ^ 2) P.p Q.p =
      chiSquaredInner Q.p (fun a => P.p a - Q.p a) (fun a => P.p a - Q.p a) := by
  unfold csiszarFDivergence chiSquaredInner
  refine Finset.sum_congr rfl ?_
  intro a _
  have hQne : Q.p a ≠ 0 := ne_of_gt (Q.pos a)
  field_simp [hQne]

lemma convexOn_chiSq_generator :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => (t - 1) ^ 2) := by
  refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hid : (a * x + b * y - 1) ^ 2 = (a * (x - 1) + b * (y - 1)) ^ 2 := by
    have h1 : a * x + b * y - 1 = a * (x - 1) + b * (y - 1) := by
      calc
        a * x + b * y - 1 = a * x + b * y - (a + b) := by rw [hab]
        _ = a * (x - 1) + b * (y - 1) := by ring
    rw [h1]
  have hdiff :
      a * (x - 1) ^ 2 + b * (y - 1) ^ 2 - (a * (x - 1) + b * (y - 1)) ^ 2 =
        a * b * (x - y) ^ 2 := by
    calc
      a * (x - 1) ^ 2 + b * (y - 1) ^ 2 - (a * (x - 1) + b * (y - 1)) ^ 2
          = a * (1 - a) * (x - 1) ^ 2 + b * (1 - b) * (y - 1) ^ 2 -
              2 * (a * b) * (x - 1) * (y - 1) := by ring
      _ = a * b * (x - 1) ^ 2 + b * a * (y - 1) ^ 2 -
              2 * (a * b) * (x - 1) * (y - 1) := by
            have ha' : 1 - a = b := by linarith
            have hb' : 1 - b = a := by linarith
            rw [ha', hb']
      _ = a * b * (x - y) ^ 2 := by ring
  have hnonneg : 0 ≤ a * b * (x - y) ^ 2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  linarith [hid, hdiff, hnonneg]

/-- **Pearson `χ²` Data Processing Inequality** under general Markov kernels. -/
theorem chiSquaredInner_markov_contraction {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (hcol : ColNondegenerate T) (P Q : ProbInterior α) :
    chiSquaredInner (pushInterior T Q hcol).p
        (fun b => (pushInterior T P hcol).p b - (pushInterior T Q hcol).p b)
        (fun b => (pushInterior T P hcol).p b - (pushInterior T Q hcol).p b) ≤
      chiSquaredInner Q.p (fun a => P.p a - Q.p a) (fun a => P.p a - Q.p a) := by
  rw [← csiszarFDivergence_chiSq_eq_chiSquaredInner (pushInterior T P hcol)
      (pushInterior T Q hcol),
    ← csiszarFDivergence_chiSq_eq_chiSquaredInner P Q]
  exact csiszarFDivergence_markov_contraction T hcol (fun t => (t - 1) ^ 2)
    convexOn_chiSq_generator P Q

/-! ### 4. Amari α-Divergences and Full-Parameter Markov DPI -/

/-- Amari's `α`-divergence:
`D^{(α)}(p ∥ q) = (4 / (1 - α²)) (1 - ∑_a p_a^{(1+α)/2} q_a^{(1-α)/2})`. -/
def amariAlphaDivergence {α : Type*} [Fintype α] (αParam : ℝ) (p q : α → ℝ) : ℝ :=
  (4 / (1 - αParam ^ 2)) *
    (1 - ∑ a, (p a) ^ ((1 + αParam) / 2) * (q a) ^ ((1 - αParam) / 2))

/-- Canonical Csiszár convex generator for Amari's `α`-divergence. -/
def amariAlphaGenerator (αParam t : ℝ) : ℝ :=
  (4 / (1 - αParam ^ 2)) * ((1 + αParam) / 2 * t + (1 - αParam) / 2 - t ^ ((1 + αParam) / 2))

@[simp]
theorem amariAlphaGenerator_one (αParam : ℝ) : amariAlphaGenerator αParam 1 = 0 := by
  unfold amariAlphaGenerator
  simp only [mul_one, Real.one_rpow]
  have h0 : (1 + αParam) / 2 + (1 - αParam) / 2 - 1 = 0 := by ring
  rw [h0, mul_zero]

/-- **Amari `α ↔ -α` Reference-Target Duality**:
`D^{(-α)}(p ∥ q) = D^{(α)}(q ∥ p)`. -/
theorem amariAlphaDivergence_dual {α : Type*} [Fintype α]
    (αParam : ℝ) (p q : α → ℝ) :
    amariAlphaDivergence (-αParam) p q = amariAlphaDivergence αParam q p := by
  unfold amariAlphaDivergence
  have hsq : (-αParam) ^ 2 = αParam ^ 2 := by ring
  have hexp1 : (1 + -αParam) / 2 = (1 - αParam) / 2 := by ring
  have hexp2 : (1 - -αParam) / 2 = (1 + αParam) / 2 := by ring
  have hsum :
      ∑ a, (p a) ^ ((1 + -αParam) / 2) * (q a) ^ ((1 - -αParam) / 2) =
        ∑ a, (q a) ^ ((1 + αParam) / 2) * (p a) ^ ((1 - αParam) / 2) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [hexp1, hexp2, mul_comm]
  rw [hsq, hsum]

/-- At `α = 0`, Amari divergence reduces to `2 * Hellinger²`:
`D^{(0)}(P ∥ Q) = 2 ∑_a (√(P_a) - √(Q_a))²`. -/
theorem amariAlphaDivergence_zero_eq_two_hellingerSq {α : Type*} [Fintype α]
    (P Q : ProbInterior α) :
    amariAlphaDivergence 0 P.p Q.p =
      2 * ∑ a, (Real.sqrt (P.p a) - Real.sqrt (Q.p a)) ^ 2 := by
  unfold amariAlphaDivergence
  have hsum :
      ∑ a, (P.p a) ^ ((1 + (0 : ℝ)) / 2) * (Q.p a) ^ ((1 - (0 : ℝ)) / 2) =
        ∑ a, Real.sqrt (P.p a) * Real.sqrt (Q.p a) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    have hp : (P.p a) ^ ((1 + (0 : ℝ)) / 2) = Real.sqrt (P.p a) := by
      rw [add_zero, Real.sqrt_eq_rpow]
    have hq : (Q.p a) ^ ((1 - (0 : ℝ)) / 2) = Real.sqrt (Q.p a) := by
      rw [sub_zero, Real.sqrt_eq_rpow]
    rw [hp, hq]
  have hhell :
      ∑ a, (Real.sqrt (P.p a) - Real.sqrt (Q.p a)) ^ 2 =
        2 - 2 * ∑ a, Real.sqrt (P.p a) * Real.sqrt (Q.p a) := by
    calc
      ∑ a, (Real.sqrt (P.p a) - Real.sqrt (Q.p a)) ^ 2
          = ∑ a, (P.p a - 2 * (Real.sqrt (P.p a) * Real.sqrt (Q.p a)) + Q.p a) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hsp := Real.sq_sqrt (P.pos a).le
              have hsq := Real.sq_sqrt (Q.pos a).le
              linarith [show (Real.sqrt (P.p a) - Real.sqrt (Q.p a)) ^ 2 =
                Real.sqrt (P.p a) ^ 2 - 2 * (Real.sqrt (P.p a) * Real.sqrt (Q.p a)) +
                  Real.sqrt (Q.p a) ^ 2 by ring]
      _ = (∑ a, P.p a) - 2 * (∑ a, Real.sqrt (P.p a) * Real.sqrt (Q.p a)) + ∑ a, Q.p a := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 1 - 2 * (∑ a, Real.sqrt (P.p a) * Real.sqrt (Q.p a)) + 1 := by
            rw [P.sum_one, Q.sum_one]
      _ = 2 - 2 * ∑ a, Real.sqrt (P.p a) * Real.sqrt (Q.p a) := by ring
  rw [hsum, hhell]
  norm_num
  ring

/-- Faithfulness (definiteness) of Amari `α = 0` divergence on `ProbInterior`. -/
theorem amariAlphaDivergence_zero_eq_zero_iff {α : Type*} [Fintype α]
    (P Q : ProbInterior α) :
    amariAlphaDivergence 0 P.p Q.p = 0 ↔ P.p = Q.p := by
  rw [amariAlphaDivergence_zero_eq_two_hellingerSq]
  have hnonneg : ∀ a ∈ (Finset.univ : Finset α),
      0 ≤ (Real.sqrt (P.p a) - Real.sqrt (Q.p a)) ^ 2 :=
    fun a _ => sq_nonneg _
  constructor
  · intro hzero
    have hsum0 : ∑ a, (Real.sqrt (P.p a) - Real.sqrt (Q.p a)) ^ 2 = 0 := by linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0
    funext a
    have hsq : Real.sqrt (P.p a) = Real.sqrt (Q.p a) :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp (hterm a (Finset.mem_univ a)))
    exact (Real.sqrt_inj (P.pos a).le (Q.pos a).le).mp hsq
  · intro hpq
    rw [hpq]
    simp

/-- Exact equality between `amariAlphaDivergence α` and the Csiszár divergence generated
by `amariAlphaGenerator α` on simplex-interior distributions. -/
theorem csiszarFDivergence_amariAlphaGenerator_eq {α : Type*} [Fintype α]
    (αParam : ℝ) (P Q : ProbInterior α) :
    csiszarFDivergence (amariAlphaGenerator αParam) P.p Q.p =
      amariAlphaDivergence αParam P.p Q.p := by
  unfold csiszarFDivergence amariAlphaGenerator amariAlphaDivergence
  have h1 :
      ∑ a, Q.p a * ((1 + αParam) / 2 * (P.p a / Q.p a) + (1 - αParam) / 2) = 1 := by
    calc
      ∑ a, Q.p a * ((1 + αParam) / 2 * (P.p a / Q.p a) + (1 - αParam) / 2)
          = ∑ a, ((1 + αParam) / 2 * P.p a + (1 - αParam) / 2 * Q.p a) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hQne : Q.p a ≠ 0 := ne_of_gt (Q.pos a)
              field_simp [hQne]
      _ = (1 + αParam) / 2 * (∑ a, P.p a) + (1 - αParam) / 2 * (∑ a, Q.p a) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (1 + αParam) / 2 * 1 + (1 - αParam) / 2 * 1 := by
            rw [P.sum_one, Q.sum_one]
      _ = 1 := by ring
  have h2 :
      ∑ a, Q.p a * (P.p a / Q.p a) ^ ((1 + αParam) / 2) =
        ∑ a, (P.p a) ^ ((1 + αParam) / 2) * (Q.p a) ^ ((1 - αParam) / 2) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    have hPpos := P.pos a
    have hQpos := Q.pos a
    rw [Real.div_rpow hPpos.le hQpos.le]
    have hqpow : Q.p a / (Q.p a) ^ ((1 + αParam) / 2) = (Q.p a) ^ ((1 - αParam) / 2) := by
      have hexp : (1 : ℝ) - (1 + αParam) / 2 = (1 - αParam) / 2 := by ring
      calc
        Q.p a / (Q.p a) ^ ((1 + αParam) / 2)
            = (Q.p a) ^ (1 : ℝ) / (Q.p a) ^ ((1 + αParam) / 2) := by rw [Real.rpow_one]
        _ = (Q.p a) ^ ((1 : ℝ) - (1 + αParam) / 2) := (Real.rpow_sub hQpos 1 _).symm
        _ = (Q.p a) ^ ((1 - αParam) / 2) := by rw [hexp]
    calc
      Q.p a * ((P.p a) ^ ((1 + αParam) / 2) / (Q.p a) ^ ((1 + αParam) / 2))
          = (P.p a) ^ ((1 + αParam) / 2) * (Q.p a / (Q.p a) ^ ((1 + αParam) / 2)) := by ring
      _ = (P.p a) ^ ((1 + αParam) / 2) * (Q.p a) ^ ((1 - αParam) / 2) := by rw [hqpow]
  calc
    ∑ a, Q.p a * ((4 / (1 - αParam ^ 2)) *
        ((1 + αParam) / 2 * (P.p a / Q.p a) + (1 - αParam) / 2 -
          (P.p a / Q.p a) ^ ((1 + αParam) / 2)))
        = (4 / (1 - αParam ^ 2)) * ∑ a,
            (Q.p a * ((1 + αParam) / 2 * (P.p a / Q.p a) + (1 - αParam) / 2) -
              Q.p a * (P.p a / Q.p a) ^ ((1 + αParam) / 2)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
    _ = (4 / (1 - αParam ^ 2)) *
          ((∑ a, Q.p a * ((1 + αParam) / 2 * (P.p a / Q.p a) + (1 - αParam) / 2)) -
            ∑ a, Q.p a * (P.p a / Q.p a) ^ ((1 + αParam) / 2)) := by
          rw [Finset.sum_sub_distrib]
    _ = (4 / (1 - αParam ^ 2)) *
          (1 - ∑ a, (P.p a) ^ ((1 + αParam) / 2) * (Q.p a) ^ ((1 - αParam) / 2)) := by
          rw [h1, h2]

/-- Convexity of `amariAlphaGenerator α` on `[0, ∞)` for every `α ≥ -1`. -/
theorem amariAlphaGenerator_convexOn {αParam : ℝ} (hα : -1 ≤ αParam) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (amariAlphaGenerator αParam) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold amariAlphaGenerator
  let p : ℝ := (1 + αParam) / 2
  have hcomb :
      (1 + αParam) / 2 * (a * x + b * y) + (1 - αParam) / 2 =
        a * ((1 + αParam) / 2 * x + (1 - αParam) / 2) +
          b * ((1 + αParam) / 2 * y + (1 - αParam) / 2) := by
    calc
      (1 + αParam) / 2 * (a * x + b * y) + (1 - αParam) / 2
          = (1 + αParam) / 2 * (a * x + b * y) + (a + b) * ((1 - αParam) / 2) := by
              rw [hab, one_mul]
      _ = a * ((1 + αParam) / 2 * x + (1 - αParam) / 2) +
            b * ((1 + αParam) / 2 * y + (1 - αParam) / 2) := by ring
  rcases le_or_gt αParam 1 with hle1 | hgt1
  · have hp0 : 0 ≤ p := by dsimp [p]; linarith
    have hp1 : p ≤ 1 := by dsimp [p]; linarith
    have hrpow := (Real.concaveOn_rpow hp0 hp1).2 hx hy ha hb hab
    simp only [smul_eq_mul] at hrpow
    have hscale : 0 ≤ 4 / (1 - αParam ^ 2) := by
      have hden : 0 ≤ 1 - αParam ^ 2 := by nlinarith
      exact div_nonneg (by norm_num) hden
    have hcore :
        (1 + αParam) / 2 * (a * x + b * y) + (1 - αParam) / 2 - (a * x + b * y) ^ p ≤
          a * ((1 + αParam) / 2 * x + (1 - αParam) / 2 - x ^ p) +
            b * ((1 + αParam) / 2 * y + (1 - αParam) / 2 - y ^ p) := by
      linarith [hcomb, hrpow]
    have hmul := mul_le_mul_of_nonneg_left hcore hscale
    linarith [show 4 / (1 - αParam ^ 2) *
          (a * ((1 + αParam) / 2 * x + (1 - αParam) / 2 - x ^ p) +
            b * ((1 + αParam) / 2 * y + (1 - αParam) / 2 - y ^ p)) =
        a * (4 / (1 - αParam ^ 2) * ((1 + αParam) / 2 * x + (1 - αParam) / 2 - x ^ p)) +
          b * (4 / (1 - αParam ^ 2) * ((1 + αParam) / 2 * y + (1 - αParam) / 2 - y ^ p)) by ring]
  · have hp1 : 1 ≤ p := by dsimp [p]; linarith
    have hrpow := (convexOn_rpow hp1).2 hx hy ha hb hab
    simp only [smul_eq_mul] at hrpow
    have hscale_le : 4 / (1 - αParam ^ 2) ≤ 0 := by
      have hden : 1 - αParam ^ 2 < 0 := by nlinarith
      exact div_nonpos_of_nonneg_of_nonpos (by norm_num) hden.le
    have hcore :
        a * ((1 + αParam) / 2 * x + (1 - αParam) / 2 - x ^ p) +
            b * ((1 + αParam) / 2 * y + (1 - αParam) / 2 - y ^ p) ≤
          (1 + αParam) / 2 * (a * x + b * y) + (1 - αParam) / 2 - (a * x + b * y) ^ p := by
      linarith [hcomb, hrpow]
    have hmul := mul_le_mul_of_nonpos_left hcore hscale_le
    linarith [show 4 / (1 - αParam ^ 2) *
          (a * ((1 + αParam) / 2 * x + (1 - αParam) / 2 - x ^ p) +
            b * ((1 + αParam) / 2 * y + (1 - αParam) / 2 - y ^ p)) =
        a * (4 / (1 - αParam ^ 2) * ((1 + αParam) / 2 * x + (1 - αParam) / 2 - x ^ p)) +
          b * (4 / (1 - αParam ^ 2) * ((1 + αParam) / 2 * y + (1 - αParam) / 2 - y ^ p)) by ring]

/-- Non-negativity of Amari's `α`-divergence for EVERY real parameter `α : ℝ`. -/
theorem amariAlphaDivergence_nonneg {α : Type*} [Fintype α]
    (αParam : ℝ) (P Q : ProbInterior α) :
    0 ≤ amariAlphaDivergence αParam P.p Q.p := by
  by_cases hα : -1 ≤ αParam
  · rw [← csiszarFDivergence_amariAlphaGenerator_eq]
    exact csiszarFDivergence_nonneg (amariAlphaGenerator αParam)
      (amariAlphaGenerator_convexOn hα) (amariAlphaGenerator_one αParam) P Q
  · have hα' : -1 ≤ -αParam := by linarith
    have hdual : amariAlphaDivergence αParam P.p Q.p =
        amariAlphaDivergence (-αParam) Q.p P.p := by
      simpa using (amariAlphaDivergence_dual αParam Q.p P.p).symm
    rw [hdual, ← csiszarFDivergence_amariAlphaGenerator_eq]
    exact csiszarFDivergence_nonneg (amariAlphaGenerator (-αParam))
      (amariAlphaGenerator_convexOn hα') (amariAlphaGenerator_one (-αParam)) Q P

/-- **Full-Parameter Amari `α`-Divergence Data Processing Inequality**:
for EVERY `α : ℝ` and every column-non-degenerate Markov kernel `T`,
`D^{(α)}(T_* P ∥ T_* Q) ≤ D^{(α)}(P ∥ Q)`. -/
theorem amariAlphaDivergence_markov_contraction {α β : Type*} [Fintype α] [Fintype β]
    (αParam : ℝ) (T : MarkovKernel α β) (hcol : ColNondegenerate T)
    (P Q : ProbInterior α) :
    amariAlphaDivergence αParam (pushInterior T P hcol).p (pushInterior T Q hcol).p ≤
      amariAlphaDivergence αParam P.p Q.p := by
  by_cases hα : -1 ≤ αParam
  · rw [← csiszarFDivergence_amariAlphaGenerator_eq αParam (pushInterior T P hcol)
        (pushInterior T Q hcol),
      ← csiszarFDivergence_amariAlphaGenerator_eq αParam P Q]
    exact csiszarFDivergence_markov_contraction T hcol (amariAlphaGenerator αParam)
      (amariAlphaGenerator_convexOn hα) P Q
  · have hα' : -1 ≤ -αParam := by linarith
    have hdual1 : amariAlphaDivergence αParam (pushInterior T P hcol).p (pushInterior T Q hcol).p =
        amariAlphaDivergence (-αParam) (pushInterior T Q hcol).p (pushInterior T P hcol).p := by
      simpa using (amariAlphaDivergence_dual αParam
        (pushInterior T Q hcol).p (pushInterior T P hcol).p).symm
    have hdual2 : amariAlphaDivergence αParam P.p Q.p =
        amariAlphaDivergence (-αParam) Q.p P.p := by
      simpa using (amariAlphaDivergence_dual αParam Q.p P.p).symm
    rw [hdual1, hdual2,
      ← csiszarFDivergence_amariAlphaGenerator_eq (-αParam) (pushInterior T Q hcol)
        (pushInterior T P hcol),
      ← csiszarFDivergence_amariAlphaGenerator_eq (-αParam) Q P]
    exact csiszarFDivergence_markov_contraction T hcol (amariAlphaGenerator (-αParam))
      (amariAlphaGenerator_convexOn hα') Q P

end InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity

end section
