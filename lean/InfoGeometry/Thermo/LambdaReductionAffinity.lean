import DAG.LambdaDeBruijnTopology
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Nlinarith

open scoped BigOperators

namespace InfoGeometry.Thermo.LambdaReduction

/-!
# Affinity and finite holonomy on the de Bruijn reduction graph

This module adds the finite thermodynamic edge layer to the existing
proof-relevant de Bruijn reduction graph.

The graph carrier and beta-step relation remain owned by
DAG.LambdaDeBruijnTopology and DAG.LambdaReduction.  This file only supplies:

* positive forward and reverse rates on a typed reduction relation;
* the logarithmic edge affinity;
* finite cycle affinity and multiplicative holonomy;
* detailed-balance and local dissipation theorems.

No normalization of rates, stochastic generator, stationary distribution, or
analytic/infinite-time convergence claim is introduced here.  Those are
separate interfaces in the existing probability and Markov owners.
-/

section EdgeRates

variable {Term : Type*} (BetaStep : Term → Term → Prop)

/-- Positive forward and reverse rates assigned to every typed reduction edge. -/
structure ReductionMarkovRates where
  k_pos : ∀ {t u : Term}, BetaStep t u → ℝ
  k_neg : ∀ {t u : Term}, BetaStep t u → ℝ
  k_pos_pos : ∀ {t u : Term} (h : BetaStep t u), 0 < k_pos h
  k_neg_pos : ∀ {t u : Term} (h : BetaStep t u), 0 < k_neg h

/-- The logarithmic thermodynamic affinity of one reduction edge. -/
noncomputable def stepAffinity (rates : ReductionMarkovRates BetaStep)
    {t u : Term} (h : BetaStep t u) : ℝ :=
  Real.log (rates.k_pos h / rates.k_neg h)

/-- Detailed balance on an edge means equality of its forward and reverse rates. -/
def HasDetailedBalance (rates : ReductionMarkovRates BetaStep)
    {t u : Term} (h : BetaStep t u) : Prop :=
  rates.k_pos h = rates.k_neg h

/-- An edge has zero affinity exactly when it satisfies detailed balance. -/
theorem affinity_eq_zero_iff_detailed_balance
    (rates : ReductionMarkovRates BetaStep)
    {t u : Term} (h : BetaStep t u) :
    stepAffinity BetaStep rates h = 0 ↔ HasDetailedBalance BetaStep rates h := by
  unfold stepAffinity HasDetailedBalance
  have h_ratio_pos : 0 < rates.k_pos h / rates.k_neg h :=
    div_pos (rates.k_pos_pos h) (rates.k_neg_pos h)
  constructor
  · intro h_zero
    have h_ratio :
        rates.k_pos h / rates.k_neg h = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero h_ratio_pos h_zero
    exact (div_eq_one_iff_eq (ne_of_gt (rates.k_neg_pos h))).mp h_ratio
  · intro h_balance
    simp [h_balance, ne_of_gt (rates.k_neg_pos h)]

end EdgeRates

section FiniteCycles

variable {Term : Type*} (BetaStep : Term → Term → Prop)

/-- A finite closed path in a reduction relation.

The reverse rate is part of the rate datum; a reverse beta-step constructor is
not required for the finite affinity identity. -/
structure ReductionCycle where
  length : ℕ
  nodes : Fin (length + 1) → Term
  steps : ∀ i : Fin length,
    BetaStep (nodes i.castSucc) (nodes i.succ)
  closed : nodes (Fin.last length) = nodes 0

/-- The sum of edge affinities along a finite reduction cycle. -/
noncomputable def cycleAffinity
    (rates : ReductionMarkovRates BetaStep)
    (C : ReductionCycle BetaStep) : ℝ :=
  ∑ i : Fin C.length, stepAffinity BetaStep rates (C.steps i)

/-- The product of forward/reverse rate ratios along a finite cycle. -/
noncomputable def cycleHolonomy
    (rates : ReductionMarkovRates BetaStep)
    (C : ReductionCycle BetaStep) : ℝ :=
  ∏ i : Fin C.length,
    rates.k_pos (C.steps i) / rates.k_neg (C.steps i)

/-- Cycle holonomy is the exponential of the cycle affinity. -/
theorem cycleHolonomy_eq_exp_affinity
    (rates : ReductionMarkovRates BetaStep)
    (C : ReductionCycle BetaStep) :
    cycleHolonomy BetaStep rates C =
      Real.exp (cycleAffinity BetaStep rates C) := by
  unfold cycleHolonomy cycleAffinity stepAffinity
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl ?_
  intro i hi
  exact Real.exp_log
    (div_pos (rates.k_pos_pos (C.steps i))
      (rates.k_neg_pos (C.steps i)))

/-- Detailed balance on every cycle edge forces trivial holonomy. -/
theorem detailed_balance_implies_trivial_holonomy
    (rates : ReductionMarkovRates BetaStep)
    (C : ReductionCycle BetaStep)
    (h_db : ∀ i : Fin C.length,
      HasDetailedBalance BetaStep rates (C.steps i)) :
    cycleHolonomy BetaStep rates C = 1 := by
  have h_aff_zero : cycleAffinity BetaStep rates C = 0 := by
    unfold cycleAffinity
    refine Finset.sum_eq_zero ?_
    intro i hi
    exact
      (affinity_eq_zero_iff_detailed_balance
        BetaStep rates (C.steps i)).2 (h_db i)
  calc
    cycleHolonomy BetaStep rates C =
        Real.exp (cycleAffinity BetaStep rates C) :=
      cycleHolonomy_eq_exp_affinity BetaStep rates C
    _ = Real.exp 0 := by rw [h_aff_zero]
    _ = 1 := Real.exp_zero

end FiniteCycles

section LocalDissipation

/-- Net flux along an oriented edge with source and target occupations. -/
def edgeFlux (k_pos k_neg p_src p_tgt : ℝ) : ℝ :=
  p_src * k_pos - p_tgt * k_neg

/-- Local Schnakenberg dissipation for a positive edge flux ratio. -/
noncomputable def edgeDissipation
    (k_pos k_neg p_src p_tgt : ℝ) : ℝ :=
  edgeFlux k_pos k_neg p_src p_tgt *
    Real.log ((p_src * k_pos) / (p_tgt * k_neg))

/-- The logarithmic mean inequality for two positive real numbers. -/
theorem log_mean_inequality_nonneg {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * Real.log (a / b) := by
  rcases lt_trichotomy a b with h_lt | h_eq | h_gt
  · have h_ratio_lt : a / b < 1 :=
      (div_lt_one hb).2 h_lt
    have h_log_neg : Real.log (a / b) < 0 :=
      Real.log_neg (div_pos ha hb) h_ratio_lt
    exact mul_nonneg (sub_nonpos.mpr h_lt.le) h_log_neg.le
  · subst b
    simp
  · have h_ratio_gt : 1 < a / b :=
      (one_lt_div hb).2 h_gt
    have h_log_pos : 0 < Real.log (a / b) :=
      Real.log_pos h_ratio_gt
    exact mul_nonneg (sub_nonneg.mpr h_gt.le) h_log_pos.le

/-- Positive occupations and positive rates give nonnegative local dissipation. -/
theorem edgeDissipation_nonneg
    {k_pos k_neg p_src p_tgt : ℝ}
    (hkp : 0 < k_pos) (hkn : 0 < k_neg)
    (hps : 0 < p_src) (hpt : 0 < p_tgt) :
    0 ≤ edgeDissipation k_pos k_neg p_src p_tgt := by
  have ha : 0 < p_src * k_pos := mul_pos hps hkp
  have hb : 0 < p_tgt * k_neg := mul_pos hpt hkn
  simpa [edgeDissipation, edgeFlux] using
    (log_mean_inequality_nonneg ha hb)

end LocalDissipation

section DeBruijnInstance

/-! The concrete relation adapter for the existing proof-relevant beta graph. -/

namespace DeBruijn

/-- The existing de Bruijn term carrier. -/
abbrev Term := DAG.LambdaDeBruijnTopology.Term

/-- The logical edge relation obtained from the existing proof-relevant step. -/
abbrev Step : Term → Term → Prop :=
  fun t u =>
    Nonempty (DAG.LambdaDeBruijnTopology.BetaStep t u)

/-- Positive rates on the existing de Bruijn beta graph. -/
abbrev Rates := ReductionMarkovRates Step

/-- Finite affinity cycles on the existing de Bruijn beta graph. -/
abbrev Cycle := ReductionCycle Step

/-- Every existing proof-relevant beta step is an edge of the adapted relation. -/
theorem betaStep_to_step
    {t u : Term}
    (h : DAG.LambdaDeBruijnTopology.BetaStep t u) :
    Step t u :=
  ⟨h⟩

end DeBruijn

end DeBruijnInstance

end InfoGeometry.Thermo.LambdaReduction
