import DAG.LambdaReduction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Thermodynamic one-cochains on beta-reduction traces

A positive forward/reverse rate field assigns a logarithmic affinity to every
proof-relevant beta step. The generic repository-owned `ReductionTrace` provides
finite paths; affinity is additive along the stored trace and its exponential
is the positive multiplicative holonomy.

The final section proves the local Schnakenberg inequality. This is a local
second-law statement for positive edge activities; it does not assert global
monotonicity on the condensation order without a probability evolution.
-/

namespace InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

namespace LambdaTerm

/-- Strictly positive forward and reverse rates on every beta-reduction edge. -/
structure BetaRateField where
  forward : ∀ {t u : LambdaTerm}, BetaStep t u → ℝ
  reverse : ∀ {t u : LambdaTerm}, BetaStep t u → ℝ
  forward_pos : ∀ {t u : LambdaTerm} (h : BetaStep t u), 0 < forward h
  reverse_pos : ∀ {t u : LambdaTerm} (h : BetaStep t u), 0 < reverse h

namespace BetaRateField

/-- Logarithmic affinity of one beta-reduction edge. -/
noncomputable def affinity (R : BetaRateField)
    {t u : LambdaTerm} (h : BetaStep t u) : ℝ :=
  Real.log (R.forward h / R.reverse h)

/-- Edgewise detailed balance means equality of forward and reverse rates. -/
def EdgeDetailedBalance (R : BetaRateField)
    {t u : LambdaTerm} (h : BetaStep t u) : Prop :=
  R.forward h = R.reverse h

/-- An edge has zero affinity exactly when it satisfies detailed balance. -/
theorem affinity_eq_zero_iff_edgeDetailedBalance (R : BetaRateField)
    {t u : LambdaTerm} (h : BetaStep t u) :
    R.affinity h = 0 ↔ R.EdgeDetailedBalance h := by
  have hratio : 0 < R.forward h / R.reverse h :=
    div_pos (R.forward_pos h) (R.reverse_pos h)
  constructor
  · intro haff
    have hexp := congrArg Real.exp haff
    have hquot : R.forward h / R.reverse h = 1 := by
      simpa [affinity, Real.exp_log hratio] using hexp
    exact (div_eq_one_iff_eq (ne_of_gt (R.reverse_pos h))).mp hquot
  · intro hbalance
    have hquot : R.forward h / R.reverse h = 1 :=
      (div_eq_one_iff_eq (ne_of_gt (R.reverse_pos h))).mpr hbalance
    rw [affinity, hquot, Real.log_one]

/-- Integrated affinity along a proof-relevant reduction trace. -/
noncomputable def traceAffinity (R : BetaRateField) :
    {t u : LambdaTerm} → {xs : List LambdaTerm} →
      DAG.ReductionTrace BetaStep t xs u → ℝ
  | _, _, _, .refl _ => 0
  | _, _, _, .cons h rest => R.affinity h + R.traceAffinity rest

/-- Product of forward/reverse rate ratios along a reduction trace. -/
noncomputable def traceRateRatio (R : BetaRateField) :
    {t u : LambdaTerm} → {xs : List LambdaTerm} →
      DAG.ReductionTrace BetaStep t xs u → ℝ
  | _, _, _, .refl _ => 1
  | _, _, _, .cons h rest =>
      (R.forward h / R.reverse h) * R.traceRateRatio rest

/-- The rate-ratio product is the exponential of integrated affinity. -/
theorem traceRateRatio_eq_exp_traceAffinity (R : BetaRateField)
    {t u : LambdaTerm} {xs : List LambdaTerm}
    (trace : DAG.ReductionTrace BetaStep t xs u) :
    R.traceRateRatio trace = Real.exp (R.traceAffinity trace) := by
  induction trace with
  | refl =>
      simp [traceRateRatio, traceAffinity]
  | cons h rest ih =>
      have hratio : 0 < R.forward h / R.reverse h :=
        div_pos (R.forward_pos h) (R.reverse_pos h)
      simp [traceRateRatio, traceAffinity, Real.exp_add, ih, affinity,
        Real.exp_log hratio]

/-- Multiplicative holonomy of a finite beta-reduction trace. -/
noncomputable def traceHolonomy (R : BetaRateField)
    {t u : LambdaTerm} {xs : List LambdaTerm}
    (trace : DAG.ReductionTrace BetaStep t xs u) : ℝ :=
  Real.exp (R.traceAffinity trace)

/-- Holonomy agrees with the direct product of microscopic rate ratios. -/
theorem traceRateRatio_eq_traceHolonomy (R : BetaRateField)
    {t u : LambdaTerm} {xs : List LambdaTerm}
    (trace : DAG.ReductionTrace BetaStep t xs u) :
    R.traceRateRatio trace = R.traceHolonomy trace := by
  exact R.traceRateRatio_eq_exp_traceAffinity trace

theorem traceHolonomy_pos (R : BetaRateField)
    {t u : LambdaTerm} {xs : List LambdaTerm}
    (trace : DAG.ReductionTrace BetaStep t xs u) :
    0 < R.traceHolonomy trace :=
  Real.exp_pos _

/-- Detailed balance on a closed trace means zero integrated affinity. -/
def DetailedBalance (R : BetaRateField)
    {t : LambdaTerm} {xs : List LambdaTerm}
    (loop : DAG.ReductionTrace BetaStep t xs t) : Prop :=
  R.traceAffinity loop = 0

/-- A closed trace has detailed balance exactly when its holonomy is the unit. -/
theorem detailedBalance_iff_traceHolonomy_eq_one (R : BetaRateField)
    {t : LambdaTerm} {xs : List LambdaTerm}
    (loop : DAG.ReductionTrace BetaStep t xs t) :
    R.DetailedBalance loop ↔ R.traceHolonomy loop = 1 := by
  unfold DetailedBalance traceHolonomy
  constructor
  · intro h
    rw [h, Real.exp_zero]
  · intro h
    apply Real.exp_injective
    simpa using h

/-- Net flux between positive source and target activities. -/
def edgeFlux (forward reverse source target : ℝ) : ℝ :=
  source * forward - target * reverse

/-- Local Schnakenberg dissipation on one oriented edge. -/
noncomputable def edgeDissipation
    (forward reverse source target : ℝ) : ℝ :=
  edgeFlux forward reverse source target *
    Real.log ((source * forward) / (target * reverse))

/-- The logarithmic mean inequality for two positive activities. -/
theorem logRatioDissipation_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * Real.log (a / b) := by
  by_cases hab : a = b
  · subst b
    simp
  · rcases lt_or_gt_of_ne hab with hlt | hgt
    · have hquot : a / b < 1 := (div_lt_one hb).mpr hlt
      have hlog : Real.log (a / b) < 0 :=
        Real.log_lt_zero (div_pos ha hb) hquot
      have hsub : a - b < 0 := sub_neg.mpr hlt
      nlinarith
    · have hquot : 1 < a / b := (one_lt_div hb).mpr hgt
      have hlog : 0 < Real.log (a / b) := Real.log_pos hquot
      have hsub : 0 < a - b := sub_pos.mpr hgt
      nlinarith

/-- Positive rates and occupations give nonnegative local entropy production. -/
theorem edgeDissipation_nonneg
    {forward reverse source target : ℝ}
    (hforward : 0 < forward) (hreverse : 0 < reverse)
    (hsource : 0 < source) (htarget : 0 < target) :
    0 ≤ edgeDissipation forward reverse source target := by
  unfold edgeDissipation edgeFlux
  exact logRatioDissipation_nonneg
    (mul_pos hsource hforward) (mul_pos htarget hreverse)

end BetaRateField

end LambdaTerm

end InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
